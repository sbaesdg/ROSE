import os
import re
import json
from custom_logger import logger

def edit_distance(s1: str, s2: str) -> int:
    m = len(s1)
    n = len(s2)

    dp = [[0] * (n + 1) for _ in range(m + 1)]

    for i in range(m + 1):
        dp[i][0] = i

    for j in range(n + 1):
        dp[0][j] = j

    for i in range(1, m + 1):
        for j in range(1, n + 1):
            cost = 0 if s1[i-1] == s2[j-1] else 1

            dp[i][j] = min(dp[i-1][j] + 1,
                           dp[i][j-1] + 1,
                           dp[i-1][j-1] + cost)

    return dp[m][n]

def clean_code(code):
    code = re.sub(r'/\*.*?\*/', '', code, flags=re.DOTALL)
    code = re.sub(r'//.*$', '', code, flags=re.MULTILINE)
    return code

def clean_code_substitute(code):
    patterns = [r'/\*.*?\*/', r'//.*$']
    char_list = list(code)
    for pattern in patterns:
        if pattern.startswith('/\\*'):
            matches = re.finditer(pattern, code, flags=re.DOTALL)
        else:
            matches = re.finditer(pattern, code, flags=re.MULTILINE)
        for match in matches:
            start, end = match.span()
            newline_count = char_list[start:end].count('\n')
            char_list[start:end] = ['\n'] * newline_count + [''] * (end - start - newline_count)
    return ''.join(char_list)

def split_code_chunks(code, max_chars=3000):
    chunks = []
    current_chunk = []
    current_length = 0
    brace_level = 0
    buffer = []
    max_overflow = max_chars * 1.2
    for line in code.split('\n'):
        line = line.rstrip() + '\n'
        line_len = len(line)
        brace_level += line.count('{') - line.count('}')
        buffer.append(line)
        current_length += line_len
        if current_length >= max_chars:
            split_index = find_brace_safe_split(buffer, brace_level)
            if split_index > 0:
                safe_chunk = buffer[:split_index]
                chunks.append(''.join(safe_chunk))
                buffer = buffer[split_index:]
                current_length = sum(len(l) for l in buffer)
                brace_level = recalculate_brace_level(buffer)
            elif current_length >= max_overflow:
                chunks.append(''.join(buffer))
                buffer = []
                current_length = 0
                brace_level = 0
    if buffer:
        chunks.append(''.join(buffer))
    return chunks

def find_brace_safe_split(buffer, current_brace_level):
    window_brace_level = current_brace_level
    window_size = len(buffer)
    for i in range(min(len(buffer), window_size)):
        idx = len(buffer) - 1 - i
        line = buffer[idx]
        window_brace_level -= line.count('{') - line.count('}')
        if window_brace_level == 0:
            return idx + 1
    return 0

def recalculate_brace_level(buffer):
    return sum(line.count('{') - line.count('}') for line in buffer)

def find_function_end_idx(lines, start_idx: int):
    content = ''.join(lines)
    if start_idx < 0 or start_idx >= len(content) or content[start_idx] != '{':
        raise ValueError("start_idx must point to a '{' character.")

    line_starts = []
    offset = 0
    for ln in lines:
        line_starts.append(offset)
        offset += len(ln)

    line_no = max(i for i, st in enumerate(line_starts) if st <= start_idx)
    brace_count = 1
    cond_stack: list[dict] = []

    for i in range(line_no, len(lines)):
        line = lines[i]
        st = line_starts[i]
        en = st + len(line)

        stripped = line.lstrip()
        if stripped.startswith('#'):
            parts = stripped[1:].split(None, 1)
            tok = parts[0] if parts else ''
            if tok in ('if', 'ifdef', 'ifndef'):
                cond_stack.append({
                    'start': brace_count,
                    'changes': [0, 0],
                    'branch': 1
                })
            elif tok in ('else', 'elif'):
                if cond_stack:
                    frame = cond_stack[-1]
                    frame['changes'][0] = brace_count - frame['start']
                    brace_count = frame['start']
                    frame['branch'] = 2
            elif tok == 'endif':
                if cond_stack:
                    frame = cond_stack.pop()
                    idx = frame['branch'] - 1
                    frame['changes'][idx] = brace_count - frame['start']
                    net = min(frame['changes'])
                    brace_count = frame['start'] + net
            continue

        in_str = False
        str_char = ''
        escaped = False
        j0 = max(start_idx + 1, st) if i == line_no else st

        j = j0
        while j < en:
            c = content[j]
            if in_str:
                if escaped:
                    escaped = False
                elif c == '\\':
                    escaped = True
                elif c == str_char:
                    in_str = False
            else:
                if c in ('"', "'"):
                    in_str = True
                    str_char = c
                elif c == '/' and j + 1 < en and content[j+1] == '/':
                    break
                elif c == '{':
                    brace_count += 1
                elif c == '}':
                    brace_count -= 1
                    if brace_count == 0 and not cond_stack:
                        return j
            j += 1

    return None

def find_function_definition_lines(lines, start_idx: int, debug_lines):
    content = ''.join(lines)
    assert len(content) > 0, "content cannot be empty."
    if start_idx < 0 or start_idx >= len(content) or content[start_idx] != '{':
        raise ValueError("start_idx must point to a '{' character.")

    line_starts = []
    offset = 0
    for ln in lines:
        line_starts.append(offset)
        offset += len(ln)

    line_no = max(i for i, st in enumerate(line_starts) if st <= start_idx)
    brace_count = 1
    cond_stack: list[dict] = []
    function_definition = []

    for i in range(line_no, len(lines)):
        line = lines[i]
        st = line_starts[i]
        en = st + len(line)

        stripped = line.lstrip()
        if stripped.startswith('#'):
            parts = stripped[1:].split(None, 1)
            tok = parts[0] if parts else ''
            if tok in ('if', 'ifdef', 'ifndef'):
                cond_stack.append({
                    'start': brace_count,
                    'start_line': i + 1,
                    'changes': [0, 0],
                    'branch': 1,
                    'content': [[], []]
                })
            elif tok in ('else', 'elif'):
                if cond_stack:
                    frame = cond_stack[-1]
                    start_line = frame['start_line']
                    assert i > start_line, f"Unexpected '{tok}' at line {i + 1}, expected after line {start_line + 1}."
                    if_lines = list(range(start_line + 1, i + 1))
                    ignore = True
                    for j in if_lines:
                        if j in debug_lines:
                            ignore = False
                            break
                    if ignore:
                        content_idx = frame['branch'] - 1
                        assert content_idx == 0, f"Unexpected branch index {content_idx} for '{tok}' at line {i + 1}."
                        frame['content'][content_idx] = []
                        frame['changes'][content_idx] = 0
                        frame['start_line'] = i + 1
                        continue
                    frame['changes'][0] = brace_count - frame['start']
                    brace_count = frame['start']
                    frame['branch'] = 2
                    frame['start_line'] = i + 1
                else:
                    raise ValueError(f"Unexpected '{tok}' without matching '#if' at line {i + 1}.")
            elif tok == 'endif':
                if cond_stack:
                    frame = cond_stack.pop()
                    start_line = frame['start_line']
                    assert i > start_line, f"Unexpected '#endif' at line {i + 1}, expected after line {start_line + 1}."
                    if_lines = list(range(start_line + 1, i + 1))
                    ignore = True
                    for j in if_lines:
                        if j in debug_lines:
                            ignore = False
                            break
                    if ignore:
                        content_idx = frame['branch'] - 1
                        frame['content'][content_idx] = []
                        frame['changes'][content_idx] = 0
                    if cond_stack:
                        idx = cond_stack[-1]['branch'] - 1
                        cond_stack[-1]['content'][idx] += frame['content'][0] + frame['content'][1]
                    else:
                        function_definition += frame['content'][0] + frame['content'][1]
                    idx = frame['branch'] - 1
                    frame['changes'][idx] = brace_count - frame['start']
                    assert frame['changes'][0] == 0 or frame['changes'][1] == 0, f"Unexpected changes: {frame['changes']} for '#endif' at line {i + 1}."
                    net = max(frame['changes'])
                    brace_count = frame['start'] + net
                else:
                    raise ValueError(f"Unexpected '#endif' without matching '#if' at line {i + 1}.")
            continue

        in_str = False
        str_char = ''
        escaped = False
        j0 = max(start_idx + 1, st) if i == line_no else st

        j = j0
        while j < en:
            c = content[j]
            if in_str:
                if escaped:
                    escaped = False
                elif c == '\\':
                    escaped = True
                elif c == str_char:
                    in_str = False
            else:
                if c in ('"', "'"):
                    in_str = True
                    str_char = c
                elif c == '/' and j + 1 < en and content[j+1] == '/':
                    break
                elif c == '{':
                    brace_count += 1
                elif c == '}':
                    brace_count -= 1
                    if brace_count == 0 and not cond_stack:
                        return function_definition + [i+1]
            j += 1
        if cond_stack:
            content_idx = cond_stack[-1]['branch'] - 1
            cond_stack[-1]['content'][content_idx] += [i+1]
        else:
            function_definition += [i+1]
    return function_definition

def find_function_definition(definition_lines, debug_lines, function_name: str):
    content = ''.join(definition_lines)
    assert len(content) > 0, "content cannot be empty."
    start_line = max(debug_lines)
    logger.debug(f"Finding function definition for '{function_name}' starting from line {start_line}.")
    function_definition_pattern = rf'((?:(?:inline|static|const|volatile|extern)\s+)*[a-zA-Z_()][a-zA-Z0-9_()]*\s+(?:\*\s*)*[a-zA-Z0-9_]*{function_name}\s*\([^)]*\))\s*{{'
    cleaned_strategies = ["Full", "Substitute"]
    for strategy in cleaned_strategies:
        if strategy == "Full":
            cleaned_content = ''.join(definition_lines[:start_line])
        elif strategy == "Substitute":
            cleaned_content = clean_code_substitute(''.join(definition_lines[:start_line]))
        else:
            assert False, f"Unknown cleaning strategy: {strategy}"
        matched = re.findall(function_definition_pattern, cleaned_content)
        if len(matched) == 0:
            logger.error(f"Function {function_name} not found in the provided content with strategy '{strategy}'.")
            continue
        if len(matched) > 1:
            logger.warning(f"Function {function_name} has multiple definitions in the provided content. Using the last one.")
        break
    if len(matched) == 0:
        with open(os.path.join(os.path.dirname(__file__), 'debug.log'), 'w', encoding='utf-8') as f:
            f.write(f"Finding function definition for '{function_name}' in content of length {len(content)}.\n")
            f.write(cleaned_content)
        assert False, f"Function {function_name} not found in the provided content."
    function_definition_start = content.find(matched[-1])
    start_idx = content.find('{', function_definition_start)
    logger.debug(f"Function definition for '{function_name}' found at line {start_line}, start index {start_idx}.")
    if start_idx == -1:
        logger.error(f"Function {function_name} definition does not contain a '{{' character.")
        return None
    lines = find_function_definition_lines(definition_lines, start_idx, debug_lines)
    logger.debug(f"Function definition lines for '{function_name}': {lines}")
    assert len(lines) > 0 and '{' in definition_lines[lines[0] - 1], f"Bad function definition lines: {lines}"
    definition_lines[lines[0] - 1] = definition_lines[lines[0] - 1][definition_lines[lines[0] - 1].find('{'):]
    function_definition = content[function_definition_start:start_idx] + ''.join(definition_lines[i-1] for i in lines)
    return clean_code(function_definition)

def find_global_variable_definition(definition_lines, debug_lines, variable_name: str):
    content = ''.join(definition_lines)
    assert len(content) > 0, "content cannot be empty."
    start_line = max(debug_lines)
    logger.debug(f"Finding global variable definition for '{variable_name}' starting from line {start_line}.")
    global_var_pattern = rf'(\b(?:static\s+)?(?:const\s+)?(?:volatile\s+)?(?:extern\s+)?[a-zA-Z_][a-zA-Z0-9_]*\s+(?:\*\s*)*{variable_name}\s*)'
    pruned_content = ''.join(definition_lines[:start_line])
    matched = re.findall(global_var_pattern, pruned_content)
    if len(matched) == 0:
        logger.error(f"Global variable {variable_name} not found in the provided content.")
        return None
    if len(matched) > 1:
        logger.warning(f"Global variable {variable_name} has multiple definitions. Using the last one.")
    global_var_definition_start = content.find(matched[-1])
    if pruned_content.find('{', global_var_definition_start) == -1:
        logger.debug(f"Simple global variable definition found for {variable_name} at line {start_line}.")
        return ""
    start_idx = content.find('{', global_var_definition_start)
    if start_idx == -1:
        logger.error(f"Global variable {variable_name} definition does not contain a '{{' character.")
        return None
    lines = find_function_definition_lines(definition_lines, start_idx, debug_lines)
    assert len(lines) > 0 and '{' in definition_lines[lines[0] - 1], f"Bad global variable definition lines: {lines}"
    definition_lines[lines[0] - 1] = definition_lines[lines[0] - 1][definition_lines[lines[0] - 1].find('{'):]
    global_var_definition = content[global_var_definition_start:start_idx] + ''.join(definition_lines[i-1] for i in lines)
    return clean_code(global_var_definition)

def json_merge(json1_path, json2_path, output_path=None):
    assert os.path.exists(json1_path), f"File not found: {json1_path}"
    assert os.path.exists(json2_path), f"File not found: {json2_path}"
    assert output_path is not None, "output_path cannot be None"
    with open(json1_path, 'r', encoding='utf-8') as f:
        content = f.read()
        json1 = json.loads(content)
    with open(json2_path, 'r', encoding='utf-8') as f:
        content = f.read()
        json2 = json.loads(content)
    if isinstance(json1, dict) and isinstance(json2, dict):
        for key in json2:
            if key in json1:
                json1[key] = json2[key]
    else:
        raise ValueError("json1 and json2 must be dictionaries.")
    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(json1, f, ensure_ascii=False, indent=4)
    print(f"Merged JSON saved to {output_path}")