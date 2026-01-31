import argparse
import hashlib
import json
import os
import queue
import re
import subprocess
import threading
import time
from collections import deque
from concurrent.futures import Future

from custom_logger import logger

from repo_utils import clean_code, find_function_definition, find_global_variable_definition, edit_distance
from utils import append_log

def query(prompt: str) -> str:
    # TODO:
    assert False, "Please implement the query function to interact with the LLM."

class RepoExtractor:

    def __init__(self, repo_path, prog_main_path=None, output_dir=None, log_path=None, bc_path=None, program_manual_path=None):
        self.repo_path = repo_path
        self.prog_main_path = prog_main_path # relative path
        self.output_dir = output_dir
        self.log_path = log_path
        self.bc_path = bc_path
        self.prog_name = os.path.basename(bc_path).replace('.bc', '')
        self.program_manual_path = program_manual_path
        self.debug_path = self.repo_path
        debug_dicts = {"TODO:": ""}
        if self.debug_path in debug_dicts:
            self.debug_path = debug_dicts[self.debug_path]
        assert os.path.exists(self.bc_path), f"BC path {self.bc_path} does not exist." if self.bc_path else None
        self.exclude_dirs = {'.git', 'venv', 'node_modules', 'test', 'tests', 'build', 'dist', '__pycache__'}
        self.code_ext = {'.c', '.h', '.cpp', '.hpp', '.cc', '.hh'}

        # definitions
        definition_path = os.path.join(self.output_dir, 'definitions.json')
        if os.path.exists(definition_path):
            with open(definition_path, 'r', encoding='utf-8') as f:
                self.definitions = json.load(f)
        else:
            self.definitions = {}

        self._global_lock = threading.Lock()
        self._enum_lock = threading.Lock()
        self._enum_inflight: dict[str, Future] = {}
        self._enum_cache: dict[str, dict] = {}
        self.analyzed_enums = {}

        self.files_in_repo = [] # relative paths of all code files
        self.check()
        self.extract_files()

    def check(self):
        logger.debug(f"Repo path: {self.repo_path}")
        assert os.path.exists(self.repo_path), f"Repo path {self.repo_path} does not exist."

    def extract_files(self):
        for root, dirs, files in os.walk(self.repo_path):
            dirs[:] = [d for d in dirs if d not in self.exclude_dirs]

            for file in files:
                if os.path.splitext(file)[1].lower() in self.code_ext:
                    file_path = os.path.join(root, file)
                    relative_path = os.path.relpath(file_path, self.repo_path)
                    self.files_in_repo.append(relative_path)
        logger.info(f"{len(self.files_in_repo)} files found in the repository {self.repo_path}")

    def resolve_include_path(self, include_file, current_file):
        candidate_paths = []
        for relative_path in self.files_in_repo:
            file_name = os.path.basename(relative_path)
            if file_name == include_file:
                candidate_paths.append(relative_path)
        if len(candidate_paths) == 1:
            assert os.path.exists(os.path.join(self.repo_path, candidate_paths[0])), f"Candidate path {candidate_paths[0]} does not exist."
            return os.path.join(self.repo_path, candidate_paths[0])
        elif len(candidate_paths) == 0:
            return None
        else:
            logger.error(f"Multiple candidates found for {include_file} in {self.repo_path}: {candidate_paths}. Please check the include path.")
            return os.path.join(self.repo_path, candidate_paths[0])

    def build_include_closure(self):
        visited_files = set()
        file_queue = deque()
        include_closure = set()

        file_queue.append(self.prog_main_path)
        visited_files.add(self.prog_main_path)

        while file_queue:
            current_relative_file = file_queue.popleft()
            # replace the occurrences of '../' with './' to handle relative paths correctly
            current_files = [
                os.path.join(self.repo_path, current_relative_file),
                os.path.join(self.repo_path, '..', current_relative_file),
                os.path.join(self.debug_path, current_relative_file),
                os.path.join(os.path.dirname(self.bc_path), current_relative_file),
                os.path.join(self.repo_path, re.sub(r'\.\./', './', current_relative_file, count=1)),
                os.path.join(self.repo_path, re.sub(r'\.\./', './', current_relative_file, count=2))
            ]
            for current_file in current_files:
                if not os.path.exists(current_file):
                    logger.warning(f"File {current_file} does not exist. Trying next candidate.")
                    continue
                try:
                    with open(current_file, 'r', encoding='utf-8', errors='ignore') as f:
                        include_closure.add(current_file)
                        logger.debug(f"Processing: {current_file}")
                        content = f.read()
                        content = re.sub(r'//.*?$|/\*.*?\*/', '', content, flags=re.MULTILINE|re.DOTALL)
                        includes = re.findall(r'#include\s+[<"][^>"]*[>"]', content)
                        for include in includes:
                            include_file = re.search(r'["<](.*?)[">]', include).group(1)
                            included_file = self.resolve_include_path(include_file, current_file)
                            if included_file and included_file not in visited_files:
                                visited_files.add(included_file)
                                file_queue.append(included_file)
                    break
                except Exception as e:
                    print(f"Error processing {current_file}: {e}")
        return include_closure

    def analyze_files(self, file_paths):
        definitions = {
            'macros': {},
            'functions': {},
            'structs': {},
            'classes': {},
            'typedefs': {},
            'enums': {}
        }

        for file_path in file_paths:
            try:
                with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                    content = f.read()
                    content = re.sub(r'//.*?$|/\*.*?\*/', '', content, flags=re.MULTILINE|re.DOTALL)
                    macro_pattern = r'#define\s+([a-zA-Z_][a-zA-Z0-9_]*)'
                    macro_names = re.findall(macro_pattern, content)
                    for macro_name in macro_names:
                        macro_value = re.search(r'(#define\s+' + re.escape(macro_name) + r'\s+.*)', content)
                        if macro_value:
                            macro_value = macro_value.group(1).strip()
                            macro_value_index = content.find(macro_value)
                            macro_value_with_context = content[macro_value_index:macro_value_index + len(macro_value) + 20].strip()
                            definitions['macros'][macro_name] = macro_value_with_context
                        else:
                            definitions['macros'][macro_name] = None
                    function_pattern = r'(?:(?:inline|static|const|volatile|extern)\s+)*[a-zA-Z_][a-zA-Z0-9_]*\s+(?:\*\s*)*([a-zA-Z_][a-zA-Z0-9_]*)\s*\([^)]*\)\s*(?:{[^}]*})'
                    function_names = re.findall(function_pattern, content)
                    for function_name in function_names:
                        if function_name not in definitions['functions']:
                            definitions['functions'][function_name] = set()
                        definitions['functions'][function_name].add(file_path)
                    struct_pattern = r'struct\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*\{'
                    struct_names = re.findall(struct_pattern, content)
                    for struct_name in struct_names:
                        if struct_name not in definitions['structs']:
                            definitions['structs'][struct_name] = set()
                        definitions['structs'][struct_name].add(file_path)
                    class_pattern = r'class\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*\{'
                    class_names = re.findall(class_pattern, content)
                    for class_name in class_names:
                        if class_name not in definitions['classes']:
                            definitions['classes'][class_name] = set()
                        definitions['classes'][class_name].add(file_path)
                    typedef_pattern = r'typedef\s+.*?\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*;'
                    typedef_names = re.findall(typedef_pattern, content)
                    for typedef_name in typedef_names:
                        typedef_value = re.search(r'typedef\s+(.*?\s+)' + re.escape(typedef_name) + r'\s*;', content)
                        if typedef_value:
                            typedef_value = typedef_value.group(1).strip()
                            definitions['typedefs'][typedef_name] = typedef_value
                        else:
                            definitions['typedefs'][typedef_name] = None
                    enum_pattern = r'''
                        \btypedef\s+enum
                        (?:\s+([A-Za-z_]\w*))?
                        \s*
                            (\{.*?\})
                        \s*
                        ([A-Za-z_]\w*)\s*;

                        |

                        \benum\s+
                        ([A-Za-z_]\w*)
                        \s*
                            (\{.*?\})
                    '''
                    regex = re.compile(enum_pattern, re.DOTALL | re.VERBOSE)
                    for m in regex.finditer(content):
                        # typedef enum {...} TypeName;
                        if m.group(3):  
                            name = m.group(3)
                            body = m.group(2)
                        # enum Name {...};
                        elif m.group(4):  
                            name = m.group(4)
                            body = m.group(5)
                        if name not in definitions['enums']:
                            definitions['enums'][name] = set()
                        definitions['enums'][name].add(body.strip())
            except Exception as e:
                print(f"Error analyzing {file_path}: {e}")
        # replace set with list
        for key in definitions:
            for name in definitions[key]:
                if isinstance(definitions[key][name], set):
                    definitions[key][name] = list(definitions[key][name])
        return definitions

    def analyze_enums(self, item):
        if not item:
            logger.warning("Empty item for analyze_enums.")
            return {}
        prompt_path = "prompts/prompt-repo-enums-definitions.txt"
        assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
        with open(prompt_path, 'r') as f:
            prompt = f.read()
            prompt = prompt.replace("###", json.dumps(item, sort_keys=True))
        start_time = time.time()
        append_log(self.log_path, f"Start analyzing enums in {self.repo_path} for program {self.prog_name}: {start_time}")
        logger.debug(f"Prompt for analyzing enums: {len(prompt)} characters.")
        response = query(prompt)
        logger.info(f"analyze_enums response: {response}")
        end_time = time.time()
        append_log(self.log_path, f"Finished analyzing enums in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")
        return json.loads(response)

    def _resolve_enum_definitions(self, related_enums: dict) -> dict:
        """
        Deduplicate concurrent enum queries so identical prompts are sent once.
        """
        if not related_enums:
            return {}

        def _canonicalize(enums_dict: dict) -> dict:
            # Keep payload stable regardless of list/dict order
            canonical = {}
            for name in sorted(enums_dict.keys()):
                bodies = enums_dict[name]
                canonical[name] = sorted(set(bodies))
            return canonical

        canonical_enums = _canonicalize(related_enums)
        key = hashlib.sha256(json.dumps(canonical_enums, sort_keys=True).encode("utf-8")).hexdigest()
        with self._enum_lock:
            cached = self._enum_cache.get(key)
            if cached is not None:
                return cached
            fut = self._enum_inflight.get(key)
            if fut is None:
                fut = Future()
                self._enum_inflight[key] = fut
                leader = True
            else:
                leader = False
        if not leader:
            return fut.result()
        try:
            result = self.analyze_enums(canonical_enums)
            fut.set_result(result)
            with self._enum_lock:
                self._enum_cache[key] = result
            return result
        except Exception as e:
            fut.set_exception(e)
            raise
        finally:
            with self._enum_lock:
                self._enum_inflight.pop(key, None)

    def _normalize_enum_definitions(self, enum_definitions_raw):
        """
        Normalize enum_definitions to {name: [ {..}, {..} ]} shape.
        """
        normalized = {}
        if isinstance(enum_definitions_raw, list):
            # [{'FALSE': 0, 'TRUE': 1}]
            # use _ as key
            if '_' not in normalized:
                normalized['_'] = []
            for item in enum_definitions_raw:
                if isinstance(item, dict):
                    normalized['_'].append(item)
                else:
                    logger.warning(f"Skip non-dict enum entry in list: {type(item)}, {item}")
        elif isinstance(enum_definitions_raw, dict):
            for name, val in enum_definitions_raw.items():
                if isinstance(val, dict):
                    normalized[name] = [val]
                elif isinstance(val, list):
                    normalized[name] = []
                    for item in val:
                        if isinstance(item, dict):
                            normalized[name].append(item)
                        else:
                            logger.warning(f"Skip non-dict enum entry for {name}: {type(item)}, {item}")
                else:
                    logger.warning(f"Skip enum_definitions entry {name} with unsupported type {type(val)}, {val}")
        else:
            raise ValueError(f"Unsupported enum_definitions type: {type(enum_definitions_raw)}, {enum_definitions_raw}")
        return normalized

    def analyze_enums_worker(self, worker_id, item):
        logger.debug(f"Worker {worker_id} got items: {item}")
        prompt_path = "prompts/prompt-repo-enums-definitions.txt"
        assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
        with open(prompt_path, 'r') as f:
            prompt = f.read()
            prompt = prompt.replace("###", json.dumps(item))
        start_time = time.time()
        append_log(self.log_path, f"Start analyzing enums subgroup in {self.repo_path} for program {self.prog_name}: {start_time}")
        logger.debug(f"Prompt for analyzing enums: {len(prompt)} characters.")
        response = query(prompt)
        logger.info(f"analyze_enums response: {response}")
        end_time = time.time()
        append_log(self.log_path, f"Finished analyzing enums in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")

    def analyze_enums_in_parallel(self, enums):
        MAX_LEN = 5000
        groups = []
        current_group = {}
        current_group_len = 0
        for enum_name in enums:
            enum_bodies = enums[enum_name]
            entry_str = json.dumps(enum_bodies)
            current_group[enum_name] = enum_bodies
            entry_len = len(enum_name) + len(entry_str)
            current_group_len += entry_len
            if current_group_len > MAX_LEN:
                groups.append(current_group)
                current_group = {}
                current_group_len = 0
        if current_group:
            groups.append(current_group)
        logger.info(f"Analyzing {len(enums)} enums in {len(groups)} groups.")
        # thread pool
        threads = []
        for i, group in enumerate(groups):
            t = threading.Thread(target=self.analyze_enums_worker, args=(i, group))
            t.start()
            threads.append(t)
        for t in threads:
            t.join()
        return self.analyzed_enums

    def extract(self):
        include_closure = self.build_include_closure()
        logger.debug("Files in the include closure:")
        for file_path in sorted(include_closure):
            logger.debug(f"  - {file_path}")
        definition_path = os.path.join(self.output_dir, 'definitions.json')
        existing_definitions = None
        if os.path.exists(definition_path):
            try:
                with open(definition_path, 'r', encoding='utf-8') as f:
                    existing_definitions = json.load(f)
            except Exception as e:
                logger.warning(f"Failed to load existing definitions for merge: {e}")
        definitions = self.analyze_files([os.path.join(self.repo_path, file) for file in self.files_in_repo])
        if existing_definitions and 'enum_definitions' in existing_definitions and 'enum_definitions' not in definitions:
            definitions['enum_definitions'] = self._normalize_enum_definitions(existing_definitions['enum_definitions'])
            logger.debug("Merged existing enum_definitions to avoid re-querying enums.")
        save_path = definition_path
        with open(save_path, 'w', encoding='utf-8') as f:
            json.dump(definitions, f, indent=4)
            logger.info(f"Definitions saved to {save_path}")
        return definitions

    def update_main_path(self, main_path):
        self.prog_main_path = main_path
        self.check()
        if len(self.files_in_repo) == 0:
            self.extract_files()
        definitions = self.extract()
        self.definitions = definitions

    def get_definition_debug_lines(self, function_name, _type='function'):
        assert _type in ['function', 'global'], f"Type {_type} is not supported. Please use 'function' or 'global'."
        if _type == 'function':
            cmd = "TODO:"
        else:
            cmd = "TODO:"
        logger.info(f"Running command: {cmd}")
        try:
            result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
            if result.returncode != 0:
                logger.error(f"Command failed with error: {result.stderr}")
                return {}
            output_content = result.stdout.strip()
            output_lines = output_content.split('\n')
            lines = {}
            for line in output_lines:
                assert "File: " in line, f"Line {line} does not contain 'File:'."
                assert "Line: " in line, f"Line {line} does not contain 'Line:'."
                file_path = line.split('File: ')[1].split(',')[0].strip()
                line_number = int(line.split('Line: ')[1].strip())
                if line_number == 0:
                    continue
                if file_path not in lines:
                    lines[file_path] = []
                lines[file_path].append(line_number)
            assert len(lines) == 1, f"Function {function_name} is defined in multiple files: {lines.keys()}. Please check the definitions."
            return lines
        except Exception as e:
            logger.error(f"Error running command: {e}")
            return {}

    def get_global_variable_definition(self, variable_name):
        definition_content = ""
        global_variable_definitions_path = os.path.join(self.output_dir, 'global_variable_definitions')
        if not os.path.exists(global_variable_definitions_path):
            os.makedirs(global_variable_definitions_path)
        existed_definitions = [os.path.splitext(f)[0] for f in os.listdir(global_variable_definitions_path)]
        if variable_name in existed_definitions:
            with open(os.path.join(global_variable_definitions_path, f"{variable_name}.txt"), 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
                return content
        lines = self.get_definition_debug_lines(variable_name, _type='global')
        if len(lines) == 0:
            return ""
        for file_path, line_numbers in lines.items():
            sorted_line_numbers = sorted(line_numbers)
            file_paths_abs = [
                os.path.join(self.repo_path, file_path),
                os.path.join(self.repo_path, '..', file_path),
                os.path.join(self.debug_path, file_path),
                os.path.join(os.path.dirname(self.bc_path), file_path),
                os.path.join(self.repo_path, re.sub(r'\.\./', './', file_path, count=1)),
                os.path.join(self.repo_path, re.sub(r'\.\./', './', file_path, count=2)),
            ]
            definition_content = ""
            for file_path_abs in file_paths_abs:
                if not os.path.exists(file_path_abs):
                    logger.warning(f"File {file_path_abs} does not exist. Trying next candidate.")
                    continue
                assert file_path_abs, f"File path {file_path} is not valid."
                definition_lines = []
                if not os.path.exists(file_path_abs):
                    logger.error(f"File {file_path_abs} does not exist. Please check the definitions.")
                    return ""
                with open(file_path_abs, 'r', encoding='utf-8', errors='ignore') as f:
                    source_lines = f.readlines()
                    for line_number in sorted_line_numbers:
                        if line_number <= len(source_lines):
                            assert line_number > 0, f"Line number {line_number} is not valid in {file_path}."
                            definition_lines.append(line_number)
                        else:
                            logger.warning(f"Line number {line_number} exceeds the number of lines in {file_path}.")
                            assert False
                    definition_content = find_global_variable_definition(source_lines, definition_lines, variable_name)
                    break
            # special handler
            if not definition_content:
                helper_path = "TODO:"
                if os.path.exists(helper_path):
                    with open(helper_path, 'r', encoding='utf-8', errors='ignore') as f:
                        definition_content = f.read()
            # save to file
            with open(os.path.join(global_variable_definitions_path, f"{variable_name}.txt"), 'w', encoding='utf-8') as f:
                f.write(definition_content)
                logger.info(f"Global variable {variable_name} definitions saved to {os.path.join(global_variable_definitions_path, f'{variable_name}.txt')}")
            return definition_content


    def get_function_definition(self, function_name):
        definition_content = ""
        function_definitions_path = os.path.join(self.output_dir, 'function_definitions')
        if not os.path.exists(function_definitions_path):
            os.makedirs(function_definitions_path)
        existed_definitions = [os.path.splitext(f)[0] for f in os.listdir(function_definitions_path)]
        if function_name in existed_definitions:
            with open(os.path.join(function_definitions_path, f"{function_name}.txt"), 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
                return content
        lines = self.get_definition_debug_lines(function_name)
        logger.debug(f"Lines for function {function_name}: {lines}")
        if len(lines) == 0:
            return ""
        for file_path, line_numbers in lines.items():
            sorted_line_numbers = sorted(line_numbers)
            file_paths_abs = [
                os.path.join(self.repo_path, file_path),
                os.path.join(self.repo_path, '..', file_path),
                os.path.join(self.debug_path, file_path),
                os.path.join(os.path.dirname(self.bc_path), file_path),
                os.path.join(self.repo_path, re.sub(r'\.\./', './', file_path, count=1)),
                os.path.join(self.repo_path, re.sub(r'\.\./', './', file_path, count=2))
            ]
            for file_path_abs in file_paths_abs:
                if not os.path.exists(file_path_abs):
                    logger.warning(f"File {file_path_abs} does not exist. Trying next candidate.")
                    continue
                assert file_path_abs, f"File path {file_path} is not valid."
                definition_lines = []
                assert os.path.exists(file_path_abs), f"File {file_path_abs} does not exist. Please check the definitions."
                logger.debug(f"Extracting function {function_name} from {file_path_abs} at lines {sorted_line_numbers}")
                with open(file_path_abs, 'r', encoding='utf-8', errors='ignore') as f:
                    source_lines = f.readlines()
                    for line_number in sorted_line_numbers:
                        if line_number <= len(source_lines):
                            assert line_number > 0, f"Line number {line_number} is not valid in {file_path}."
                            definition_lines.append(line_number)
                        else:
                            logger.warning(f"Line number {line_number} exceeds the number of lines in {file_path}.")
                            assert False
                    definition_content = find_function_definition(source_lines, definition_lines, function_name)
                    break
            # save to file
            with open(os.path.join(function_definitions_path, f"{function_name}.txt"), 'w', encoding='utf-8') as f:
                f.write(definition_content)
                logger.info(f"Function {function_name} definitions saved to {os.path.join(function_definitions_path, f'{function_name}.txt')}")
            return definition_content
        assert False, "Function definition not found. Please check the definitions."

    def get_function_start_line(self, function_name, function_lines):
        debug_lines = self.get_definition_debug_lines(function_name)
        if len(debug_lines) == 0:
            # maybe runtime error
            return None
        assert type(debug_lines) == dict
        assert len(debug_lines) == 1, f"only one file should contain the function {function_name} definition, but got {len(debug_lines)} files."
        file_paths = []
        max_lines = []
        for file_path, line_numbers in debug_lines.items():
            sorted_line_numbers = sorted(line_numbers)
            file_path_abs = os.path.join(self.debug_path, file_path)
            file_paths_abs = [
                os.path.join(self.repo_path, file_path),
                os.path.join(self.repo_path, '..', file_path),
                os.path.join(os.path.dirname(self.repo_path), file_path),
                os.path.join(self.debug_path, file_path),
                os.path.join(os.path.dirname(self.bc_path), file_path),
                os.path.join(self.repo_path, re.sub(r'\.\./', './', file_path, count=1)),
                os.path.join(self.repo_path, re.sub(r'\.\./', './', file_path, count=2))
            ]
            for file_path_abs in file_paths_abs:
                if not os.path.exists(file_path_abs):
                    logger.warning(f"File {file_path_abs} does not exist. Trying next candidate.")
                    continue
                assert file_path_abs, f"File path {file_path} is not valid."
                assert os.path.exists(file_path_abs), f"File {file_path_abs} does not exist. Please check the definitions."
                logger.debug(f"Extracting function {function_name} from {file_path_abs} at lines {sorted_line_numbers}")
                file_paths.append(os.path.relpath(file_path_abs, self.repo_path))
                max_lines.append(max(sorted_line_numbers))
        assert type(file_paths) == list, f"Function {function_name} has multiple definitions. Please check the definitions."
        for file_path in file_paths:
            assert os.path.exists(os.path.join(self.repo_path, file_path)), f"File {file_path} does not exist."
        for file_path, max_line in zip(file_paths, max_lines):
            with open(os.path.join(self.repo_path, file_path), 'r', encoding='utf-8', errors='ignore') as f:
                logger.debug(f"Reading file {file_path} to find start line for function {function_name}")
                lines = f.readlines()
                candidate_answers = []
                for i in range(len(lines)):
                    if edit_distance(lines[i].strip(), function_lines[0].strip()) < 5:
                        candidate_answers.append(i + 1)
                if len(candidate_answers) == 1:
                    logger.debug(f"Matched line {candidate_answers[0]} in {file_path}: {lines[candidate_answers[0] - 1].strip()}")
                    return candidate_answers[0]
                first_i = None
                j = 0
                for i in range(len(lines)):
                    if lines[i].strip() == "":
                        continue
                    if edit_distance(lines[i].strip(), function_lines[j].strip()) < 5:
                        logger.debug(f"Matched line {i + 1} in {file_path}: {lines[i].strip()}")
                        if not first_i:
                            first_i = i
                        j += 1
                        if j == 2:
                            return first_i + 1
                        continue
                    j = 0
                    first_i = None

        return None

    def get_enum_from_enum_definitions(self, enum_name):
        enum_definitions = self.definitions['enum_definitions'] if 'enum_definitions' in self.definitions else {}
        enum_definitions = self._normalize_enum_definitions(enum_definitions) if enum_definitions else {}
        possible_values = []
        for enum_def_name, enum_def_list in enum_definitions.items():
            for enum_def_dict in enum_def_list:
                if enum_name in enum_def_dict:
                    possible_values.append(enum_def_dict[enum_name])
        if len(possible_values) == 0:
            logger.warning(f"Enum {enum_name} not found in enum definitions.")
            return None
        if len(possible_values) > 1:
            logger.warning(f"Enum {enum_name} has multiple possible values in enum definitions: {possible_values}. Returning the first one.")
        return possible_values[0]

    def get_macro_definitions(self, macro_names):
        assert 'macros' in self.definitions, "No macro definitions found. Please run extract() first."
        macros = self.definitions['macros']
        enums = self.definitions['enums']
        enum_definitions = self.definitions['enum_definitions'] if 'enum_definitions' in self.definitions else {}
        macro_definitions = {}
        unfound_macro_names = []
        related_enums = {}
        for macro_name in macro_names:
            if macro_name not in macros:
                logger.warning(f"Macro {macro_name} not found in definitions.")
                enum_result = self.get_enum_from_enum_definitions(macro_name)
                if enum_result:
                    macro_value = enum_result
                    macro_definitions[macro_name] = macro_value
                else:
                    unfound_macro_names.append(macro_name)
                continue
            macro_value = macros[macro_name]
            if macro_value is None:
                logger.warning(f"Macro {macro_name} has no value.")
                continue
            macro_definitions[macro_name] = macro_value
        if unfound_macro_names:
            for macro_name in unfound_macro_names:
                for key, value_list in enums.items():
                    if macro_name in "\n".join(value_list):
                        related_enums[key] = value_list
            if related_enums:
                logger.debug(f"[enum-dedupe] resolving enums for macros={unfound_macro_names}, enums={list(related_enums.keys())}")
        if related_enums:
            partial_enum_definitions = self._resolve_enum_definitions(related_enums)
            partial_enum_definitions = self._normalize_enum_definitions(partial_enum_definitions) if partial_enum_definitions else {}
            with self._global_lock:
                enum_definitions = self.definitions.get('enum_definitions', {})
                enum_definitions = self._normalize_enum_definitions(enum_definitions) if enum_definitions else {}
                enum_definitions.update(partial_enum_definitions)
                self.definitions['enum_definitions'] = enum_definitions
                definition_path = os.path.join(self.output_dir, 'definitions.json')
                with open(definition_path, 'w', encoding='utf-8') as f:
                    json.dump(self.definitions, f, indent=4)
                for macro_name in unfound_macro_names:
                    enum_result = self.get_enum_from_enum_definitions(macro_name)
                    if enum_result:
                        macro_value = enum_result
                        macro_definitions[macro_name] = macro_value
                    else:
                        logger.error(f"Macro {macro_name} not found in enum definitions.")
        return macro_definitions

    def get_enum_definitions(self, enum_names=None):
        assert 'enums' in self.definitions, "No enum definitions found. Please run extract() first."
        enums = self.definitions['enums']
        if enum_names is None:
            return enums
        enum_definitions = {}
        for enum_name in enum_names:
            if enum_name not in enums:
                logger.warning(f"Enum {enum_name} not found in definitions.")
                continue
            enum_definition_files = enums[enum_name]
            enum_definitions[enum_name] = enum_definition_files
        return enum_definitions