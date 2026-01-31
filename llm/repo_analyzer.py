import os
import re
import json
import requests
import time
import threading
import queue
import random
import subprocess
from collections import deque
from llm_utils import query, scrutinize_json
from repo_utils import clean_code, json_merge
from repo_extractor import RepoExtractor
from custom_logger import logger
from utils import append_log

class RepoAnalyzer:

    def __init__(self, repo_path, prog_name, output_dir=None, log_path=None, bc_path=None, program_manual_path=None):
        self.repo_path = repo_path
        self.prog_name = prog_name
        self.output_dir = output_dir
        assert os.path.exists(repo_path), f"Repository path {repo_path} does not exist."
        self.log_path = log_path
        self.bc_path = bc_path
        self.program_manual_path = program_manual_path
        self.exclude_dirs = {'.git', 'venv', 'node_modules', 'test', 'tests', 'build', 'dist', '__pycache__'}
        self.code_ext = {'.c', '.h', '.cpp', '.hpp', '.cc', '.hh'}
        self.results = []
        self._global_lock = threading.Lock()
        self.repo_extractor = RepoExtractor(repo_path=repo_path, prog_main_path=None, output_dir=output_dir, log_path=log_path, bc_path=bc_path, program_manual_path=program_manual_path)

    def find_option_parsing_files(self):
        files = self.repo_extractor.files_in_repo
        files_str = "\n".join(files)
        logger.debug(f"Prompt for finding option parsing files: {len(files)} files, {len(files_str)} characters.")
        prompt_path = "TODO:"
        assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
        with open(prompt_path, 'r') as f:
            prompt = f.read()
            prompt = prompt.replace("@@@", self.prog_name)
            prompt = prompt.replace("###", files_str)
        response = query(prompt)
        logger.info(f"Possible option parsing files: {response}")
        return json.loads(response)

    def find_state_variables(self, files):
        assert type(files) == dict, "files should be a dict"
        main_func_pattern = re.compile(r'\bint\s+main\s*\(.*?\)\s*{', re.DOTALL)
        for k, file in files.items():
            file_path = os.path.join(self.repo_path, file)
            assert os.path.exists(file_path), f"File {file_path} does not exist."
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    code = f.read()
                    cleaned_code = clean_code(code)
                if main_func_pattern.search(code):
                    logger.debug(f"Find main function in {file_path}, with code length {len(cleaned_code)}")
                    prompt_path = "TODO:"
                    assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
                    with open(prompt_path, 'r') as f:
                        prompt = f.read()
                        prompt = prompt.replace("###", cleaned_code)
                    response = query(prompt)
                    logger.info(f"Possible state variables: {response}")
                    response_json = json.loads(response)
                    return response_json
            except Exception as e:
                print(f"Failed to read file {file_path}: {str(e)}")
        return None

    def find_option_parsing_functions(self, files):
        assert type(files) == dict, "files should be a dict"
        main_func_pattern = re.compile(r'\bint\s+main\s*\(.*?\)\s*{', re.DOTALL)
        for k, file in files.items():
            file_path = os.path.join(self.repo_path, file)
            assert os.path.exists(file_path), f"File {file_path} does not exist."
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    code = f.read()
                    cleaned_code = clean_code(code)
                if main_func_pattern.search(code):
                    logger.debug(f"Find main function in {file_path}, with code length {len(cleaned_code)}")
                    prompt_path = "TODO:"
                    assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
                    with open(prompt_path, 'r') as f:
                        prompt = f.read()
                        prompt = prompt.replace("###", cleaned_code)
                    response = query(prompt)
                    logger.info(f"Possible option parsing functions: {response}")
                    self.repo_extractor.update_main_path(file)
                    return json.loads(response)
            except Exception as e:
                print(f"Failed to read file {file_path}: {str(e)}")
        return None

    def find_all_options(self, functions_info):
        if not functions_info:
            logger.error("No functions found for option parsing.")
            assert False
        assert type(functions_info) == dict, "functions should be a dict"
        logger.debug(f"Functions info: {functions_info}")
        parsing_type = functions_info["option parsing code type"]
        parsing_functions = functions_info["option parsing code functions"]
        function_definitions = []
        for parsing_function in parsing_functions:
            _function_definition = self.repo_extractor.get_function_definition(parsing_function)
            if _function_definition is not None:
                function_definitions += [_function_definition]
        function_definitions_path = os.path.join(self.output_dir, 'function_definitions')
        if os.path.exists(function_definitions_path):
            existed_definition_name_and_paths = [
                (os.path.splitext(f)[0], os.path.join(function_definitions_path, f)) for f in os.listdir(function_definitions_path)
            ]
            for name, definition_path in existed_definition_name_and_paths:
                if name in parsing_functions:
                    continue
                with open(definition_path, 'r', encoding='utf-8') as f:
                    _function_definition = f.read()
                    if _function_definition:
                        function_definitions += [_function_definition]
        all_option_result_path = os.path.join(self.output_dir, "TODO:")
        extra_infomation = []
        if not os.path.exists(all_option_result_path):
            start_time = time.time()
            append_log(self.log_path, f"Start finding options in {self.repo_path} for program {self.prog_name}: {start_time}")
            prompt_path = "TODO:"
            assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
            existed_information = set()
            with open(prompt_path, 'r') as f:
                prompt = f.read()
                prompt = prompt.replace("@@@", '\n'.join(function_definitions))
                prompt = prompt.replace("###", '\n'.join(extra_infomation))
            logger.debug(f"Prompt for finding options: {len(prompt)} characters.")
            append_log(os.path.join(self.output_dir, "TODO:"), prompt)
            response = query(prompt)
            logger.info(f"Possible options: {response}")
            response_json = json.loads(response)
            MAX_LOOP_CNT = 3
            CURRENT_LOOP_CNT = 0
            while response_json["result"] != "finished":
                CURRENT_LOOP_CNT += 1
                if CURRENT_LOOP_CNT > MAX_LOOP_CNT:
                    logger.error("Maximum loop count reached, exiting.")
                    assert False
                if response_json["result"] == "more information":
                    more_functions = response_json["functions"]
                    for func in more_functions:
                        if func in existed_information:
                            logger.debug(f"Function {func} already processed, skipping.")
                            continue
                        _function_definition = self.repo_extractor.get_function_definition(func)
                        if _function_definition is not None:
                            extra_infomation += [_function_definition]
                            existed_information.add(func)
                    more_global_vars = response_json["globalVariables"]
                    for var in more_global_vars:
                        if var in existed_information:
                            logger.debug(f"Global variable {var} already processed, skipping.")
                            continue
                        _global_vars = self.repo_extractor.get_global_variable_definition(var)
                        if _global_vars is not None:
                            extra_infomation += [_global_vars]
                            existed_information.add(var)
                    with open(prompt_path, 'r') as f:
                        prompt = f.read()
                        prompt = prompt.replace("@@@", '\n'.join(function_definitions))
                        prompt = prompt.replace("###", '\n'.join(extra_infomation))
                        prompt = prompt.replace("===", '\n'.join(existed_information))
                    logger.debug(f"Prompt for finding options: {len(prompt)} characters.")
                    append_log(os.path.join(self.output_dir, "TODO:"), prompt)
                    response = query(prompt)
                    logger.info(f"Possible options: {response}")
                    response_json = json.loads(response)
                else:
                    logger.error("Unimplemented so far.")
            options = response_json["options"]
            end_time = time.time()
            append_log(self.log_path, f"Finished finding options in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")
            self.save_json(options, all_option_result_path)
            assert os.path.exists(all_option_result_path), f"All options result file {all_option_result_path} does not exist."
        else:
            logger.debug(f"All options result file {all_option_result_path} already exists, loading from it.")
            options = self.load_json(all_option_result_path)
        
        optval_result_path = os.path.join(self.output_dir, "TODO:")
        if not os.path.exists(optval_result_path):
            prompt_path = "TODO:"
            assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
            with open(prompt_path, 'r') as f:
                prompt = f.read()
                prompt = prompt.replace("@@@", '\n'.join(function_definitions))
                prompt = prompt.replace("###", '\n'.join(extra_infomation))
            logger.debug(f"Prompt for finding optval: {len(prompt)} characters.")
            start_time = time.time()
            append_log(self.log_path, f"Start finding optval in {self.repo_path} for program {self.prog_name}: {start_time}")
            response = query(prompt)
            end_time = time.time()
            append_log(self.log_path, f"Finished finding optval in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")
            logger.info(f"Optval info: {response}")
            optval_info = json.loads(response)
            self.save_json(optval_info, optval_result_path)

    def prune_options(self, refresh=False):
        all_option_result_path = os.path.join(self.output_dir, "TODO:")
        assert os.path.exists(all_option_result_path), f"All options result file {all_option_result_path} does not exist."
        pruned_options_result_path = os.path.join(self.output_dir, "TODO:")
        if os.path.exists(pruned_options_result_path) and not refresh:
            logger.debug(f"Pruned options result file {pruned_options_result_path} already exists, skipping pruning.")
            return
        prompt_path = "TODO:"
        assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
        start_time = time.time()
        append_log(self.log_path, f"Start pruning options in {self.repo_path} for program {self.prog_name}: {start_time}")
        all_options = self.load_json(all_option_result_path)
        with open(prompt_path, 'r') as f:
            prompt = f.read()
            prompt = prompt.replace("@@@", str(all_options))
        logger.debug(f"Prompt for pruning options: {len(prompt)} characters.")
        response = query(prompt)
        logger.info(f"Pruned options: {response}")
        pruned_options = json.loads(response)
        self.save_json(pruned_options, pruned_options_result_path)
        end_time = time.time()
        append_log(self.log_path, f"Finished pruning options in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")
        assert os.path.exists(pruned_options_result_path), f"Pruned options result file {pruned_options_result_path} does not exist."

    def find_option_parsing_code(self, functions_info):
        if not functions_info:
            logger.error("No functions found for option parsing.")
            assert False
        assert type(functions_info) == dict, "functions should be a dict"
        logger.debug(f"Functions info: {functions_info}")
        parsing_type = functions_info["option parsing code type"]
        parsing_functions = functions_info["option parsing code functions"]
        function_definitions = []
        for parsing_function in parsing_functions:
            _function_definition = self.repo_extractor.get_function_definition(parsing_function)
            if _function_definition is not None:
                function_definitions += [_function_definition]
        function_definitions_path = os.path.join(self.output_dir, 'function_definitions')
        if os.path.exists(function_definitions_path):
            existed_definition_name_and_paths = [
                (os.path.splitext(f)[0], os.path.join(function_definitions_path, f)) for f in os.listdir(function_definitions_path)
            ]
            for name, definition_path in existed_definition_name_and_paths:
                if name in parsing_functions:
                    continue
                with open(definition_path, 'r', encoding='utf-8') as f:
                    _function_definition = f.read()
                    if _function_definition:
                        function_definitions += [_function_definition]
        all_option_result_path = os.path.join(self.output_dir, "TODO:")
        assert os.path.exists(all_option_result_path), f"All options result file {all_option_result_path} does not exist."
        options = self.load_json(all_option_result_path)
        parsing_code_tmp_result_path = os.path.join(self.output_dir, "TODO:")
        results = self.load_json(parsing_code_tmp_result_path) if os.path.exists(parsing_code_tmp_result_path) else {}
        prompt_path = "TODO:"
        assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
        extra_infomation = []
        for i in range(0, len(options), 5):
            selected_options = options[i:i + 5]
            selected_options = [opt for opt in selected_options if opt not in results]
            if len(selected_options) == 0:
                continue
            start_time = time.time()
            append_log(self.log_path, f"Start finding option parsing code for {selected_options} in {self.repo_path} for program {self.prog_name}: {start_time}")
            with open(prompt_path, 'r') as f:
                prompt = f.read()
                prompt = prompt.replace("@@@", ' '.join(selected_options))
                prompt = prompt.replace("###", '\n'.join(function_definitions))
                prompt = prompt.replace("+++", '\n'.join(extra_infomation))
            logger.debug(f"Prompt for finding option parsing code: {len(prompt)} characters.")
            response = query(prompt)
            logger.debug(f"Response for option parsing code: {response}")
            response = response.strip()
            response = re.sub(r'```.*?```', '', response, flags=re.DOTALL)
            response = re.sub(r'```', '', response)
            response_json = json.loads(response)
            results.update(response_json)
            logger.debug(f"Parsing code for options: {selected_options}")
            logger.debug(f"Parsing code: {response_json}")
            self.update_json(response_json, parsing_code_tmp_result_path)
            end_time = time.time()
            append_log(self.log_path, f"Finished finding option parsing code for {selected_options} in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")
        assert len(results) == len(options), "Results length does not match options length."
        return results

    def find_option_parsing_start(self, functions_info):
        if not functions_info:
            logger.error("No functions found for option parsing.")
            assert False
        assert type(functions_info) == dict, "functions should be a dict"
        logger.debug(f"Functions info: {functions_info}")
        parsing_type = functions_info["option parsing code type"]
        parsing_functions = functions_info["option parsing code functions"]
        function_definitions = []
        for parsing_function in parsing_functions:
            _function_definition = self.repo_extractor.get_function_definition(parsing_function)
            if _function_definition is not None:
                function_definitions += _function_definition
        prompt_path = "TODO:"
        assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
        extra_infomation = []
        results = {}
        with open(prompt_path, 'r') as f:
            prompt = f.read()
            prompt = prompt.replace("###", '\n'.join(function_definitions))
            prompt = prompt.replace("+++", '\n'.join(extra_infomation))
        logger.debug(f"Prompt for finding option parsing code start: {len(prompt)} characters.")
        response = query(prompt)
        logger.debug(f"Response for option parsing code start: {response}")
        response = response.strip()
        response = re.sub(r'```.*?```', '', response, flags=re.DOTALL)
        response = re.sub(r'```', '', response)
        response_json = json.loads(response)
        results.update(response_json)
        logger.debug(f"Parsing code start: {response_json}")
        return results

    def find_symbolization_line(self):
        input_path = os.path.join(self.output_dir, "TODO:")
        assert os.path.exists(input_path), f"Input file {input_path} does not exist."
        result_path = os.path.join(self.output_dir, "TODO:")
        if not os.path.exists(result_path):
            start_time = time.time()
            append_log(self.log_path, f"Start finding symbolization line in {self.repo_path} for program {self.prog_name}: {start_time}")
            with open(input_path, 'r', encoding='utf-8') as f:
                content = f.read()
                data = json.loads(content)
            assert "function" in data, "function not found in input file"
            assert "line" in data, "line not found in input file"
            func = data["function"]
            lines = data["line"]
            line_no = self.repo_extractor.get_function_start_line(func, lines)
            if line_no is None:
                logger.error(f"Lines \"{lines}\" not found in function {func}.")
                assert False
            data["line_no"] = line_no
            self.save_json(data, result_path)
            logger.debug(f"line number: {line_no}")
            end_time = time.time()
            append_log(self.log_path, f"Finished finding symbolization line in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")

    def query_callee_functions(self, code):
        prompt_path = "TODO:"
        assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
        with open(prompt_path, 'r') as f:
            prompt = f.read()
            prompt = prompt.replace("###", code)
        response = query(prompt)
        try:
            response_json = json.loads(response)
        except Exception as e:
            logger.error(f"Bad format: {response}")
            assert False
        logger.debug(f"Query callee functions: {response_json}")
        return response_json

    def query_macros(self, code):
        prompt_path = "TODO:"
        assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
        candidate_macros = []
        for macro in self.repo_extractor.definitions["macros"].keys():
            if macro in code:
                candidate_macros.append(macro)
        with open(prompt_path, 'r') as f:
            prompt = f.read()
            prompt = prompt.replace("###", code)
            prompt = prompt.replace("@@@", ','.join(candidate_macros))
        logger.debug(f"Prompt for finding macros: {len(prompt)} characters.")
        response = query(prompt)
        try:
            response_json = json.loads(scrutinize_json(response))
        except Exception as e:
            logger.error(f"Bad format: {response}")
            raise e
        logger.debug(f"Query macros: {response_json}")
        return response_json

    def query_substitutions(self, code, macro_definitions):
        assert type(macro_definitions) == dict, "macro_definitions should be a dict"
        prompt_path = "TODO:"
        assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
        with open(prompt_path, 'r') as f:
            prompt = f.read()
            prompt = prompt.replace("###", code)
            prompt = prompt.replace("@@@", str(macro_definitions))
        logger.debug(f"Prompt for finding macro substitutions: {len(prompt)} characters.")
        response = query(prompt)
        try:
            response_json = json.loads(scrutinize_json(response))
        except Exception as e:
            logger.error(f"Bad format: {response}")
            raise e
        logger.debug(f"Query substitutions: {response_json}")
        return response_json

    def supplement_code(self, code, FUNCTION_DEPTH=None):
        definitions = []
        queue = []
        next_level = []
        current_depth = 1
        MAX_DEPTH = 1
        callee_functions = self.query_callee_functions(code)
        queue += callee_functions
        visited = set()
        function_count = 0
        while True:
            logger.debug(f"Queue: {queue}")
            if len(queue) == 0:
                if len(next_level) == 0:
                    break
                queue = next_level
                next_level = []
                current_depth += 1
                if FUNCTION_DEPTH is None:
                    if current_depth > MAX_DEPTH:
                        logger.debug(f"Max depth reached: {current_depth}")
                        break
                else:
                    if function_count >= FUNCTION_DEPTH:
                        logger.debug(f"Function count reached: {function_count}")
                        break
                continue
            func = queue.pop(0)
            if func not in visited:
                visited.add(func)
            else:
                continue
            _definitions = self.repo_extractor.get_function_definition(func)
            if _definitions is not None:
                function_count += 1
                definitions += _definitions
                callee_functions = self.query_callee_functions('\n'.join(_definitions))
                next_level += callee_functions
        return '\n'.join(definitions)

    def analyze(self):
        parsing_code_path = os.path.join(self.output_dir, "TODO:")
        state_variables_path = os.path.join(self.output_dir, "TODO:")
        assert os.path.exists(parsing_code_path), f"Parsing code file {parsing_code_path} does not exist."
        assert os.path.exists(state_variables_path), f"State variables file {state_variables_path} does not exist."
        parsing_code = self.load_json(parsing_code_path)
        state_variables = self.load_json(state_variables_path)
        analysis_result_with_macro_path = os.path.join(self.output_dir, "TODO:")
        tmp_results = self.load_json(analysis_result_with_macro_path) if os.path.exists(analysis_result_with_macro_path) else {}
        option_groups = []
        for i in range(0, len(parsing_code), 5):
            option_group = list(parsing_code.keys())[i:i + 5]
            option_group = [opt for opt in option_group if opt not in tmp_results]
            if len(option_group) == 0:
                continue
            option_groups.append(option_group)
        for option_group in option_groups:
            start_time = time.time()
            append_log(self.log_path, f"Start analyzing {option_group} parsing code in {self.repo_path} for program {self.prog_name}: {start_time}")
            code = ""
            for option in option_group:
                code = code + "\n" + option + ":\n" + parsing_code[option]
            if len(code) == 0:
                continue
            supplemented_code = self.supplement_code(code)
            prompt_path = "TODO:"
            assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
            with open(prompt_path, 'r') as f:
                prompt = f.read()
                prompt = prompt.replace("+++", ",".join(option_group))
                prompt = prompt.replace("@@@", str(code))
                prompt = prompt.replace("###", str(supplemented_code))
                prompt = prompt.replace("$$$", ",".join(state_variables))
            logger.debug(f"Prompt for analyzing {option_group} parsing code: {len(prompt)} characters.")
            response = query(prompt)
            response_json = json.loads(response)
            tmp_results.update(response_json)
            self.update_json(response_json, analysis_result_with_macro_path)
            end_time = time.time()
            append_log(self.log_path, f"Finished analyzing {option_group} parsing code in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")

    def parse_and_analyze(self, group_cnt=5):
        all_options_path = os.path.join(self.output_dir, "TODO:")
        all_options_pruned_path = os.path.join(self.output_dir, "TODO:")
        state_variables_path = os.path.join(self.output_dir, "TODO:")
        assert os.path.exists(all_options_path), f"Parsing code file {all_options_path} does not exist."
        assert os.path.exists(state_variables_path), f"State variables file {state_variables_path} does not exist."
        if os.path.exists(all_options_pruned_path):
            logger.debug(f"All options pruned file {all_options_pruned_path} exists, loading from it.")
            all_options = self.load_json(all_options_pruned_path)
        else:
            all_options = self.load_json(all_options_path)
        state_variables = self.load_json(state_variables_path)
        analysis_result_with_macro_path = os.path.join(self.output_dir, "TODO:")
        tmp_results = self.load_json(analysis_result_with_macro_path) if os.path.exists(analysis_result_with_macro_path) else {}
        option_groups = []
        for i in range(0, len(all_options), group_cnt):
            option_group = all_options[i:i + group_cnt]
            option_group = [opt for opt in option_group if opt not in tmp_results]
            if len(option_group) == 0:
                continue
            option_groups.append(option_group)
        for option_group in option_groups:
            start_time = time.time()
            append_log(self.log_path, f"Start analyzing {option_group} in {self.repo_path} for program {self.prog_name}: {start_time}")
            code = ""
            supplemented_code = ""
            function_definitions_path = os.path.join(self.output_dir, "function_definitions")
            if os.path.exists(function_definitions_path):
                existed_definition_name_and_paths = [
                    (os.path.splitext(f)[0], os.path.join(function_definitions_path, f)) for f in os.listdir(function_definitions_path)
                ]
                for name, definition_path in existed_definition_name_and_paths:
                    with open(definition_path, 'r', encoding='utf-8') as f:
                        code += "\n" + f.read()
            global_vars_path = os.path.join(self.output_dir, "TODO:")
            if os.path.exists(global_vars_path):
                existed_definition_name_and_paths = [
                    (os.path.splitext(f)[0], os.path.join(global_vars_path, f)) for f in os.listdir(global_vars_path)
                ]
                for name, definition_path in existed_definition_name_and_paths:
                    with open(definition_path, 'r', encoding='utf-8') as f:
                        supplemented_code += "\n" + f.read()
            prompt_path = "TODO:"
            assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
            with open(prompt_path, 'r') as f:
                prompt = f.read()
                prompt = prompt.replace("+++", ",".join(option_group))
                prompt = prompt.replace("@@@", str(code))
                prompt = prompt.replace("###", str(supplemented_code))
                prompt = prompt.replace("$$$", ",".join(state_variables))
            logger.debug(f"Prompt for analyzing {option_group} parsing code: {len(prompt)} characters.")
            response = query(prompt)
            response_json = json.loads(response)
            tmp_results.update(response_json)
            self.update_json(response_json, analysis_result_with_macro_path)
            end_time = time.time()
            append_log(self.log_path, f"Finished analyzing {option_group} parsing code in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")

    def parse_and_analyze_worker(self, worker_id, pool_queue, a):
        success = False
        fail_cnt = 0
        worker_total_fail_cnt = 0
        WORKER_MAX_ALLOW_FAIL_CNT = 3
        group_cnt = a
        group_cnt_1_cnt = 0
        degrade = False
        while True:
            if fail_cnt >= 2:
                group_cnt -= 1
                if group_cnt == 0:
                    group_cnt = 1
                if group_cnt == 1:
                    group_cnt_1_cnt += 1
                if group_cnt_1_cnt >= 3:
                    logger.error(f"Worker {worker_id}: too many failures")
                    degrade = True
                fail_cnt = 0
            option_group = []
            for _ in range(group_cnt):
                try:
                    item = pool_queue.get(timeout=1)
                except queue.Empty:
                    logger.debug(f"Worker {worker_id}: the queue has been emptied.")
                    break
                option_group.append(item)
            if len(option_group) == 0:
                logger.debug(f"Worker {worker_id}: no items to process, exiting.")
                break
            logger.debug(f"Worker {worker_id} got items: {option_group}")
            start_time = time.time()
            append_log(self.log_path, f"Start analyzing {option_group} in {self.repo_path} for program {self.prog_name}: {start_time}")
            analysis_result_with_macro_path = os.path.join(self.output_dir, "TODO:")
            state_variables_path = os.path.join(self.output_dir, "TODO:")
            state_variables = self.load_json(state_variables_path)
            code = ""
            supplemented_code = ""
            function_definitions_path = os.path.join(self.output_dir, "function_definitions")
            if os.path.exists(function_definitions_path):
                existed_definition_name_and_paths = [
                    (os.path.splitext(f)[0], os.path.join(function_definitions_path, f)) for f in os.listdir(function_definitions_path)
                ]
                for name, definition_path in existed_definition_name_and_paths:
                    with open(definition_path, 'r', encoding='utf-8') as f:
                        code += "\n" + f.read()
            global_vars_path = os.path.join(self.output_dir, "TODO:")
            if os.path.exists(global_vars_path):
                existed_definition_name_and_paths = [
                    (os.path.splitext(f)[0], os.path.join(global_vars_path, f)) for f in os.listdir(global_vars_path)
                ]
                for name, definition_path in existed_definition_name_and_paths:
                    with open(definition_path, 'r', encoding='utf-8') as f:
                        supplemented_code += "\n" + f.read()
            prompt_path = "TODO:"
            assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
            with open(prompt_path, 'r') as f:
                prompt = f.read()
                prompt = prompt.replace("+++", ",".join(option_group))
                prompt = prompt.replace("@@@", str(code))
                prompt = prompt.replace("###", str(supplemented_code))
                prompt = prompt.replace("$$$", ",".join(state_variables))
            logger.debug(f"Prompt for analyzing {option_group} parsing code: {len(prompt)} characters.")
            try:
                response = query(prompt)
                response_json = json.loads(response)
                self.update_json_thread_safe(response_json, analysis_result_with_macro_path)
                end_time = time.time()
                append_log(self.log_path, f"Finished analyzing {option_group} parsing code in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")
            except Exception as e:
                logger.error(f"Worker {worker_id} failed to query: {e}")
                fail_cnt += 1
                worker_total_fail_cnt += 1
                if worker_total_fail_cnt >= WORKER_MAX_ALLOW_FAIL_CNT:
                    logger.error(f"Worker {worker_id}: reached maximum fail count, exiting.")
                    response_json = {opt: [] for opt in option_group}
                    self.update_json_thread_safe(response_json, analysis_result_with_macro_path)
                    for _ in range(len(option_group)):
                        pool_queue.task_done()
                    break
                for item in option_group:
                    pool_queue.put(item)
                continue
            for _ in range(len(option_group)):
                pool_queue.task_done()

    def parse_and_analyze_in_parallel(self, thread_cnt=5, group_cnt=5):
        all_options_path = os.path.join(self.output_dir, "TODO:")
        all_options_pruned_path = os.path.join(self.output_dir, "TODO:")
        state_variables_path = os.path.join(self.output_dir, "TODO:")
        assert os.path.exists(all_options_path), f"Parsing code file {all_options_path} does not exist."
        assert os.path.exists(state_variables_path), f"State variables file {state_variables_path} does not exist."
        if os.path.exists(all_options_pruned_path):
            logger.debug(f"All options pruned file {all_options_pruned_path} exists, loading from it.")
            all_options = self.load_json(all_options_pruned_path)
        else:
            all_options = self.load_json(all_options_path)
        state_variables = self.load_json(state_variables_path)
        analysis_result_with_macro_path = os.path.join(self.output_dir, "TODO:")
        tmp_results = self.load_json(analysis_result_with_macro_path) if os.path.exists(analysis_result_with_macro_path) else {}
        option_groups = []
        pool_queue = queue.Queue()
        for option in all_options:
            if option in tmp_results:
                continue
            pool_queue.put(option)
        threads = []
        for i in range(thread_cnt):
            t = threading.Thread(target=self.parse_and_analyze_worker, args=(i, pool_queue, group_cnt))
            t.start()
            threads.append(t)
        for t in threads:
            t.join()

    def simplify_value(self):
        from evaluator import simplify_expression
        var_value_setting_path = os.path.join(self.output_dir, "TODO:")
        var_value_setting_simplified = os.path.join(self.output_dir, "TODO:")
        assert os.path.exists(var_value_setting_path), f"Analysis result file {var_value_setting_path} does not exist."
        analysis_result = self.load_json(var_value_setting_path)
        start_time = time.time()
        append_log(self.log_path, f"Start var_value_setting simplifying analysis result in {self.repo_path} for program {self.prog_name}: {start_time}")
        response_json = {}
        for var, group_list in analysis_result.items():
            '''
            "--no-xattrs": [
                [
                    "[]",
                    "[\"extract_flags = (extract_flags) & (-129)\", \"readdisk_flags = (readdisk_flags) | (16)\", \"flags = (flags) | (32768)\"]"
                ]
            ],
            '''
            for i, group in enumerate(group_list):
                try:
                    evaluated_value_list = eval(group[1])
                except Exception as e:
                    logger.error(f"Error evaluating value for group {group}: {e}")
                    evaluated_value_list = group[1]
                    raise
                for j, v in enumerate(evaluated_value_list):
                    if v.endswith(' = '):
                        v = v + '""'
                    v = v.replace("${OPTVAL_INT}", "__TEMP_OPTVAL_INT__")
                    v = v.replace("${OPTVAL_FP}", "__TEMP_OPTVAL_FP__")
                    v = v.replace("${OPTVAL_FLOAT}", "__TEMP_OPTVAL_FLOAT__")
                    v = v.replace("${OPTVAL}", "__TEMP_OPTVAL__")
                    evaluated_value_list[j] = v

                simplified_value_list = []
                for expr in evaluated_value_list:
                    try:
                        simplified_expr = simplify_expression(expr)
                        simplified_value_list.append(simplified_expr)
                    except Exception as e:
                        logger.error(f"Error simplifying expression '{expr}': {e}")
                        logger.error(f"  current group: {group}")
                        logger.error(f"  current program: {self.prog_name}, repo: {self.repo_path}")
                        logger.error(f"  fallback to original expression.")
                        simplified_value_list.append(expr)
                        input("Press Enter to continue after error simplifying expression.")

                for j, v in enumerate(simplified_value_list):
                    v = v.replace("__TEMP_OPTVAL_INT__", "${OPTVAL_INT}")
                    v = v.replace("__TEMP_OPTVAL_FP__", "${OPTVAL_FP}")
                    v = v.replace("__TEMP_OPTVAL_FLOAT__", "${OPTVAL_FLOAT}")
                    v = v.replace("__TEMP_OPTVAL__", "${OPTVAL}")
                    simplified_value_list[j] = v

                simplified_value_list_str = json.dumps(simplified_value_list)
                group_list[i][1] = simplified_value_list_str
            response_json[var] = group_list
        self.save_json(response_json, var_value_setting_simplified)
        end_time = time.time()
        append_log(self.log_path, f"Finished var_value_setting simplifying result in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")

    def refine_extract(self):
        analysis_result_with_macro_path = os.path.join(self.output_dir, "TODO:")
        analysis_result_with_macro_refined_path = os.path.join(self.output_dir, "TODO:")
        assert os.path.exists(analysis_result_with_macro_path), f"Analysis result file {analysis_result_with_macro_path} does not exist."
        if os.path.exists(analysis_result_with_macro_refined_path):
            logger.debug(f"Analysis result with macro refined file {analysis_result_with_macro_refined_path} exists, skipping refinement.")
            return
        analysis_result = self.load_json(analysis_result_with_macro_path)
        start_time = time.time()
        append_log(self.log_path, f"Start refining analysis result with macro in {self.repo_path} for program {self.prog_name}: {start_time}")
        prompt_path = "TODO:"
        assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
        with open(prompt_path, 'r') as f:
            prompt = f.read()
            prompt = prompt.replace("@@@", str(analysis_result))
        logger.debug(f"Prompt for refining analysis result with macro: {len(prompt)} characters.")
        response = query(prompt)
        logger.debug(f"Response for refining analysis result with macro: {response}")
        response_json = json.loads(scrutinize_json(response))
        logger.debug(f"Refined analysis result with macro: {response_json}")
        self.save_json(response_json, analysis_result_with_macro_refined_path)
        end_time = time.time()
        append_log(self.log_path, f"Finished refining analysis result with macro in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")

    def refine(self):
        refine_list = []
        save_path = "TODO:"
        raw_path = "TODO:"
        assert os.path.exists(raw_path), f"Raw analysis result file {raw_path} does not exist."
        if not os.path.exists(save_path):
            os.system(f"cp {raw_path} {save_path}")
        assert os.path.exists(save_path), f"Refined analysis result file {save_path} does not exist."
        analysis_result = self.load_json(save_path)
        parsing_code_path = "TODO:"
        state_variables_path = "TODO:"
        parsing_code = self.load_json(parsing_code_path)
        state_variables = self.load_json(state_variables_path)
        FUNCTION_DEPTH = 10
        for refine_option in refine_list:
            assert refine_option in analysis_result, f"Refine option {refine_option} not found in analysis result."
            code = ""
            code = code + "\n" + refine_option + ":\n" + parsing_code[refine_option]
            if len(code) == 0:
                continue
            supplemented_code = self.supplement_code(code, FUNCTION_DEPTH)
            prompt_path = "TODO:"
            assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
            with open(prompt_path, 'r') as f:
                prompt = f.read()
                prompt = prompt.replace("+++", refine_option)
                prompt = prompt.replace("@@@", str(code))
                prompt = prompt.replace("###", str(supplemented_code))
                prompt = prompt.replace("$$$", ",".join(state_variables))
            logger.debug(f"Prompt for analyzing {refine_option} parsing code: {len(prompt)} characters.")
            response = query(prompt)
            response_json = json.loads(response)
            self.update_json(response_json, save_path)

    def resolve_macro(self):
        analysis_result_resolved_path = os.path.join(self.output_dir, "TODO:")
        input_path = os.path.join(self.output_dir, "TODO:")
        assert os.path.exists(input_path), f"Input file {input_path} does not exist."
        analysis_result = self.load_json(input_path)
        resolved_result = self.load_json(analysis_result_resolved_path) if os.path.exists(analysis_result_resolved_path) else {}
        option_groups = []
        group_cnt = len(analysis_result)
        for i in range(0, len(analysis_result), group_cnt):
            option_group = list(analysis_result.keys())[i:i + group_cnt]
            option_group = [opt for opt in option_group if opt not in resolved_result]
            if len(option_group) == 0:
                continue
            option_groups.append(option_group)
        for option_group in option_groups:
            start_time = time.time()
            append_log(self.log_path, f"Start resolving macros for {option_group} parsing code in {self.repo_path} for program {self.prog_name}: {start_time}")
            group_info = {}
            for option in option_group:
                option_info = analysis_result[option]
                group_info[option] = option_info
            original_content = str(group_info)
            macros = self.query_macros(original_content)
            if len(macros) == 0:
                logger.debug(f"No macros found for {option}, skipping.")
                continue
            macro_definitions = self.repo_extractor.get_macro_definitions(macros)
            logger.debug(f"Macro definitions: {macro_definitions}")
            resolved_content_json = self.query_substitutions(original_content, macro_definitions)
            for resolved_option, resolved_content in resolved_content_json.items():
                resolved_result[resolved_option] = resolved_content
            logger.debug(f"Resolved content: {resolved_content_json}")
            resolved_result.update(resolved_content_json)
            self.update_json(resolved_content_json, analysis_result_resolved_path)
        assert len(resolved_result) == len(analysis_result), "Resolved result length does not match analysis result length."

    def resolve_macro_worker(self, worker_id, pool_queue, group_cnt):
        success = False
        fail_cnt = 0
        worker_total_fail_cnt = 0
        WORKER_MAX_ALLOW_FAIL_CNT = 3
        group_cnt_1_cnt = 0
        degrade = True
        while True:
            if fail_cnt >= 2:
                group_cnt -= 1
                if group_cnt == 0:
                    group_cnt = 1
                if group_cnt == 1:
                    group_cnt_1_cnt += 1
                if group_cnt_1_cnt >= 3:
                    logger.error(f"Worker {worker_id}: too many failures")
                    degrade = True
                fail_cnt = 0
            option_group = []
            for _ in range(group_cnt):
                try:
                    item = pool_queue.get(timeout=1)
                except queue.Empty:
                    logger.debug(f"Worker {worker_id}: the queue has been emptied.")
                    break
                option_group.append(item)
            if len(option_group) == 0:
                logger.debug(f"Worker {worker_id}: no items to process, exiting.")
                break
            logger.debug(f"Worker {worker_id} got items: {option_group}")
            start_time = time.time()
            append_log(self.log_path, f"Start resolving macros for {option_group} parsing code in {self.repo_path} for program {self.prog_name}: {start_time}")
            analysis_result_with_macro_path = os.path.join(self.output_dir, "TODO:")
            analysis_result_resolved_path = os.path.join(self.output_dir, "TODO:")
            analysis_result = self.load_json(analysis_result_with_macro_path)
            group_info = {}
            for option in option_group:
                option_info = analysis_result[option]
                group_info[option] = option_info
            original_content = str(group_info)
            resolved_content_json = {}
            try:
                macros = self.query_macros(original_content)
                if len(macros) > 0:
                    macro_definitions = self.repo_extractor.get_macro_definitions(macros)
                    logger.debug(f"Macro definitions: {macro_definitions}")
                    resolved_content_json = self.query_substitutions(original_content, macro_definitions)
                else:
                    logger.debug(f"No macros found for {option}, keeping original content.")
                    for option in option_group:
                        resolved_content_json[option] = analysis_result[option]
                self.update_json_thread_safe(resolved_content_json, analysis_result_resolved_path)
                end_time = time.time()
                append_log(self.log_path, f"Finished resolving macros for {option_group} parsing code in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")
            except Exception as e:
                logger.error(f"Worker {worker_id} failed to query: {e}")
                import traceback
                traceback.print_exc()
                fail_cnt += 1
                worker_total_fail_cnt += 1
                if worker_total_fail_cnt >= WORKER_MAX_ALLOW_FAIL_CNT:
                    logger.error(f"Worker {worker_id}: reached maximum fail count, exiting.")
                    resolved_content_json = {opt: analysis_result[opt] for opt in option_group}
                    self.update_json_thread_safe(resolved_content_json, analysis_result_resolved_path)
                    for _ in range(len(option_group)):
                        pool_queue.task_done()
                    break
                for item in option_group:
                    pool_queue.put(item)
                continue
            for _ in range(len(option_group)):
                pool_queue.task_done()

    def resolve_macro_in_parallel(self, thread_cnt=5, group_cnt=5):
        analysis_result_resolved_path = os.path.join(self.output_dir, "TODO:")
        input_path = os.path.join(self.output_dir, "TODO:")
        assert os.path.exists(input_path), f"Input file {input_path} does not exist."
        analysis_result = self.load_json(input_path)
        resolved_result = self.load_json(analysis_result_resolved_path) if os.path.exists(analysis_result_resolved_path) else {}
        option_groups = []
        pool_queue = queue.Queue()
        for option in analysis_result:
            if option in resolved_result:
                continue
            pool_queue.put(option)
        threads = []
        for i in range(thread_cnt):
            t = threading.Thread(target=self.resolve_macro_worker, args=(i, pool_queue, group_cnt))
            t.start()
            threads.append(t)
        for t in threads:
            t.join()

    def parse(self):
        possible_option_parsing_functions_result_path = os.path.join(self.output_dir, "TODO:")
        assert os.path.exists(possible_option_parsing_functions_result_path), f"Possible option parsing functions file {possible_option_parsing_functions_result_path} does not exist."
        possible_option_parsing_functions = self.load_json(possible_option_parsing_functions_result_path)
        parsing_code_result_path = os.path.join(self.output_dir, "TODO:")
        if not os.path.exists(parsing_code_result_path):
            start_time = time.time()
            append_log(self.log_path, f"Start finding option parsing code in {self.repo_path} for program {self.prog_name}: {start_time}")
            self.find_all_options(possible_option_parsing_functions)
            parsing_code = self.find_option_parsing_code(possible_option_parsing_functions)
            assert parsing_code is not None, "No option parsing code found."
            end_time = time.time()
            append_log(self.log_path, f"Finished finding option parsing code in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")
            self.save_json(parsing_code, parsing_code_result_path)
            assert os.path.exists(parsing_code_result_path), f"Option parsing code result file {parsing_code_result_path} does not exist."
        else:
            logger.debug(f"Option parsing code result file {parsing_code_result_path} already exists, loading from it.")
            parsing_code = self.load_json(parsing_code_result_path)

    def find_option_parsing_start_code(self):
        possible_option_parsing_functions_result_path = os.path.join(self.output_dir, "TODO:")
        assert os.path.exists(possible_option_parsing_functions_result_path), f"Possible option parsing functions file {possible_option_parsing_functions_result_path} does not exist."
        possible_option_parsing_functions = self.load_json(possible_option_parsing_functions_result_path)
        parsing_start_result_path = os.path.join(self.output_dir, "TODO:")
        if not os.path.exists(parsing_start_result_path):
            logger.debug(f"Option parsing code start result file {parsing_start_result_path} does not exist, finding it.")
            start_time = time.time()
            append_log(self.log_path, f"Start finding option parsing code start in {self.repo_path} for program {self.prog_name}: {start_time}")
            possible_parsing_start = self.find_option_parsing_start(possible_option_parsing_functions)
            assert possible_parsing_start is not None, "No option parsing code start found."
            end_time = time.time()
            append_log(self.log_path, f"Finished finding option parsing code start in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")
            self.save_json(possible_parsing_start, parsing_start_result_path)
            assert os.path.exists(parsing_start_result_path), f"Option parsing code start result file {parsing_start_result_path} does not exist."
        else:
            logger.debug(f"Option parsing code start result file {parsing_start_result_path} already exists, loading from it.")
            possible_parsing_start = self.load_json(parsing_start_result_path)


    def process_repo(self):
        possible_option_parsing_files_result_path = os.path.join(self.output_dir, "TODO:")
        if not os.path.exists(possible_option_parsing_files_result_path):
            start_time = time.time()
            append_log(self.log_path, f"Start finding option parsing files in {self.repo_path} for program {self.prog_name}: {start_time}")
            possible_option_parsing_files = self.find_option_parsing_files()
            assert len(possible_option_parsing_files) > 0, "No possible option parsing files found."
            possible_main_file = possible_option_parsing_files["1"]
            logger.debug(f"Possible main file: {possible_main_file}")
            end_time = time.time()
            append_log(self.log_path, f"Finished finding option parsing files in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")
            self.save_json(possible_option_parsing_files, possible_option_parsing_files_result_path)
            assert os.path.exists(possible_option_parsing_files_result_path), f"Possible option parsing files result file {possible_option_parsing_files_result_path} does not exist."
        else:
            logger.debug(f"Possible option parsing files result file {possible_option_parsing_files_result_path} already exists, loading from it.")
            possible_option_parsing_files = self.load_json(possible_option_parsing_files_result_path)
            possible_main_file = possible_option_parsing_files["1"]
        main_lines = self.repo_extractor.get_definition_debug_lines("main")
        assert len(main_lines) == 1, f"Main function should have exactly one line. Found: {main_lines}"
        possible_main_file_abs = os.path.join(os.path.dirname(self.repo_path), list(main_lines.keys())[0])
        possible_main_file = os.path.relpath(possible_main_file_abs, self.repo_path)
        logger.debug(f"Possible main file: {possible_main_file}")
        self.repo_extractor.update_main_path(possible_main_file)
        possible_state_variables_result_path = os.path.join(self.output_dir, "TODO:")
        if not os.path.exists(possible_state_variables_result_path):
            start_time = time.time()
            append_log(self.log_path, f"Start finding state variables in {self.repo_path} for program {self.prog_name}: {start_time}")
            possible_state_variables = self.find_state_variables(possible_option_parsing_files)
            assert possible_state_variables is not None, "No possible state variables found."
            end_time = time.time()
            append_log(self.log_path, f"Finished finding state variables in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")
            self.save_json(possible_state_variables, possible_state_variables_result_path)
            assert os.path.exists(possible_state_variables_result_path), f"Possible state variables result file {possible_state_variables_result_path} does not exist."
        else:
            logger.debug(f"Possible state variables result file {possible_state_variables_result_path} already exists, loading from it.")
            possible_state_variables = self.load_json(possible_state_variables_result_path)
        possible_option_parsing_functions_result_path = os.path.join(self.output_dir, "TODO:")
        if not os.path.exists(possible_option_parsing_functions_result_path):
            start_time = time.time()
            append_log(self.log_path, f"Start finding option parsing functions in {self.repo_path} for program {self.prog_name}: {start_time}")
            possible_option_parsing_functions = self.find_option_parsing_functions(possible_option_parsing_files)
            assert possible_option_parsing_functions is not None, "No possible option parsing functions found."
            end_time = time.time()
            append_log(self.log_path, f"Finished finding option parsing functions in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")
            self.save_json(possible_option_parsing_functions, possible_option_parsing_functions_result_path)
            assert os.path.exists(possible_option_parsing_functions_result_path), f"Possible option parsing functions result file {possible_option_parsing_functions_result_path} does not exist."
        else:
            logger.debug(f"Possible option parsing functions result file {possible_option_parsing_functions_result_path} already exists, loading from it.")
            possible_option_parsing_functions = self.load_json(possible_option_parsing_functions_result_path)
        self.find_all_options(possible_option_parsing_functions)

    def save_results(self, output_file):
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(self.results, f, indent=4, ensure_ascii=False)

    def load_json(self, input_file):
        assert os.path.exists(input_file), f"Input file {input_file} does not exist."
        with open(input_file, 'r', encoding='utf-8') as f:
            content = f.read()
            data = json.loads(content)
        return data

    def save_json(self, obj, output_file):
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(obj, f, indent=4, ensure_ascii=False)

    def update_json(self, obj, output_file):
        if not os.path.exists(output_file):
            with open(output_file, 'w', encoding='utf-8') as f:
                json.dump(obj, f, indent=4, ensure_ascii=False)
        else:
            with open(output_file, 'r', encoding='utf-8') as f:
                data = json.load(f)
            data.update(obj)
            with open(output_file, 'w', encoding='utf-8') as f:
                json.dump(data, f, indent=4, ensure_ascii=False)

    def update_json_thread_safe(self, obj, output_file):
        with self._global_lock:
            self.update_json(obj, output_file)

    def segment_code(self):
        segment_code_result_path = os.path.join(self.output_dir, "TODO:")
        if os.path.exists(segment_code_result_path):
            logger.debug(f"Code segments file {segment_code_result_path} already exists, skipping.")
            return
        possible_option_parsing_files_result_path = os.path.join(self.output_dir, "TODO:")
        assert os.path.exists(possible_option_parsing_files_result_path), f"Possible option parsing files file {possible_option_parsing_files_result_path} does not exist."
        possible_option_parsing_files = self.load_json(possible_option_parsing_files_result_path)
        assert len(possible_option_parsing_files) > 0, "No possible option parsing files found."
        possible_main_file = possible_option_parsing_files["1"]
        code = ""
        with open(os.path.join(self.repo_path, possible_main_file), 'r', encoding='utf-8') as f:
            lines = f.readlines()
            numbered_lines = []
            for i, line in enumerate(lines, 1):
                line = line.rstrip()
                numbered_line = f"{i}. {line}\n"
                numbered_lines.append(numbered_line)
            code = "".join(numbered_lines)
        assert len(code) > 0, f"Code in file {possible_main_file} is empty."
        prompt_path = "TODO:"
        assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
        with open(prompt_path, 'r') as f:
            prompt = f.read()
            prompt = prompt.replace("###", code)
        start_time = time.time()
        append_log(self.log_path, f"Start segmenting code in {self.repo_path} for program {self.prog_name}: {start_time}")
        logger.debug(f"Prompt for segment code: {len(prompt)} characters.")
        try:
            response = query(prompt)
        except Exception as e:
            logger.error(f"Failed to query for segmenting code: {e}")
            response = query(prompt)
        logger.info(f"segment_code response: {response}")
        response_json = json.loads(response)
        end_time = time.time()
        append_log(self.log_path, f"Finished segmenting code in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")
        result = {
            "file": possible_main_file,
            "segments": response_json
        }
        self.save_json(result, segment_code_result_path)
        assert os.path.exists(segment_code_result_path), f"Code segments file {segment_code_result_path} does not exist."
    
    def sample_optval_in_parallel(self, thread_cnt=5, group_cnt=5):
        sample_optval_result_path = os.path.join(
            self.output_dir,
            "TODO:"
        )
        optval_path = os.path.join(self.output_dir, "TODO:")
        assert os.path.exists(optval_path), f"OPTVAL json file {optval_path} does not exist."
        all_optval_options = self.load_json(optval_path)
        sample_optval_result = self.load_json(sample_optval_result_path) if os.path.exists(sample_optval_result_path) else {}
        manual_path = self.program_manual_path
        assert os.path.exists(manual_path), f"Program manual file {manual_path} does not exist."
        manual_content = ""
        try:
            env = os.environ.copy()
            env["MANWIDTH"] = "1000"
            cmd = f"MANWIDTH=1000 man -l {manual_path} | col -bx"
            proc = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env, text=True)
            if proc.returncode == 0 and proc.stdout.strip():
                manual_content = proc.stdout
            else:
                with open(manual_path, 'r', encoding='utf-8', errors='ignore') as f:
                    manual_content = f.read()
        except Exception as e:
            logger.error(f"Failed running man on {manual_path}: {e}")
            with open(manual_path, 'r', encoding='utf-8', errors='ignore') as f:
                manual_content = f.read()
        pool_queue = queue.Queue()
        for option in all_optval_options:
            if option in sample_optval_result:
                continue
            pool_queue.put(option)
        threads = []
        for i in range(thread_cnt):
            t = threading.Thread(target=self.sample_optval_worker, args=(i, pool_queue, group_cnt, manual_content))
            t.start()
            threads.append(t)
        for t in threads:
            t.join()

    def sample_optval_worker(self, worker_id, pool_queue, group_cnt, manual_content):
        success = False
        fail_cnt = 0
        group_cnt_1_cnt = 0
        degrade = True
        while True:
            if fail_cnt >= 2:
                group_cnt -= 1
                if group_cnt == 0:
                    group_cnt = 1
                if group_cnt == 1:
                    group_cnt_1_cnt += 1
                if group_cnt_1_cnt >= 3:
                    logger.error(f"Worker {worker_id}: too many failures")
                    degrade = True
                fail_cnt = 0
            option_group = []
            for _ in range(group_cnt):
                try:
                    item = pool_queue.get(timeout=1)
                except queue.Empty:
                    logger.debug(f"Worker {worker_id}: the queue has been emptied.")
                    break
                option_group.append(item)
            if len(option_group) == 0:
                logger.debug(f"Worker {worker_id}: no items to process, exiting.")
                break
            logger.debug(f"Worker {worker_id} got items: {option_group}")
            start_time = time.time()
            append_log(self.log_path, f"Start sampling optval for {option_group} in {self.repo_path} for program {self.prog_name}: {start_time}")
            sample_optval_result_path = os.path.join(self.output_dir, "TODO:")
            try:
                prompt_path = "TODO:"
                assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
                with open(prompt_path, 'r') as f:
                    prompt = f.read()
                    prompt = prompt.replace("@@@", manual_content)
                    prompt = prompt.replace("$$$", "\n".join(option_group))
                logger.debug(f"Prompt for sample optval: {len(prompt)} characters.")
                response = query(prompt)
                logger.info(f"sample_optval response: {response}")
                response_json = json.loads(scrutinize_json(response))
                self.update_json_thread_safe(response_json, sample_optval_result_path)
                end_time = time.time()
                append_log(self.log_path, f"Finished sampling optval for {option_group} in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")
            except Exception as e:
                logger.error(f"Worker {worker_id} failed to query: {e}")
                fail_cnt += 1
                for item in option_group:
                    pool_queue.put(item)
                continue
            for _ in range(len(option_group)):
                pool_queue.task_done()

    def add_check_constraints_in_parallel(self, thread_cnt=5, group_cnt=5):
        add_check_constraints_result_path = os.path.join(
            self.output_dir,
            "TODO:"
        )
        input_path = os.path.join(self.output_dir, "TODO:")
        assert os.path.exists(input_path), f"Input file {input_path} does not exist."
        analysis_result = self.load_json(input_path)
        add_check_constraints_result = self.load_json(add_check_constraints_result_path) if os.path.exists(add_check_constraints_result_path) else {}
        segment_code_result_path = os.path.join(self.output_dir, "TODO:")
        assert os.path.exists(segment_code_result_path), f"Code segments file {segment_code_result_path} does not exist."
        segment_code_result = self.load_json(segment_code_result_path)
        main_file_path = os.path.join(self.repo_path, segment_code_result["file"])
        main_code_lines = ""
        with open(main_file_path, 'r', encoding='utf-8') as f:
            main_code_lines = f.readlines()
        segments = segment_code_result["segments"]
        relevant_segments = []
        for segment in segments:
            assert len(segment) == 4, f"Segment {segment} does not have 4 elements."
            start_line = int(segment[0])
            end_line = int(segment[1])
            segment_type = segment[2]
            description = segment[3]
            # TODO:
            if segment_type == "check":
                assert start_line <= end_line, f"Start line {start_line} is greater than end line {end_line}."
                assert start_line > 0 and end_line <= len(main_code_lines), f"Start line {start_line} or end line {end_line} is out of range."
                relevant_segment = main_code_lines[start_line - 1:end_line]
                relevant_segments.append("".join(relevant_segment))
        relevant_code = "...\n".join(relevant_segments)
        pool_queue = queue.Queue()
        for option in analysis_result:
            if option in add_check_constraints_result:
                continue
            pool_queue.put(option)
        threads = []
        for i in range(thread_cnt):
            t = threading.Thread(target=self.add_check_constraints_worker, args=(i, pool_queue, group_cnt, relevant_code))
            t.start()
            threads.append(t)
        for t in threads:
            t.join()

    def add_check_constraints_worker(self, worker_id, pool_queue, group_cnt, relevant_code):
        success = False
        fail_cnt = 0
        group_cnt_1_cnt = 0
        degrade = True
        while True:
            if fail_cnt >= 2:
                group_cnt -= 1
                if group_cnt == 0:
                    group_cnt = 1
                if group_cnt == 1:
                    group_cnt_1_cnt += 1
                if group_cnt_1_cnt >= 3:
                    logger.error(f"Worker {worker_id}: too many failures")
                    degrade = True
                fail_cnt = 0
            option_group = []
            for _ in range(group_cnt):
                try:
                    item = pool_queue.get(timeout=1)
                except queue.Empty:
                    logger.debug(f"Worker {worker_id}: the queue has been emptied.")
                    break
                option_group.append(item)
            if len(option_group) == 0:
                logger.debug(f"Worker {worker_id}: no items to process, exiting.")
                break
            logger.debug(f"Worker {worker_id} got items: {option_group}")
            start_time = time.time()
            append_log(self.log_path, f"Start adding check constraints for {option_group} parsing code in {self.repo_path} for program {self.prog_name}: {start_time}")
            analysis_result_with_macro_path = os.path.join(self.output_dir, "TODO:")
            add_check_constraints_result_path = os.path.join(self.output_dir, "TODO:")
            analysis_result = self.load_json(analysis_result_with_macro_path)
            group_info = {}
            for option in option_group:
                option_info = analysis_result[option]
                group_info[option] = option_info
            original_content = str(group_info)
            try:
                prompt_path = "TODO:"
                assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
                with open(prompt_path, 'r') as f:
                    prompt = f.read()
                    prompt = prompt.replace("###", original_content)
                    prompt = prompt.replace("@@@", relevant_code)
                logger.debug(f"Prompt for add check constraints: {len(prompt)} characters.")
                response = query(prompt)
                logger.info(f"add_check_constraints response: {response}")
                response_json = json.loads(scrutinize_json(response))
                self.update_json_thread_safe(response_json, add_check_constraints_result_path)
                end_time = time.time()
                append_log(self.log_path, f"Finished adding check constraints for {option_group} parsing code in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")
            except Exception as e:
                logger.error(f"Worker {worker_id} failed to query: {e}")
                fail_cnt += 1
                for item in option_group:
                    pool_queue.put(item)
                continue
            for _ in range(len(option_group)):
                pool_queue.task_done()

    def add_check_constraints(self):
        add_check_constraints_result_path = os.path.join(self.output_dir, "TODO:")
        if os.path.exists(add_check_constraints_result_path):
            logger.debug(f"Add check constraints result file {add_check_constraints_result_path} already exists, skipping.")
            return
        segment_code_result_path = os.path.join(self.output_dir, "TODO:")
        assert os.path.exists(segment_code_result_path), f"Code segments file {segment_code_result_path} does not exist."
        segment_code_result = self.load_json(segment_code_result_path)
        main_file_path = os.path.join(self.repo_path, segment_code_result["file"])
        main_code_lines = ""
        with open(main_file_path, 'r', encoding='utf-8') as f:
            main_code_lines = f.readlines()
        segments = segment_code_result["segments"]
        relevant_segments = []
        for segment in segments:
            assert len(segment) == 4, f"Segment {segment} does not have 4 elements."
            start_line = int(segment[0])
            end_line = int(segment[1])
            segment_type = segment[2]
            description = segment[3]
            # TODO:
            if segment_type == "check":
                assert start_line <= end_line, f"Start line {start_line} is greater than end line {end_line}."
                assert start_line > 0 and end_line <= len(main_code_lines), f"Start line {start_line} or end line {end_line} is out of range."
                relevant_segment = main_code_lines[start_line - 1:end_line]
                relevant_segments.append("".join(relevant_segment))
        relevant_code = "...\n".join(relevant_segments)
        analysis_result_with_macro_refined_path = os.path.join(self.output_dir, "TODO:")
        assert os.path.exists(analysis_result_with_macro_refined_path), f"Analysis result with macro refined file {analysis_result_with_macro_refined_path} does not exist."
        with open(analysis_result_with_macro_refined_path, 'r', encoding='utf-8') as f:
            analysis_result = f.read()
        prompt_path = "TODO:"
        assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
        with open(prompt_path, 'r') as f:
            prompt = f.read()
            prompt = prompt.replace("###", analysis_result)
            prompt = prompt.replace("@@@", relevant_code)
        start_time = time.time()
        append_log(self.log_path, f"Start adding check constraints in {self.repo_path} for program {self.prog_name}: {start_time}")
        logger.debug(f"Prompt for add check constraints: {len(prompt)} characters.")
        response = query(prompt)
        logger.info(f"add_check_constraints response: {response}")
        response_json = json.loads(scrutinize_json(response))
        end_time = time.time()
        append_log(self.log_path, f"Finished adding check constraints in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")
        self.save_json(response_json, add_check_constraints_result_path)

    def add_global_check_constraints(self):
        add_global_check_constraints_result_path = os.path.join(self.output_dir, "TODO:")
        if os.path.exists(add_global_check_constraints_result_path):
            logger.debug(f"Add check constraints result file {add_global_check_constraints_result_path} already exists, skipping.")
            return
        segment_code_result_path = os.path.join(self.output_dir, "TODO:")
        assert os.path.exists(segment_code_result_path), f"Code segments file {segment_code_result_path} does not exist."
        segment_code_result = self.load_json(segment_code_result_path)
        main_file_path = os.path.join(self.repo_path, segment_code_result["file"])
        main_code_lines = ""
        with open(main_file_path, 'r', encoding='utf-8') as f:
            main_code_lines = f.readlines()
        segments = segment_code_result["segments"]
        relevant_segments = []
        for segment in segments:
            assert len(segment) == 4, f"Segment {segment} does not have 4 elements."
            start_line = int(segment[0])
            end_line = int(segment[1])
            segment_type = segment[2]
            description = segment[3]
            # TODO:
            if segment_type == "check":
                assert start_line <= end_line, f"Start line {start_line} is greater than end line {end_line}."
                assert start_line > 0 and end_line <= len(main_code_lines), f"Start line {start_line} or end line {end_line} is out of range."
                relevant_segment = main_code_lines[start_line - 1:end_line]
                relevant_segments.append("".join(relevant_segment))
        relevant_code = "...\n".join(relevant_segments)
        analysis_result_with_macro_refined_path = os.path.join(self.output_dir, "TODO:")
        assert os.path.exists(analysis_result_with_macro_refined_path), f"Analysis result with macro refined file {analysis_result_with_macro_refined_path} does not exist."
        with open(analysis_result_with_macro_refined_path, 'r', encoding='utf-8') as f:
            analysis_result = f.read()
        prompt_path = "TODO:"
        assert os.path.exists(prompt_path), f"Prompt file {prompt_path} does not exist."
        with open(prompt_path, 'r') as f:
            prompt = f.read()
            prompt = prompt.replace("###", analysis_result)
            prompt = prompt.replace("@@@", relevant_code)
        start_time = time.time()
        append_log(self.log_path, f"Start adding global check constraints in {self.repo_path} for program {self.prog_name}: {start_time}")
        logger.debug(f"Prompt for add global check constraints: {len(prompt)} characters.")
        try:
            response = query(prompt)
        except Exception as e:
            logger.error(f"Failed to query for global check constraints: {e}")
            response = "{}"
            logger.error(f"Using empty response for global check constraints.")
        logger.info(f"add_global_check_constraints response: {response}")
        response_json = json.loads(scrutinize_json(response))
        end_time = time.time()
        append_log(self.log_path, f"Finished adding global check constraints in {self.repo_path} for program {self.prog_name}: {end_time}, took {end_time - start_time:.2f} seconds")
        self.save_json(response_json, add_global_check_constraints_result_path)