import os
import json
import string
from custom_logger import logger
from evaluator import evaluate
from utils import to_json_str, str_to_json, save_json, append_log, scrutinize_constraint_with_llm, store_llm_result, save_special_arg, parse_to_set_sequence_and_constraint_format
from renamer import Renamer
import z3
import itertools
import time

class OptionInfoAnalyzer:
    def __init__(self, repo_name, prog_name, option_info_filename=None, output_dir=None, log_path=None, default_values_path=None, check_constraints_path=None, check_global_constraints_path=None):
        ### variables
        self.repo_name = repo_name
        self.prog_name = prog_name
        self.output_dir = output_dir
        self.log_path = log_path
        if option_info_filename is None:
            self.option_info_path = os.path.join(self.output_dir, "TODO:")
        else:
            self.option_info_path = os.path.join(self.output_dir, option_info_filename)
        if not os.path.exists(self.option_info_path):
            logger.warning(f"Option info file does not exist")
            assert False
        # load option info
        self.renamer = Renamer()
        with open(self.option_info_path, "r", encoding='utf-8') as f:
            self.option_info = json.load(f)
        self.ignored_options = {}
        self.option_info_format_check_and_rename()
        self.default_values_path = default_values_path
        self.default_values = None
        self.check_constraints_path = check_constraints_path
        self.check_constraints = None
        if self.check_constraints_path is not None and os.path.exists(self.check_constraints_path):
            with open(self.check_constraints_path, "r", encoding='utf-8') as f:
                self.check_constraints = json.load(f)
        self.check_global_constraints_path = check_global_constraints_path
        self.check_global_constraints = None
        if self.check_global_constraints_path is not None and os.path.exists(self.check_global_constraints_path):
            with open(self.check_global_constraints_path, "r", encoding='utf-8') as f:
                self.check_global_constraints = json.load(f)
        self.check_constraints_format_check_and_rename()
        self.check_global_constraints_format_check_and_rename()
        self.z3_vars = {
            "Not": z3.Not,
            "And": z3.And,
            "Or": z3.Or,
            "__OPTVAL__": z3.String("__OPTVAL__"),
            "StrToInt": z3.StrToInt,
            "Length": z3.Length,
        }

    ### Format check
    def option_info_format_check_and_rename(self):
        assert self.option_info is not None, "Option info is None"
        # check if option_info is a dict
        assert type(self.option_info) == dict, f"Option info should be a dict, but got {type(self.option_info)}"
        for option in self.option_info:
            info = self.option_info[option]
            set_sequence, constraints = parse_to_set_sequence_and_constraint_format(info)
            # check if set_sequence and constraints have the same length
            # assert len(set_sequence) == len(constraints), f"Option {option} set_sequence and constraints should have the same length: {len(set_sequence)} != {len(constraints)}, set_sequence: {set_sequence}, constraints: {constraints}"
            if len(set_sequence) != len(constraints):
                logger.warning(f"Option {option} set_sequence and constraints should have the same length: {len(set_sequence)} != {len(constraints)}, set_sequence: {set_sequence}, constraints: {constraints}")
                assert False
            # check if set_sequence is a list of strings
            assert type(set_sequence) == list, f"Option {option} set_sequence should be a list, but got {type(set_sequence)}"
            for i, item in enumerate(set_sequence):
                assert type(item) == str, f"Option {option} set_sequence item should be a string, but got {type(item)}"
                set_sequence[i] = self.renamer.scrutinize_field(item)
                self.option_info[option][i][0] = self.renamer.scrutinize_field(item)
            # check if constraints is a list of lists
            assert type(constraints) == list, f"Option {option} constraints should be a list, but got {type(constraints)}"
            for i, constraint in enumerate(constraints):
                if type(constraint) == str:
                    constraints[i] = [constraint]
                    constraint = constraints[i]
                assert type(constraint) == list, f"constraint should be a list, but got {type(constraint)}, constraint: {constraint}"
                for j, item in enumerate(constraint):
                    constraint[j] = self.renamer.scrutinize_field(item)
                    self.option_info[option][i][1][j] = self.renamer.scrutinize_field(item)
    
    def check_constraints_format_check_and_rename(self):
        if self.check_constraints is None:
            return
        for option, constraints in self.check_constraints.items():
            # rename
            for j, constraint in enumerate(constraints):
                assert type(constraint) == str, f"constraint should be a string, but got {type(constraint)}, constraint: {constraint}"
                constraints[j] = self.renamer.scrutinize_field(constraint)

    def check_global_constraints_format_check_and_rename(self):
        if self.check_global_constraints is None:
            return
        for i, constraint in enumerate(self.check_global_constraints):
            # print(i, constraint)
            self.check_global_constraints[i] = self.renamer.scrutinize_field(constraint)

    def condition_json_str_check(self, json_str):
        s = z3.Solver()
        try:
            js_list = str_to_json(json_str)
        except Exception as e:
            logger.error(f"Error in str_to_json: {json_str}, error: {e}")
            assert False
        assert type(js_list) == list, f"condition json string should be parsed to a list, but got {type(js_list)}"
        condition_str = '[' + ', '.join(js_list) + ']'
        s.add(eval(condition_str, self.z3_vars))
        assert s.check() == z3.sat, f"condition {json_str} is not sat"

    def construct_expr_from_str(self, str_expr: str):
        splitted = str_expr.split(" ")
        if len(splitted) == 1:
            value_str = splitted[0]
            return value_str
        # assert len(splitted) == 3, f"expression should be in the form of var_name op value, but got {str_expr}"
        operand_1 = splitted[0]
        operator = splitted[1]
        operand_2 = " ".join(splitted[2:])
        def scrutinize_operand_2(operand):
            # remove matching parentheses
            if operand.startswith("(") and operand.endswith(")"):
                logger.debug(f"Removing parentheses from operand: {operand}")
                return operand[1:-1].strip()
            return operand
        operand_2 = scrutinize_operand_2(operand_2)
        expr_1 = self.construct_expr_from_str(operand_1)
        expr_2 = self.construct_expr_from_str(operand_2)
        if operator == "+":
            return ("+", expr_1, expr_2)
        elif operator == "-":
            return ("-", expr_1, expr_2)
        elif operator == "*":
            return ("*", expr_1, expr_2)
        elif operator == "/":
            return ("/", expr_1, expr_2)
        elif operator == "&":
            return ("&", expr_1, expr_2)
        elif operator == "|":
            return ("|", expr_1, expr_2)
        elif operator == "^":
            return ("^", expr_1, expr_2)
        # <<
        elif operator == "<<":
            return ("*", expr_1, ("^", "2", expr_2))
        else:
            logger.error(f"invalid operator in {str_expr}: {operator}")
            assert False

    def merge_set_sequence(self, set_sequence) -> list:
        # generate expressions (maybe with ${DEFAULT})
        var_value_map = {}
        for operation in set_sequence:
            if operation.endswith("++"):
                # var_name++
                var_name = operation[:-2].strip()
                var_name = self.renamer.scrutinize_var_name(var_name)
                if var_name not in var_value_map:
                    # var_value_map[var_name] = "${DEFAULT}_(" + var_name + ")"
                    var_value_map[var_name] = var_name
                var_value_map[var_name] = ("+", var_value_map[var_name], "1")
                continue
            if operation.endswith("--"):
                # var_name--
                var_name = operation[:-2].strip()
                var_name = self.renamer.scrutinize_var_name(var_name)
                if var_name not in var_value_map:
                    # var_value_map[var_name] = "${DEFAULT}_(" + var_name + ")"
                    var_value_map[var_name] = var_name
                var_value_map[var_name] = ("-", var_value_map[var_name], "1")
                continue
            # var_name assign_op val
            split = operation.split(" ")
            assert len(split) >= 3, f"operation should be in the form of var_name assign_op val, but got {operation}"
            var_name = split[0]
            var_name = self.renamer.scrutinize_var_name(var_name)
            assign_op = split[1]
            value_str = " ".join(split[2:])
            def scrutinize_value_str(value_str):
                # remove matching parentheses
                if value_str.startswith("(") and value_str.endswith(")"):
                    logger.debug(f"Removing parentheses from value: {value_str}")
                    return value_str[1:-1].strip()
                return value_str
            value_str = scrutinize_value_str(value_str)
            value_expr = self.construct_expr_from_str(value_str)
            if var_name not in var_value_map:
                # var_value_map[var_name] = "${DEFAULT}_(" + var_name + ")"
                var_value_map[var_name] = var_name
            if assign_op == "=":
                var_value_map[var_name] = value_expr
            elif assign_op == "+=":
                var_value_map[var_name] = ("+", var_value_map[var_name], value_expr)
            elif assign_op == "-=":
                var_value_map[var_name] = ("-", var_value_map[var_name], value_expr)
            elif assign_op == "*=":
                var_value_map[var_name] = ("*", var_value_map[var_name], value_expr)
            elif assign_op == "/=":
                var_value_map[var_name] = ("/", var_value_map[var_name], value_expr)
            elif assign_op == "&=":
                var_value_map[var_name] = ("&", var_value_map[var_name], value_expr)
            elif assign_op == "|=":
                var_value_map[var_name] = ("|", var_value_map[var_name], value_expr)
            elif assign_op == "^=":
                var_value_map[var_name] = ("^", var_value_map[var_name], value_expr)
            else:
                assert False, f"invalid operation: {assign_op}"
        result = []
        for var_name, value_expr in var_value_map.items():
            is_const, value = evaluate(value_expr, self.default_values, self.renamer)
            # adjust value: if value is "True" and type of var_name is "int", set value to 1
            if is_const:
                if value == "True" and self.default_values[var_name]["type"] in ["int"]:
                    value = 1
                elif value == "False" and self.default_values[var_name]["type"] in ["int"]:
                    value = 0
            descrutinized_var_name = self.renamer.descrutinize_var_name(var_name)
            descrutinized_var_name = self.renamer.get_last_field(descrutinized_var_name)
            assert descrutinized_var_name in self.default_values, f"var {var_name} not in default_values"
            var_type = self.default_values[descrutinized_var_name]["type"]
            if var_type in ["char *", "const char *", "char*", "const char*"]:
                value = "\"" + str(value) + "\""
            elif var_type == "char":
                value = "\'" + str(value) + "\'"
            result.append(f"{var_name} = {value}")
        return result

    ### Default values
    def extract_var_name_from_setting(self, setting):
        # var_name op value
        splitted = setting.split(" ")
        if len(splitted) == 1:
            if setting.endswith("++") or setting.endswith("--"):
                var = setting[:-2]
                return var
            else:
                logger.error(f"extract_var_name_from_setting failed: {setting}")
                assert False
        elif len(splitted) == 3:
            var_name = splitted[0]
            op = splitted[1]
            value = splitted[2]
            return var_name
        elif len(splitted) > 3:
            ops = ["=", "+=", "-=", "*=", "/=", "&=", "|=", "^="]
            var_name = splitted[0]
            op = splitted[1]
            value = " ".join(splitted[2:])
            if op in ops:
                return var_name
            else:
                logger.error(f"extract_var_name_from_setting failed: {setting}")
                assert False
        else:
            logger.error(f"extract_var_name_from_setting failed: {setting}")
            assert False

    def scrutinize_prompt(self, prompt) -> str:
        return prompt.split("<EOF>")[0]

    def _parse_var_value(self, var_type, var_value):
        type_map = {
            'char': (8, True),
            'signed char': (8, True),
            'unsigned char': (8, False),
            'short': (16, True),
            'signed short': (16, True),
            'unsigned short': (16, False),
            'int': (32, True),
            'signed int': (32, True),
            'signed': (32, True),
            'unsigned int': (32, False),
            'unsigned': (32, False),
            'long': (32, True),
            'signed long': (32, True),
            'unsigned long': (32, False),
            'long long': (64, True),
            'signed long long': (64, True),
            'unsigned long long': (64, False)
        }

        normalized_type = ' '.join(var_type.split()).lower()

        if normalized_type in type_map:
            bits, signed = type_map[normalized_type]
        else:
            # raise ValueError(f"Unsupported data type: {var_type}")
            return var_value

        try:
            if isinstance(var_value, str):
                var_value = var_value.strip().lower()
                if var_value.startswith('0x'):
                    int_value = int(var_value, 16)
                elif var_value.startswith('0b'):
                    int_value = int(var_value, 2)
                else:
                    int_value = int(var_value)
            else:
                int_value = int(var_value)
        except (ValueError, TypeError) as e:
            raise ValueError(f"Invalid var_value: {var_value}") from e

        max_val = 1 << bits
        mask = max_val - 1

        truncated = int_value & mask

        if signed and truncated >= (1 << (bits - 1)):
            return truncated - max_val
        else:
            return truncated

    def prepare_default_values(self):
        if self.default_values is None:
            assert os.path.exists(self.default_values_path), f"Default values file does not exist"
            # load default values
            if self.default_values_path.endswith("TODO:"):
                with open(self.default_values_path, "r", encoding='utf-8') as f:
                    self.default_values = json.load(f)
            elif self.default_values_path.endswith("TODO:"):
                # load from text file
                with open(self.default_values_path, "r", encoding='utf-8') as f:
                    content = f.read()
                    self.default_values = {}
                    for line in content.splitlines():
                        if not line.strip():
                            continue
                        assert line.count('(') == 1 and line.count(')') == 1, f'Error: {line} is not a valid line.'
                        assert len(line.split()) >= 3, f'Error: {line} is not a valid line.'
                        var_name = line.split('(')[0].strip()
                        var_type = line.split('(')[1].split(')')[0].strip()
                        var_value = line.split(')')[1].strip().split()[0]
                        self.default_values[var_name] = {"type": var_type, "value": self._parse_var_value(var_type, var_value)}
            # scrutinize and prepare z3 variables
        assert self.default_values is not None, "Default values is None"
        return

    def prepare_z3_vars(self):
        for var_name, info in self.default_values.items():
            # scrutinize var_name
            scrutinized_var_name = self.renamer.scrutinize_var_name(var_name)
            self.renamer.add_rename(scrutinized_var_name, var_name)
            # prepare z3 variables
            var_type = info["type"]
            # EXTENSION
            if var_type in ["int", "unsigned int"]:
                self.z3_vars[scrutinized_var_name] = z3.Int(scrutinized_var_name)
            elif var_type in ["long int", "long"]:
                self.z3_vars[scrutinized_var_name] = z3.Int(scrutinized_var_name + "_Int64")
            elif var_type == "bool":
                self.z3_vars[scrutinized_var_name] = z3.Bool(scrutinized_var_name)
            elif var_type == "char *" or var_type == "const char *" or var_type == "char*":
                self.z3_vars[scrutinized_var_name] = z3.String(scrutinized_var_name)
            elif var_type == "char":
                self.z3_vars[scrutinized_var_name] = z3.String(scrutinized_var_name)
            else:
                logger.error(f"Unsupported var {var_name} type: {var_type}")
                # assert False
        logger.info(f"z3 vars: {self.z3_vars.keys()}")

    ### Analyze
    def replace_special_tokens(self, scrutinized_constraint: str):
        scrutinized_constraint = scrutinized_constraint.replace("\'\\0\'", "\"\"")
        scrutinized_constraint = scrutinized_constraint.replace("\"\\0\"", "\"\"")
        return scrutinized_constraint

    def str_list_to_z3_constraint(self, str_list):
        # convert string list to z3 expressions
        full_constraint = z3.BoolVal(True)
        for constraint in str_list:
            # convert string to z3 expression
            scrutinized_constraint = self.renamer.scrutinize_str(constraint)
            scrutinized_constraint = scrutinized_constraint.replace("${OPTVAL}", "__OPTVAL__")
            scrutinized_constraint = scrutinized_constraint.replace("${OPTVAL_INT}", "StrToInt(__OPTVAL__)")
            # strlen
            scrutinized_constraint = scrutinized_constraint.replace("strlen(__OPTVAL__)", "Length(__OPTVAL__)")
            # strdup
            scrutinized_constraint = self.replace_special_tokens(scrutinized_constraint)
            scrutinized_constraint = self.renamer.scrutinize_field(scrutinized_constraint)
            if "formatted as" in scrutinized_constraint:
                save_special_arg(scrutinized_constraint, self.output_dir)
                continue
            try:
                if " in " in scrutinized_constraint:
                    raise Exception("Special case: in")
                if scrutinized_constraint.startswith("not"):
                    scrutinized_constraint = "Not" + scrutinized_constraint[3:]
                expr = eval(scrutinized_constraint, self.z3_vars)
            except Exception as e:
                logger.error(f"Error in eval: {scrutinized_constraint}, error: {e}")
                # if error message contains "is not defined"
                if "is not defined" in str(e):
                    raise e
                new_scrutinized_constraint = scrutinize_constraint_with_llm(scrutinized_constraint, self.output_dir, self.default_values)
                logger.info("LLM scrutinized constraint: " + new_scrutinized_constraint)
                try:
                    expr = eval(new_scrutinized_constraint, self.z3_vars)
                except Exception as e:
                    logger.error(f"Error in eval after llm scrutiny: {new_scrutinized_constraint}, error: {e}")
                    # logger.error(f"z3 vars: {self.z3_vars}")
                    assert False
                    raise e
                store_llm_result(scrutinized_constraint, new_scrutinized_constraint, self.output_dir)
                assert type(expr) == z3.BoolRef, f"Expression should be a z3 BoolRef, but got {type(expr)}"
            full_constraint = z3.And(full_constraint, expr)
        # simplify full_constraint
        full_constraint = z3.simplify(full_constraint)
        return full_constraint

    def divide_solution_space(self, constraints: list, complex_constraint_indices: list, set_sequence: list):
        # return a list of 0-1 sequences, and each sequence represents the selection of complex constraints
        # return the constraint json string for each selection
        # return the set_sequence for each selection
        assert len(constraints) == len(set_sequence), f"constraints and set_sequence should have the same length: {len(constraints)} != {len(set_sequence)}"
        assert len(complex_constraint_indices) <= 10, "complex_z3_constraints should have at most 10 elements"
        selections = []
        condition_js_str_list = []
        operations_list = []
        for selection in itertools.product([True, False], repeat=len(complex_constraint_indices)):
            s = z3.Solver()
            # add constraints to the solver
            for i in range(len(selection)):
                if selection[i]:
                    s.add(constraints[complex_constraint_indices[i]])
                else:
                    s.add(z3.Not(constraints[complex_constraint_indices[i]]))
            if s.check() == z3.sat:
                selections.append(selection)
                assertion_js_str_list = []
                for _assersion in s.assertions():
                    simplified_assersion = z3.simplify(_assersion)
                    assertion_js_str_list.append(str(simplified_assersion))
                assertion_js_str = to_json_str(assertion_js_str_list)
                condition_js_str_list.append(assertion_js_str)
                # get the operations for this selection
                operations = []
                for i, set_step in enumerate(set_sequence):
                    if s.check(constraints[i]) == z3.sat:
                        operations.append(set_step)
                operations_list.append(operations)
        assert len(selections) == len(condition_js_str_list), f"selections and condition_js_str_list should have the same length: {len(selections)} != {len(condition_js_str_list)}"
        assert len(selections) == len(operations_list), f"selections and operations_list should have the same length: {len(selections)} != {len(operations_list)}"
        return selections, condition_js_str_list, operations_list

    def analyze(self):
        start_time = time.time()
        append_log(self.log_path, f"Start analyzing sequence constraints for {self.prog_name} in {self.repo_name}")
        self.prepare_default_values()
        self.prepare_z3_vars()
        # analyze constraints
        option_to_var_value_setting = {}
        for option, info in self.option_info.items():
            logger.info(f"Analyzing option: {option}")
            if option in self.ignored_options:
                logger.warning(f"Ignore option {option}: {self.ignored_options[option]}")
                continue
            if option not in option_to_var_value_setting:
                option_to_var_value_setting[option] = []
            set_sequence, constraints = parse_to_set_sequence_and_constraint_format(info)
            set_sequence = [self.replace_special_tokens(s) for s in set_sequence]
            logger.debug(f"Option: {option}, Set sequence: {set_sequence}, Constraints: {constraints}")
            # parse constraints
            all_z3_constraints = []
            complex_constraint_indices = []
            skip_flag = False
            for i, constraints_per_step in enumerate(constraints):
                try:
                    full_constraint = self.str_list_to_z3_constraint(constraints_per_step)
                except Exception as e:
                    skip_flag = True
                    logger.warning(f"Error in str_list_to_z3_constraint, set skip_flag to True. Option {option}, Step {i}, Error message {e}")
                    break
                logger.info(f"Option: {option}, Step: {i}, Constraint: {full_constraint}")
                all_z3_constraints.append(full_constraint)
                if len(constraints_per_step) > 0:
                    complex_constraint_indices.append(i)
            if skip_flag:
                logger.warning(f"Skip option {option} due to error in constraints parsing")
                continue
            # divide the solution space
            divisions, condition_js_str_list, operations_list = self.divide_solution_space(all_z3_constraints, complex_constraint_indices, set_sequence)
            # merge operations
            merged_operations_list = []
            for operations in operations_list:
                merged_operations = self.merge_set_sequence(operations)
                merged_operations_list.append(merged_operations)
            for merged_operations in merged_operations_list:
                print(merged_operations)
            assert len(operations_list) == len(merged_operations_list), f"operations_list and merged_operations_list should have the same length: {len(operations_list)} != {len(merged_operations_list)}"
            # store the results
            for condition_js_str, merged_operations in zip(condition_js_str_list, merged_operations_list):
                self.condition_json_str_check(condition_js_str)
                descrutinized_condition_str = self.renamer.descrutinize_str(condition_js_str)
                # merged_operations_str = str(merged_operations)
                merged_operations_str = to_json_str(merged_operations)
                option_to_var_value_setting[option].append((descrutinized_condition_str, merged_operations_str))
        logger.info(f"Result: {option_to_var_value_setting}")
        # save result
        save_path = os.path.join(self.output_dir, "TODO:")
        save_json(option_to_var_value_setting, save_path)
        logger.info(f"Saved result to {save_path}")
        # save z3 variables
        save_path = os.path.join(self.output_dir, "TODO:")
        z3_vars_content = {}
        for var_name in self.z3_vars:
            ignore_list = ["__builtins__"]
            if var_name in ignore_list:
                continue
            var_value = self.z3_vars[var_name]
            # if var_value is a function, get the name of the function
            if callable(var_value):
                module_name = var_value.__module__
                function_name = var_value.__name__
                var_value = f"{module_name}.{function_name}"
            # if var_value is a z3.Int, get the name of the variable
            elif isinstance(var_value, z3.ExprRef) and var_value.sort() == z3.IntSort():
                # EXTENSION
                if str(var_value).endswith("_Int64"):
                    var_value = f"Int64 : {str(var_value)[:-6]}"
                else:
                    var_value = f"Int : {str(var_value)}"
            # if var_value is a z3.String, get the name of the variable
            elif isinstance(var_value, z3.ExprRef) and var_value.sort() == z3.StringSort():
                var_value = f"String : {str(var_value)}"
            # if var_value is a z3.Bool, get the name of the variable
            elif isinstance(var_value, z3.ExprRef) and var_value.sort() == z3.BoolSort():
                var_value = f"Bool : {str(var_value)}"
            else:
                # var_value = str(var_value)
                assert False, f"Unsupported z3 variable type: {type(var_value)}, var_value: {var_value}"
            z3_vars_content[var_name] = var_value
        save_json(z3_vars_content, save_path)
        logger.info(f"Saved z3 vars to {save_path}")
        end_time = time.time()
        append_log(self.log_path, f"Finished analyzing sequence constraints for {self.prog_name} in {self.repo_name}, time taken: {end_time - start_time:.2f} seconds")
    
    def process_check_constraints(self):
        # process self.check_constraints to make it a legal z3 format
        if self.check_constraints is None:
            logger.warning(f"No check constraints to process")
            return
        z3_vars_path = os.path.join(self.output_dir, "TODO:")
        assert os.path.exists(z3_vars_path), f"file does not exist, please run analyze() first."
        # self.z3_vars = _load_z3_vars(z3_vars_path)
        self.prepare_default_values()
        self.prepare_z3_vars()
        processed_constraints = {}
        for option, constraints in self.check_constraints.items():
            try:
                z3_constraint = self.str_list_to_z3_constraint(constraints)
            except Exception as e:
                logger.warning(f"Error in str_list_to_z3_constraint, skip this check constraint. Constraints: {constraints}, Error message {e}")
                continue
            z3_constraint_json_str = to_json_str(str(z3_constraint))
            processed_constraints[option] = z3_constraint_json_str
            logger.info(f"Option: {option}, Check constraint: {z3_constraint_json_str}, constraints: {constraints}")
        # save result
        save_path = os.path.join(self.output_dir, "TODO:")
        save_json(processed_constraints, save_path)
    
    def process_check_global_constraints(self):
        # process self.check_global_constraints to make it a legal z3 format
        if self.check_global_constraints is None:
            logger.warning(f"No check global constraints to process")
            return
        z3_vars_path = os.path.join(self.output_dir, "TODO:")
        assert os.path.exists(z3_vars_path), f"file does not exist, please run analyze() first."
        self.prepare_default_values()
        self.prepare_z3_vars()
        processed_constraints = []
        # for constraint in self.check_global_constraints:
        z3_constraint = ""
        try:
            z3_constraint = self.str_list_to_z3_constraint(self.check_global_constraints)
        except Exception as e:
            logger.warning(f"Error in str_list_to_z3_constraint, skipping. Constraint: {self.check_global_constraints}, Error message {e}")
        z3_constraint_json_str = to_json_str(str(z3_constraint))
        processed_constraints.append(z3_constraint_json_str)
        logger.info(f"Check constraint: {z3_constraint_json_str}, constraint: {self.check_global_constraints}")
        # save result
        save_path = os.path.join(self.output_dir, "TODO:")
        save_json(processed_constraints, save_path)