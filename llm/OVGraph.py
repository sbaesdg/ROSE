import json
import random
import z3
import copy
import os
import re
import time
from datetime import datetime
from custom_logger import logger
from OVGraph_utils import load_json, str_to_json, expr_ast_to_z3

class OptionNode:
    def __init__(self, name, type=None, default=None):
        self.name = name
        self.type = type
        self.default = default

    def __str__(self):
        return f'({self.name} {self.type} {self.default})'

    def __repr__(self):
        return self.__str__()

class VarNode:
    def __init__(self, name, type=None, default=None):
        self.name = name
        self.type = type
        self.default = default

    def __str__(self):
        return f'({self.name} {self.type} {self.default})'

    def __repr__(self):
        return self.__str__()

class SetEdge:
    def __init__(self, option, var, condition, value):
        self.optionNode = option
        self.varNode = var
        self.condition = condition
        self.value = value

    def __str__(self):
        if isinstance(self.condition, list) and len(self.condition) > 0:
            assert isinstance(self.condition[0], z3.z3.BoolRef), f'condition[0] = {self.condition[0]}, type = {type(self.condition[0])}'
            suffix = str(type(self.condition[0]))
        else:
            suffix = ""
        return f'({self.optionNode} {self.varNode} {self.condition}({suffix}) {self.value})'
    def __repr__(self):
        return self.__str__()

class OVGraph:
    def __init__(self, var_value_setting_path=None, z3_vars_path=None, default_value_path=None, check_constraints_path=None, check_global_constraints_path=None, program=None):
        # _optionNodes: {optionName: OptionNode}
        self._optionNodes = {}
        # _varNodes: {varName: VarNode}
        self._varNodes = {}
        # _setEdges: [SetEdge]
        self._setEdges = []
        # _inEdges: {varname: [SetEdge]}
        self._inEdges = {}
        # _outEdges: {optionName: [SetEdge]}
        self._outEdges = {}
        # _varToCondEdges: {varName: [SetEdge]}
        self._varToCondEdges = {}

        # _varInfo: {varname: {"type": ..., "value": ...}}
        self._varInfo = {}
        # _optionInfo: {optionName: {"type": ..., "has_optval": ...}}
        self._optionInfo = {}

        self._initialState = {}
        self._visited_seqs = set()
        self._visited_seqs_with_timestamp = {}
        self._visited_seqs_with_timestamp["__START_TIME__"] = time.time()
        self._visited_seqs_bv = set()

        # misc
        self.MAX_LEVEL = 1
        self.program = program
        # extra overhead log time
        self.server_init_time = datetime.now().strftime("%Y%m%d%H%M%S")

        # z3_vars: {varname: Z3Expression, "Not": z3.Not, ...}
        self.z3_vars = {}
        self.name_mapping = None
        self.all_options = None
        self.bv_map = None
        self.bv_len = None
        self.check_constraints = {}
        self.check_global_constraints = []
        self.load_z3_vars(z3_vars_path)
        self.load_default_values(default_value_path)
        self.load_check_constraints(check_constraints_path)
        self.load_check_global_constraints(check_global_constraints_path)
        self.load_var_value_setting(var_value_setting_path)

        self.check_value_interested(os.path.dirname(var_value_setting_path))

    def __str__(self):
        # return f'optionNodes: {self._optionNodes}\nvarNodes: {self._varNodes}\nsetEdges: {self._setEdges}'
        optionNodesStr = "optionNodes: {\n"
        for option in self._optionNodes:
            optionNodesStr += f'{option}: {self._optionNodes[option]}\n'
        optionNodesStr += "}\n"
        varNodesStr = "varNodes: {\n"
        for var in self._varNodes:
            varNodesStr += f'{var}: {self._varNodes[var]}\n'
        varNodesStr += "}\n"
        setEdgesStr = "setEdges: [\n"
        for edge in self._setEdges:
            setEdgesStr += f'{edge}\n'
        setEdgesStr += "]\n"
        optionInfosStr = "optionInfo: {\n"
        for option, info in self._optionInfo.items():
            optionInfosStr += f'{option}: {info}\n'
        optionInfosStr += "}\n"
        return optionNodesStr + varNodesStr + setEdgesStr + optionInfosStr

    def __repr__(self):
        return self.__str__()

    def z3_condition_eval(self, option, var, condition, value):
        if condition == "true":
            condition = []
        z3_constraints = []
        pruned_option = option.replace("-", "_")
        z3_var_name = f'__OPTVAL__{pruned_option}__'
        z3_select_var_name = f'__SELECT__{pruned_option}__'
        for c_str in condition:
            print(f'c_str: {c_str}')
            # rename
            c_str = c_str.replace("->", "__TO__")
            # create variable for __OPTVAL__: z3.String('__OPTVAL__{OPTION}__')
            c_str = c_str.replace("__OPTVAL__", z3_var_name)
            if "OPTVAL" in c_str:
                if option not in self._optionInfo:
                    self._optionInfo[option] = {"type": None, "has_optval": False}
                self._optionInfo[option]["has_optval"] = True
            if z3_var_name not in self.z3_vars:
                self.z3_vars[z3_var_name] = z3.String(z3_var_name)
                self.z3_vars[z3_select_var_name] = z3.Bool(z3_select_var_name)
            # special cases that eval cannot handle
            if c_str == "True" or c_str == "true":
                z3_constraint = z3.BoolVal(True)
            elif c_str == "False" or c_str == "false":
                z3_constraint = z3.BoolVal(False)
            else:
                try:
                    z3_constraint = eval(c_str, self.z3_vars)
                except Exception as e:
                    logger.error(f'condition: {c_str}')
                    logger.error(f'z3 condition eval error: {e}')
                    assert False, f'condition: {c_str}, z3_vars: {self.z3_vars}'
            z3_constraints.append(z3_constraint)
        # check value to create __OPTVAL__ and __SELECT__
        if value and "OPTVAL" in value:
            if option not in self._optionInfo:
                self._optionInfo[option] = {"type": None, "has_optval": False}
            self._optionInfo[option]["has_optval"] = True
        if z3_var_name not in self.z3_vars:
            self.z3_vars[z3_var_name] = z3.String(z3_var_name)
            self.z3_vars[z3_select_var_name] = z3.Bool(z3_select_var_name)
        return z3_constraints

    def add_edge(self, option, var, condition, value: str):
        condition = self.condition_format_check(condition)
        if condition is None:
            logger.error(f'condition format check failed: {condition}')
            assert False
        if option not in self._optionNodes:
            self._optionNodes[option] = OptionNode(option)
        if var not in self._varNodes:
            self._varNodes[var] = VarNode(var)
            self._initialState[var] = None
        optionNode = self._optionNodes[option]
        varNode = self._varNodes[var]
        z3_condition = self.z3_condition_eval(option, var, condition, value)
        # format value
        pruned_option = option.replace("-", "_")
        value = value.replace("${OPTVAL}", f'__OPTVAL__{pruned_option}__')
        value = value.replace("${OPTVAL_INT}", f'z3.StrToInt(__OPTVAL__{pruned_option}__)')
        edge = SetEdge(optionNode, varNode, z3_condition, value)
        # edge = SetEdge(optionNode, varNode, condition, value)
        self._setEdges.append(edge)
        if var not in self._inEdges:
            self._inEdges[var] = []
        if option not in self._outEdges:
            self._outEdges[option] = []
        self._inEdges[var].append(edge)
        self._outEdges[option].append(edge)
        related_vars = self.get_related_vars(condition)
        for related_var in related_vars:
            if related_var not in self._varToCondEdges:
                self._varToCondEdges[related_var] = []
            self._varToCondEdges[related_var].append(edge)

    def get_related_vars(self, condition):
        # example: "condition": [["$OPTARG", "==", "always"]],
        related_vars = set()
        if condition == "true":
            return related_vars
        return related_vars

    def condition_format_check(self, cond):
        # example: "condition": [["$OPTARG", "==", "always"]]
        if cond == "true" or cond == []:
            return "true"
        assert type(cond) == list, f'type(cond) = {type(cond)}'
        assert len(cond) > 0, f'len(cond) = {len(cond)}, cond = {cond}'
        formatted_cond = []
        for c in cond:
            assert type(c) == str, f'type(c) = {type(c)}'
            formatted_cond.append(c)
            continue
        return formatted_cond

    def setVarTable(self, varTable):
        self._varInfo = varTable

    def getIndegree(self, varName):
        assert varName in self._inEdges, f'varName {varName} not in _inEdges'
        return len(self._inEdges[varName])

    def getAdjacentEdgesForVarName(self, varName):
        if varName not in self._inEdges:
            logger.error(f'varName {varName} not in _inEdges, return empty list')
            return []
        assert varName in self._inEdges, f'varName {varName} not in _inEdges'
        return self._inEdges[varName]

    def getAdjacentEdgesForOptionName(self, optionName):
        assert optionName in self._outEdges, f'optionName {optionName} not in _outEdges'
        return self._outEdges[optionName]

    def generateSequences(self):
        assert False, 'Not implemented'

    def printNode(self, name, isOption):
        if isOption:
            print(self._optionNodes[name])
            # print adjacent edges
            for edge in self.getAdjacentEdgesForOptionName(name):
                print(edge)
        else:
            print(self._varNodes[name])
            # print adjacent edges
            for edge in self.getAdjacentEdgesForVarName(name):
                print(edge)

    def get_dependent_options(self, condition):
        if condition == "true":
            return []
        condition_related_vars = self.get_related_vars(condition)
        assert len(condition_related_vars) == 1, f'len(condition_related_vars) = {len(condition_related_vars)}'
        condition_related_var = condition_related_vars.pop()
        if condition_related_var == "$OPTARG":
            return []
        else:
            adjacent_in_edges = self.getAdjacentEdgesForVarName(condition_related_var)
            for in_edge in adjacent_in_edges:
                if in_edge.condition != "true":
                    continue
                value = in_edge.value
                assignment = {}
                assignment[condition_related_var] = value
                if self.isSAT(condition, assignment):
                    return [self.instantiate(in_edge.optionNode.name)]

    def get_options_depend_on(self, option, option_values=None):
        if option_values is not None:
            assert type(option_values) == list, f'type(option_values) = {type(option_values)}'
            assert len(option_values) == 1, f'len(option_values) = {len(option_values)}'
        # return the options that depend on the given option
        dependent_options = []
        adjacent_out_edges = self.getAdjacentEdgesForOptionName(option)
        for edge in adjacent_out_edges:
            if edge.condition != "true":
                continue
            var = edge.varNode.name
            val = edge.value
            if var not in self._varToCondEdges:
                continue
            related_cond_edges = self._varToCondEdges[var]
            assert len(related_cond_edges) > 0, f'len(related_cond_edges) = {len(related_cond_edges)}'
            for cond_edge in related_cond_edges:
                assert cond_edge.condition != "true", f'cond_edge.condition = {cond_edge.condition}'
                cond_related_vars = self.get_related_vars(cond_edge.condition)
                if len(cond_related_vars) != 1:
                    continue
                cond_related_var = cond_related_vars.pop()
                assert cond_related_var == var, f'cond_related_var = {cond_related_var}'
                assignment = {}
                assignment[var] = val
                if self.isSAT(cond_edge.condition, assignment):
                    dependent_options.append(cond_edge.optionNode.name)
        return dependent_options

    def get_conflicting_options(self, option):
        conflicting_options = []
        adjacent_out_edges = self.getAdjacentEdgesForOptionName(option)
        for edge in adjacent_out_edges:
            var = edge.varNode.name
            adjacent_in_edges = self.getAdjacentEdgesForVarName(var)
            for in_edge in adjacent_in_edges:
                if in_edge.optionNode.name != option:
                    conflicting_options.append(in_edge.optionNode.name)
        return conflicting_options

    def instantiate(self, option):
        return [option]

    def check_decls(self, string):
        # (declare-fun XX () (Array (_ BitVec 32) (_ BitVec 8)))
        # make sure all declare-fun have the same type: (Array (_ BitVec 32) (_ BitVec 8))
        count = string.count('(declare-fun')
        if count == 0:
            return False, []
        pattern = r'\(declare-fun (\w+) \(\) \(Array \(_ BitVec 32\) \(_ BitVec 8\)\)\)'
        var_names = re.findall(pattern, string)
        assert len(var_names) == count, "Not all declare-fun have the same type: (Array (_ BitVec 32) (_ BitVec 8)):\n{}".format(string)
        print("All declare-fun have the same type: (Array (_ BitVec 32) (_ BitVec 8))")
        return True, var_names

    def isSAT(self, cond, assignment):
        # assert cond != "true", f'cond = {cond}'
        if cond == "true":
            return True
        for c in cond:
            var, op, val = c
            assert var in assignment, f'var {var} not in assignment'
            # generate a string and evaluate it
            expr = f'{assignment[var]} {op} {val}'
            try:
                result = eval(expr)
                assert type(result) == bool, f'type(result) = {type(result)}'
                if result == False:
                    return False
            except Exception as e:
                logger.error(f'Eval Exception: {e}')
                return False
        return True

    def check(self):
        for var_name in self._varNodes:
            for var_name2 in self._varNodes:
                if var_name != var_name2 and var_name in var_name2:
                    logger.error(f'Error: {var_name} and {var_name2} may be indistinguishable.')
        logger.info(self._varNodes)

    def check_value(self):
        for edge in self._setEdges:
            assert type(edge.value) == str, f'edge.value = {edge.value}, type = {type(edge.value)}'
            # check if value can be converted into a z3 expression
            try:
                z3_expr = self.z3_get_value_expr(edge.value)
            except Exception as e:
                logger.error(f'Error: {edge.value} cannot be evaluated. Exception: {e}')
                assert False, f'Error: {edge.value} cannot be evaluated.'

    def check_value_interested(self, file_dir):
        state_variables_path = "TODO:"
        assert os.path.exists(state_variables_path), f'check_value_interested error: {state_variables_path} not found.'
        with open(state_variables_path, 'r') as f:
            lines = f.readlines()
        # parse lines
        full_klee_variables = []
        for line in lines:
            # use last word as variable name
            var_name = line.strip().split()[-1]
            if var_name in self.z3_vars:
                full_klee_variables.append(var_name)
        for var in full_klee_variables:
            # get adjacent
            try:
                adjacent_edges = self.getAdjacentEdgesForVarName(var)
            except Exception as e:
                logger.error(f'Error: {var} has no adjacent edges.')
                continue
            print(f'Variable: {var}')
            for edge in adjacent_edges:
                print(f'  Edge: {edge}')
                assert type(edge.value) == str, f'edge.value = {edge.value}, type = {type(edge.value)}'
                try:
                    z3_expr = self.z3_get_value_expr(edge.value)
                    print(f'  Z3 Expression: {z3_expr}')
                except Exception as e:
                    logger.error(f'Error: {edge.value} cannot be evaluated. Exception: {e}')
                    print(f'  Error: {edge.value} cannot be evaluated.')
                    assert False, f'Error: {edge.value} cannot be evaluated.'
        logger.info("All interested variables checked successfully.")

    def _parse_operation(self, operation_str):
        splited = operation_str.split(' ')
        assert len(splited) >= 3, "Error: {} is not a valid operation".format(operation_str)
        var = splited[0]
        op = splited[1]
        value = ' '.join(splited[2:])
        return var, op, value

    def load_var_value_setting(self, path):
        # load json file
        js = load_json(path)
        options = list(js.keys())
        self.all_options = options
        logger.info("Options: {}".format(options))
        # add nodes and edges
        for option in options:
            logger.debug("Option: {}".format(option))
            set_cases = js[option]
            for set_case in set_cases:
                assert isinstance(set_case, list), "Error: {} is not a list".format(set_case)
                assert len(set_case) == 2, "Error: {} is not a list of length 2".format(set_case)
                # get condition and operations
                condition_str = set_case[0]
                conditions = str_to_json(condition_str)
                operation_str = set_case[1]
                operations = str_to_json(operation_str)
                logger.debug("Condition({}): {}".format(type(conditions), conditions))
                logger.debug("Operations({}): {}".format(type(operations), operations))
                for opreation in operations:
                    var_name, _, value = self._parse_operation(opreation)
                    # add extra check constraints
                    if option in self.check_constraints:
                        assert isinstance(conditions, list), f'type(conditions) = {type(conditions)}'
                        conditions.append(self.check_constraints[option])
                    self.add_edge(option, var_name, conditions, value)

    def load_check_constraints(self, path):
        if not os.path.exists(path):
            logger.warning(f'Warning: {path} not found. No check constraints loaded.')
            return
        # load json file
        js = load_json(path)
        options = list(js.keys())
        # add nodes and edges
        for option in options:
            logger.debug("Option: {}".format(option))
            if option not in js:
                continue
            logger.debug("js[option]: {}".format(js[option]))
            check_constraints = str_to_json(str(js[option]))
            self.check_constraints[option] = check_constraints

    def load_check_global_constraints(self, path):
        if not os.path.exists(path):
            logger.warning(f'Warning: {path} not found. No check global constraints loaded.')
            return
        # load json file
        js = load_json(path)
        self.check_global_constraints = []
        for constraint in js:
            logger.debug("Global Constraint: {}".format(constraint))
            check_constraint = str_to_json(constraint)
            self.check_global_constraints.append(check_constraint)

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

    def load_default_values(self, path, file_type="txt"):
        # update _varInfo
        if not os.path.exists(path):
            logger.error(f'Error: {path} not found.')
            assert False
        if file_type == "json":
            with open(path, 'r') as f:
                data = json.load(f)
            for var_name in data:
                if var_name not in self._varInfo:
                    self._varInfo[var_name] = {}
                var_type = data[var_name]['type']
                var_value = data[var_name]['value']
                self._varInfo[var_name]['type'] = var_type
                self._varInfo[var_name]['value'] = var_value
        elif file_type == "txt":
            with open(path, 'r') as f:
                lines = f.readlines()
                for line in lines:
                    assert line.count('(') == 1 and line.count(')') == 1, f'Error: {line} is not a valid line.'
                    assert len(line.split()) >= 3, f'Error: {line} is not a valid line.'
                    var_name = line.split('(')[0].strip()
                    var_type = line.split('(')[1].split(')')[0].strip()
                    var_value = line.split(')')[1].strip().split()[0]
                    if var_name not in self._varInfo:
                        self._varInfo[var_name] = {}
                    self._varInfo[var_name]['type'] = var_type
                    self._varInfo[var_name]['value'] = self._parse_var_value(var_type, var_value)
        else:
            assert False, f'Error: {file_type} is not a valid file type.'

    def _get_default_value(self, var_name):
        # get the default value of the var_name
        var_name = var_name.strip().replace("__TO__", "->")
        if var_name in self._varInfo:
            return self._varInfo[var_name]['type'], self._varInfo[var_name]['value']
        else:
            assert False, f'Error: {var_name} not found in _varInfo.'

    def prune_state_variables(self, state_variables_path):
        assert os.path.exists(state_variables_path), f'Error: {state_variables_path} not found.'
        with open(state_variables_path, 'r') as f:
            lines = f.readlines()
        # parse lines
        new_lines = []
        for line in lines:
            # use last word as variable name
            var_name = line.strip().split()[-1]
            if var_name in self.z3_vars:
                new_lines.append(line.strip())
        pruned_state_variables_path = "TODO:"
        with open(pruned_state_variables_path, 'w') as f:
            f.write('\n'.join(new_lines))

    def get_var_type(self, var_name):
        _type, _ = self._get_default_value(var_name)
        return _type

    def z3_get_default_value(self, var_name):
        _type, default_value = self._get_default_value(var_name)
        # EXTENSION
        if _type == "bool":
            if default_value == "0":
                default_value = "False"
            elif default_value == "1":
                default_value = "True"
            else:
                assert False, f'Error: {default_value} is not a valid bool value.'
        return self.z3_get_value_expr(default_value, _type)

    def get_symbolic_vars(self):
        # return [[var_name, field1, field1.field2, ...], ...]
        symbolic_vars = []
        for var_name in self._varNodes:
            seps = ['.', '->']
            splitted = re.split(r'(\.|\->)', var_name)
            res = []
            for element in splitted:
                if element in seps:
                    continue
                element = element.strip()
                if element == "":
                    continue
                res.append(element)
            symbolic_vars.append(res)
        return symbolic_vars

    def load_z3_vars(self, path):
        # update _varInfo
        if not os.path.exists(path):
            logger.error(f'Error: {path} not found.')
            assert False
        with open(path, 'r') as f:
            data = json.load(f)
        special_name = {
            "Not": z3.Not,
            "And": z3.And,
            "Or": z3.Or,
            "StrToInt": z3.StrToInt,
            "Length": z3.Length
        }
        for var_name in data:
            var_data = data[var_name]
            if var_name in special_name:
                # special variable names
                self.z3_vars[var_name] = special_name[var_name]
                continue
            if var_name == "__OPTVAL__":
                # ignore, prepare __OPTVAL__{varname}__ later
                continue
            else:
                assert var_data.count(':') == 1, f'Illegal {{var_name: var_data}}: {{{var_name}: {var_data}}}'
                var_data = var_data.split(':')
                assert len(var_data) == 2, f'Illegal {{var_name: var_data}}: {{{var_name}: {var_data}}}'
                var_type = var_data[0].strip()
                var_name = var_data[1].strip()
                assert var_type in ['Int', 'Int64', 'String', 'Bool'], f'Illegal var_type: {var_type}'
                if var_type == 'Int':
                    # self.z3_vars[var_name] = z3.Int(var_name)
                    self.z3_vars[var_name] = z3.BitVec(var_name, 32)
                elif var_type == 'Int64':
                    self.z3_vars[var_name] = z3.BitVec(var_name, 64)
                elif var_type == 'String':
                    self.z3_vars[var_name] = z3.String(var_name)
                elif var_type == 'Bool':
                    self.z3_vars[var_name] = z3.Bool(var_name)
                    # EXTENSION
                    # self.z3_vars[var_name] = z3.BitVec(var_name, 1)
                else:
                    logger.error(f'Error: {var_type} is not a valid type.')
                    assert False

    def z3_get_all_var_names(self, expr):
        var_names = set()
        if isinstance(expr, list):
            for e in expr:
                var_names.update(self.z3_get_all_var_names(e))
            return var_names
        # traverse the expression tree
        if type(expr) in [bool]:
            return var_names
        children = expr.children()
        if len(children) == 0:
            # leaf node
            if isinstance(expr, z3.ExprRef) and expr.sort() == z3.IntSort():
                int_ignore_names = ['Int']
                name = expr.decl().name()
                if name not in int_ignore_names:
                    var_names.add(name)
            elif isinstance(expr, z3.ExprRef) and expr.sort() in [z3.BitVecSort(64), z3.BitVecSort(56), z3.BitVecSort(48), z3.BitVecSort(40), z3.BitVecSort(32), z3.BitVecSort(24), z3.BitVecSort(16), z3.BitVecSort(8)]:
                bv_ignore_names = ['BitVec', 'bv', 'bv32']
                name = expr.decl().name()
                if name not in bv_ignore_names:
                    var_names.add(name)
            elif isinstance(expr, z3.ExprRef) and expr.sort() == z3.BoolSort():
                bool_ignore_names = ['Bool', 'true', 'false']
                name = expr.decl().name()
                if name not in bool_ignore_names:
                    var_names.add(name)
            elif isinstance(expr, z3.ExprRef) and expr.sort() == z3.StringSort():
                string_ignore_names = ['String']
                name = expr.decl().name()
                if name not in string_ignore_names:
                    var_names.add(name)
            elif isinstance(expr, z3.ExprRef) and expr.sort() == z3.ArraySort(z3.BitVecSort(32), z3.BitVecSort(8)):
                array_ignore_names = ['Array', 'Array32']
                name = expr.decl().name()
                if name not in array_ignore_names:
                    var_names.add(name)
            else:
                logger.error(f'Error: {expr} is not a valid expression, sort: {expr.sort()}.')
                assert False
        else:
            for child in children:
                var_names.update(self.z3_get_all_var_names(child))
        return var_names

    def z3_get_var_in_expr(self, expr, name):
        if isinstance(expr, list):
            for e in expr:
                node = self.z3_get_var_in_expr(e, name)
                if node is not None:
                    return node
            return None
        children = expr.children()
        if len(children) == 0:
            expr_name = expr.decl().name()
            if expr_name == name:
                return expr
            else:
                return None
        else:
            for child in children:
                node = self.z3_get_var_in_expr(child, name)
                if node is not None:
                    return node
        return None

    def create_new_var_by_name(self, old_var, new_name):
        if isinstance(old_var, z3.ExprRef) and old_var.sort() == z3.IntSort():
            return z3.BitVec(new_name, 32)
            # return z3.Int(new_name)
        elif isinstance(old_var, z3.ExprRef) and old_var.sort() == z3.BitVecSort(32):
            return z3.BitVec(new_name, 32)
        elif isinstance(old_var, z3.ExprRef) and old_var.sort() == z3.StringSort():
            return z3.String(new_name)
        elif isinstance(old_var, z3.ExprRef) and old_var.sort() == z3.BoolSort():
            return z3.Bool(new_name)
        elif isinstance(old_var, str):
            # old_var is the name of a variable
            _type = self.get_var_type(old_var)
            # EXTENSION
            if _type == 'int' or _type == 'unsigned int':
                return z3.BitVec(new_name, 32)
            elif _type == 'long' or _type == 'long int':
                return z3.BitVec(new_name, 64)
            elif _type == 'char' or _type == 'char *' or _type == 'const char *':
                return z3.String(new_name)
            elif _type == 'bool':
                return z3.Bool(new_name)
            else:
                assert False, f'Error: {old_var} is not a valid expression, type: {_type}.'
        else:
            assert False, f'Error: {old_var} is not a valid expression, type: {type(old_var)}.'

    def construct_z3_expr_from_str(self, str_expr: str):
        splitted = str_expr.split(" ")
        if len(splitted) == 1:
            var_name = splitted[0]
            if var_name in self.z3_vars:
                expr = self.z3_vars[var_name]
            else:
                if var_name.startswith('(') and var_name.endswith(')'):
                    var_name = var_name[1:-1].strip()
                expr = self.z3_get_value_expr(var_name)
            return expr
        assert len(splitted) == 3, f"expression should be in the form of var_name op value, but got {str_expr}"
        operand_1 = splitted[0]
        operator = splitted[1]
        operand_2 = splitted[2]
        expr_1 = self.construct_z3_expr_from_str(operand_1)
        expr_2 = self.construct_z3_expr_from_str(operand_2)
        if operator == "+":
            return expr_1 + expr_2
        elif operator == "-":
            return expr_1 - expr_2
        elif operator == "*":
            return expr_1 * expr_2
        elif operator == "/":
            return expr_1 / expr_2
        elif operator == "&":
            return expr_1 & expr_2
        elif operator == "|":
            return expr_1 | expr_2
        elif operator == "^":
            return expr_1 ^ expr_2
        else:
            logger.error(f"invalid operator in {str_expr}: {operator}")
            assert False

    def z3_get_value_expr(self, value_expr, _type=None):
        return expr_ast_to_z3(str(value_expr), self.z3_vars, _type)

    def __get_related_edges(self, var_name):
        related_edges = set()
        _set_edges = self.getAdjacentEdgesForVarName(var_name)
        _adjecent_options = set()
        for _edge in _set_edges:
            _adjecent_options.add(_edge.optionNode.name)
        for _adjecent_option in _adjecent_options:
            _related_edges = self.getAdjacentEdgesForOptionName(_adjecent_option)
            for _related_edge in _related_edges:
                if _related_edge.varNode.name == var_name:
                    related_edges.add(_related_edge)
        return related_edges

    def __get_z3_merged_condition(self, edge):
        _conditions = edge.condition
        # _condition: and all the conditions in _conditions
        _condition = z3.BoolVal(True)
        if type(_conditions) == list:
            for _c in _conditions:
                _condition = z3.And(_condition, _c)
        elif _conditions == True:
            _condition = z3.BoolVal(True)
        else:
            assert False, f'bad format for _conditions: {_conditions}'
        return _condition

    def __get_select_z3_var(self, option):
        _pruned_option = option.replace("-", "_")
        _z3_select_var_name = f'__SELECT__{_pruned_option}__'
        assert _z3_select_var_name in self.z3_vars, f'Error: {_z3_select_var_name} not in z3_vars.'
        select_z3_var = self.z3_vars[_z3_select_var_name]
        return select_z3_var

    def get_extra_conditions_level(self, condition, interested_var_names=None, blocked_options=None):
        if interested_var_names is None:
            all_var_names = self.z3_get_all_var_names(condition)
        else:
            all_var_names = set(interested_var_names)
        print(f'all_var_names: {all_var_names}')
        recursive = False
        next_level_vars = []
        current_level_vars = []
        visited = set()
        # start var_names
        for var_name in all_var_names:
            if not var_name.startswith('__OPTVAL__'):
                next_level_vars.append(var_name)
                visited.add(var_name)
                recursive = True
        extra_conditions = []
        if not recursive:
            return extra_conditions
        MAX_DEPTH = 100
        MAX_LEVEL = self.MAX_LEVEL
        CURRENT_LEVEL = 0
        # level2: var1_2, var2_2, var3_2
        # level1: var1_1, var2_1, var3_1
        # level0: var1_0, var2_0, var3_0
        # The relationship between two levels is defined by the edges: level2 transition to level1 when a new option is parsed
        # The variables in condition are in level0.
        # BackPropagate the variables in level0 to level1, level2, ... when necessary
        # Variable in the last level is the default value
        last_level_var_name_to_z3_var = {}
        new_level_var_name_to_z3_var = {}
        # new_level_var_name_to_z3_select_var = {}
        level_options = {}
        new_level_var_name_to_z3_optval = {}
        for var_name in all_var_names:
            last_level_var_name_to_z3_var[var_name] = self.z3_get_var_in_expr(condition, var_name)
            assert last_level_var_name_to_z3_var[var_name] is not None, f'Error: {var_name} not found in condition: {condition}'
        while True:
            MAX_DEPTH -= 1
            if MAX_DEPTH <= 0:
                logger.error(f'Error: Exceeded max depth for recursive analysis.')
                assert False
            current_level_vars = next_level_vars
            next_level_vars = []
            # break condition
            if len(current_level_vars) == 0:
                break
            CURRENT_LEVEL += 1
            if CURRENT_LEVEL > MAX_LEVEL:
                break
            if CURRENT_LEVEL not in level_options:
                new_level_option_name = f'__OPTION__{CURRENT_LEVEL}__'
                level_options[CURRENT_LEVEL] = z3.String(new_level_option_name)
            # enable_option_z3_var = z3.Bool(f'__ENABLE_OPTION__{CURRENT_LEVEL}__')
            # extra_conditions.append(z3.Or(enable_option_z3_var, level_options[CURRENT_LEVEL] == z3.StringVal("")))
            option_candidates = []
            # handle transition for each var_name
            for var_name in current_level_vars:
                # filter related edges
                related_edges = self.__get_related_edges(var_name)
                # group edges by option
                edge_groups = {}
                for _edge in related_edges:
                    _option = _edge.optionNode.name
                    if _option not in edge_groups:
                        edge_groups[_option] = []
                    edge_groups[_option].append(_edge)
                logger.debug(f'edge_groups:')
                for group_option in edge_groups:
                    print(f'group_option: {group_option}', 'size:', len(edge_groups[group_option]))
                # construct the extra condition:
                # "--option1" [ [condition1, var = value1], [condition2, var = value2] ]
                # "--option2" [ [condition3, var = value3]]
                # extra_condition1 = LEVEL_OPTION == "--option1" -> ((condition1 -> var = value1) and (condition2 -> var = value2) and ((~condition1 and ~condition2) -> False))
                #                  = LEVEL_OPTION == "--option1" -> ((condition1 -> var = value1) and (condition2 -> var = value2) and (condition1 or condition2))
                # extra_condition2 = LEVEL_OPTION == "--option2" -> ((condition3 -> var = value3) and condition3)
                # extra_condition3 = ~(LEVEL_OPTION == "--option1" or LEVEL_OPTION == "--option2") -> LEVEL_OPTION == "" and (var = default_value)
                # extra_condition3 = ~(LEVEL_OPTION == "--option1" or LEVEL_OPTION == "--option2") -> (var = default_value)
                # extra_condition4 = LEVEL_OPTION != all candidates -> LEVEL_OPTION == ""
                # extra_condition = extra_condition1 and extra_condition2 and extra_condition3 and extra_condition4
                _extra_condition = z3.BoolVal(True)
                select_conditions = set() # for default case
                new_level_option = level_options[CURRENT_LEVEL]
                for group_option in edge_groups:
                    if blocked_options and group_option in blocked_options:
                        logger.info(f'[Level {CURRENT_LEVEL}] Skipping visited option: {group_option}')
                        continue
                    # "--option": edge_group: [ [condition1, var = value1], [condition2, var = value2] ]
                    # extra_condition = LEVEL_OPTION == "--option" -> ((condition1 -> var = value1) and (condition2 -> var = value2) and (condition1 or condition2) and enable_option)
                    edge_group = edge_groups[group_option]
                    assert len(edge_group) > 0, f'len(edge_group) = {len(edge_group)}'
                    logger.debug(f'edge_group: {edge_group}')
                    # merged_cases: (condition1 -> var = value1) and (condition2 -> var = value2) and (condition1 or condition2)
                    merged_cases = z3.BoolVal(True)
                    constraint_condition = None
                    for _edge in edge_group:
                        logger.debug(f'_edge: {_edge}')
                        _condition = self.__get_z3_merged_condition(_edge)
                        # level: replace var nodes whose names are var_name to new z3 nodes whose names are {var_name}___{current_level}
                        all_var_names_in_condition = self.z3_get_all_var_names(_condition)
                        for var_name_in_condition in all_var_names_in_condition:
                            var_node = self.z3_get_var_in_expr(_condition, var_name_in_condition)
                            if var_node is not None:
                                if var_name_in_condition in new_level_var_name_to_z3_var:
                                    new_z3_var = new_level_var_name_to_z3_var[var_name_in_condition]
                                else:
                                    new_var_name = f'{var_name_in_condition}___{CURRENT_LEVEL}'
                                    new_z3_var = self.create_new_var_by_name(var_node, new_var_name)
                                    new_level_var_name_to_z3_var[var_name_in_condition] = new_z3_var
                                # substitute the var_node with new_z3_var
                                _condition = z3.substitute(_condition, (var_node, new_z3_var))
                        # level: replace __OPTVAL__{pruned_option}__ with __OPTVAL__{pruned_option}___{CURRENT_LEVEL}
                        pruned_option = group_option.replace("-", "_")
                        original_optval_name = f'__OPTVAL__{pruned_option}__'
                        new_optval_name = f'__OPTVAL__{pruned_option}___{CURRENT_LEVEL}'
                        optval_node = self.z3_get_var_in_expr(_condition, original_optval_name)
                        if optval_node is not None:
                            if group_option in new_level_var_name_to_z3_optval:
                                new_z3_optval = new_level_var_name_to_z3_optval[group_option]
                            else:
                                new_z3_optval = self.create_new_var_by_name(optval_node, new_optval_name)
                                new_level_var_name_to_z3_optval[group_option] = new_z3_optval
                            # substitute the optval_nodes with new_z3_optval
                            _condition = z3.substitute(_condition, (optval_node, new_z3_optval))
                        var_value = _edge.value
                        z3_value_expr = self.z3_get_value_expr(var_value)
                        # assert self.z3_get_var_in_expr(z3_value_expr, var_name) is None, f'var_name: {var_name}, z3_value_expr: {z3_value_expr}'
                        # handle recursive like: flag = flag + 1
                        # replace flag on the right side with new level nodes like: flag = flag___1 + 1
                        operand_var_names = self.z3_get_all_var_names(z3_value_expr)
                        for operand_var_name in operand_var_names:
                            if operand_var_name.startswith("__OPTVAL__"):
                                assert operand_var_name == original_optval_name, f'Error: {operand_var_name} should be {original_optval_name}.'
                                # substitute __OPTVAL__{pruned_option}__ with __OPTVAL__{pruned_option}___{CURRENT_LEVEL}
                                if group_option not in new_level_var_name_to_z3_optval:
                                    assert original_optval_name in self.z3_vars, f'Error: {original_optval_name} not in z3_vars.'
                                    new_level_var_name_to_z3_optval[group_option] = self.create_new_var_by_name(self.z3_vars[original_optval_name], new_optval_name)
                                z3_value_expr = z3.substitute(z3_value_expr, (self.z3_get_var_in_expr(z3_value_expr, original_optval_name), new_level_var_name_to_z3_optval[group_option]))
                                continue
                            if operand_var_name not in new_level_var_name_to_z3_var:
                                new_var_name = f'{operand_var_name}___{CURRENT_LEVEL}'
                                new_z3_var = self.create_new_var_by_name(operand_var_name, new_var_name)
                                new_level_var_name_to_z3_var[operand_var_name] = new_z3_var
                            operand_z3_var = new_level_var_name_to_z3_var[operand_var_name]
                            z3_value_expr = z3.substitute(z3_value_expr, (self.z3_get_var_in_expr(z3_value_expr, operand_var_name), operand_z3_var))
                            next_level_vars.append(operand_var_name)
                        # level: replace var nodes whose names are var_name to last level z3 nodes
                        _setting = last_level_var_name_to_z3_var[var_name] == z3_value_expr
                        # case: (condition1 -> var = value1)
                        case = z3.Implies(_condition, _setting)
                        merged_cases = z3.And(merged_cases, case)
                        if constraint_condition is None:
                            constraint_condition = _condition
                        else:
                            constraint_condition = z3.Or(constraint_condition, _condition)
                        # add unvisited var names to the queue
                        _all_var_names = self.z3_get_all_var_names(_condition)
                        for _var_name in _all_var_names:
                            if not _var_name.startswith('__OPTVAL__'):
                                pruned_var_name = _var_name.split('___')[0]
                                assert pruned_var_name in self.z3_vars, f'Error: {pruned_var_name} not in z3_vars.'
                                next_level_vars.append(pruned_var_name)
                    assert constraint_condition is not None, f'constraint_condition is None for {group_option}'
                    merged_cases = z3.And(merged_cases, constraint_condition)
                    print(f'merged_cases: {merged_cases}')
                    # LEVEL_OPTION == "--option" -> merged_cases
                    # = LEVEL_OPTION == "--option" -> ((condition1 -> var = value1) and (condition2 -> var = value2) and (condition1 or condition2))
                    select_condition = new_level_option == z3.StringVal(group_option)
                    option_candidates.append(group_option)
                    _sub_extra_condition = z3.Implies(select_condition, merged_cases)
                    _extra_condition = z3.And(_extra_condition, _sub_extra_condition)
                    select_conditions.add(select_condition)
                # default case
                default_condition = z3.BoolVal(True)
                for select_condition in select_conditions:
                    default_condition = z3.And(default_condition, select_condition == False)
                if var_name not in new_level_var_name_to_z3_var:
                    # create a new z3 variable for the var_name
                    new_var_name = f'{var_name}___{CURRENT_LEVEL}'
                    new_z3_var = self.create_new_var_by_name(var_name, new_var_name)
                    new_level_var_name_to_z3_var[var_name] = new_z3_var
                assert var_name in new_level_var_name_to_z3_var, f'Error: {var_name} not in new_level_var_name_to_z3_var.'
                default_value = new_level_var_name_to_z3_var[var_name]
                logger.debug(f'default_value: {default_value}, default_condition: {default_condition}')
                # _extra_condition = z3.And(_extra_condition, z3.Implies(default_condition, z3.And(new_level_option == z3.StringVal(""), last_level_var_name_to_z3_var[var_name] == default_value)))
                _extra_condition = z3.And(_extra_condition, z3.Implies(default_condition, last_level_var_name_to_z3_var[var_name] == default_value))
                if CURRENT_LEVEL == MAX_LEVEL or len(next_level_vars) == 0:
                    # initialize the default value
                    initial_value = self.z3_get_default_value(var_name)
                    print(f"typeof new_level_var_name_to_z3_var[var_name]: {type(new_level_var_name_to_z3_var[var_name])}")
                    print(f"type(initial_value): {type(initial_value)}")
                    _extra_condition = z3.And(_extra_condition, new_level_var_name_to_z3_var[var_name] == initial_value)
                    logger.debug(f"initialize default value for {var_name}: {initial_value}")
                _extra_condition = z3.simplify(_extra_condition)
                extra_conditions.append(_extra_condition)
            disable_option_constraint = z3.BoolVal(True)
            for option_candidate in option_candidates:
                disable_option_constraint = z3.And(disable_option_constraint, level_options[CURRENT_LEVEL] != z3.StringVal(option_candidate))
            extra_conditions.append(z3.Implies(disable_option_constraint, level_options[CURRENT_LEVEL] == z3.StringVal("")))
            # update
            last_level_var_name_to_z3_var = new_level_var_name_to_z3_var
            new_level_var_name_to_z3_var = {}
            new_level_var_name_to_z3_select_var = {}
            new_level_var_name_to_z3_optval = {}
        return extra_conditions

    def generate_initial_sequences(self):
        # analyze the dependency of the options
        sequences = []
        tuple_list = []
        _visited_options = set()
        for set_edge in self._setEdges:
            tuple_list.append((set_edge.optionNode.name, set_edge.varNode.name, set_edge.condition, set_edge.value))
            _visited_options.add(set_edge.optionNode.name)
        for option in self.all_options:
            if option in _visited_options:
                continue
            if option in self.check_constraints:
                z3_condition = self.z3_condition_eval(option, None, [self.check_constraints[option]], None)
                tuple_list.append((option, None, z3_condition, None))
        z3_check_global_constraints = []
        for constraint in self.check_global_constraints:
            try:
                constraint = constraint.replace("\\n", " ").replace("\\r", " ").strip()
                if constraint == "":
                    continue
                z3_constraint = eval(constraint, self.z3_vars)
            except Exception as e:
                logger.error(f'condition: {constraint}')
                logger.error(f'z3 condition eval error: {e}')
                assert False, f'condition: {constraint}, z3_vars: {self.z3_vars}'
            z3_check_global_constraints.append(z3_constraint)
        for option, var, _condition, value in tuple_list:
            assert type(_condition) in [z3.z3.BoolRef, list], f'Error: {_condition} is not a valid condition type: {type(_condition)}'
            if type(_condition) == list:
                condition = _condition + z3_check_global_constraints
            elif type(_condition) == z3.z3.BoolRef:
                condition = [_condition] + z3_check_global_constraints
            else:
                assert False, f'Error: {_condition} is not a valid condition type: {type(_condition)}'
            if type(condition) in [z3.z3.BoolRef] and condition == z3.BoolVal(True):
                continue
            else:
                logger.debug("=" * 30)
                logger.debug(f'option: {option}, var: {var}, condition: {condition}, value: {value}')
                # get the extra conditions
                extra_conditions = self.get_extra_conditions_level(condition)
                # z3 solve condition and get the model for var_names
                s = z3.Solver()
                all_var_names = set()
                s.add(condition)
                all_var_names.update(self.z3_get_all_var_names(condition))
                for _extra_condition in extra_conditions:
                    s.add(_extra_condition)
                    all_var_names.update(self.z3_get_all_var_names(_extra_condition))
                if s.check() == z3.sat:
                    model = s.model()
                    logger.debug(f'model: {model}')
                    seq = []
                    options = {}
                    for var_name in all_var_names:
                        # f'__OPTION__{CURRENT_LEVEL}__'
                        if var_name.startswith('__OPTION__'):
                            level = int(var_name.split('__')[2])
                            if level not in options:
                                options[level] = {"option": None, "value": None}
                            option_model = model.eval(z3.String(var_name))
                            option_str = option_model.as_string()
                            options[level]["option"] = option_str
                        # f'__OPTVAL__{pruned_option}___{CURRENT_LEVEL}' instead of '__OPTVAL__{pruned_option}'
                    for level in options:
                        level_option = options[level]["option"]
                        assert level_option is not None, f'Error: option_name is None for level {level}'
                        if level_option in self._optionInfo and self._optionInfo[level_option]["has_optval"]:
                            pruned_option = level_option.replace("-", "_")
                            optval_name = f'__OPTVAL__{pruned_option}___{level}'
                            option_model = model.eval(z3.String(optval_name))
                            option_str = option_model.as_string()
                            options[level]["value"] = option_str
                    for level in sorted(options.keys()):
                        __option = options[level]["option"]
                        __value = options[level]["value"]
                        if __option == '':
                            continue
                        if __value is not None:
                            assert self._optionInfo[__option]["has_optval"], f'Error: {__option} has no optval, but value is {__value}'
                            seq.insert(0, __value)
                        assert __option is not None, f'option is None for level {level}'
                        seq.insert(0, __option)
                    # append option
                    seq.append(option)
                    _option_var_name = "__OPTVAL__" + option.replace("-", "_") + "__"
                    if _option_var_name in all_var_names:
                        option_value = model.eval(self.z3_vars[_option_var_name])
                        assert option_value is not None, f'option_value is None for {_option_var_name}'
                        seq.append(option_value.as_string())
                    logger.info(f'seq: {seq}')
                    sequences.append(seq)
                else:
                    # print unsatisfiable core
                    unsat_core = s.unsat_core()
                    logger.error(f'Unsatisfiable core: {unsat_core}')
                    logger.error(f'Error: {condition} is not satisfiable.')
        # add options that do not appear in the sequences
        all_elements = set()
        for seq in sequences:
            for element in seq:
                all_elements.add(element)
        for _option in self.all_options:
            if _option not in all_elements:
                sequences.append([_option])
        # deduplicate sequences
        sequences = [list(seq) for seq in set(tuple(seq) for seq in sequences)]
        return sequences

    def check_decls(self, string: str):
        # (declare-fun XX () (Array (_ BitVec 32) (_ BitVec 8)))
        # make sure all declare-fun have the same type: (Array (_ BitVec 32) (_ BitVec 8))
        count = string.count('(declare-fun')
        if count == 0:
            return False, []
        pattern = r'\(declare-fun (\w+) \(\) \(Array \(_ BitVec 32\) \(_ BitVec 8\)\)\)'
        varnames = re.findall(pattern, string)
        assert len(varnames) == count, "Not all declare-fun have the same type: (Array (_ BitVec 32) (_ BitVec 8)):\n{}".format(string)
        print("All declare-fun have the same type: (Array (_ BitVec 32) (_ BitVec 8))")
        return True, varnames

    def update_name_mapping(self, varnames: list):
        if self.name_mapping is None:
            self.name_mapping = {}
        for varname in varnames:
            if varname in self.name_mapping:
                # if varname is already in name_mapping, skip it
                continue
            # select name_in_graph which is a prefix of varname and has the longest length
            name_in_graph = max((name for name in self._varNodes if varname.startswith(name)), key=len, default=None)
            if name_in_graph is not None:
                self.name_mapping[varname] = name_in_graph
                logger.debug(f"Updated name_mapping: {varname} -> {name_in_graph}")
                path = "TODO:"
                with open(path, 'w') as f:
                    json.dump(self.name_mapping, f, indent=4)

    def get_solve_name_mapping(self):
        return self.name_mapping

    def get_bv(self, option_sequence_list):
        if self.bv_map is None:
            self.bv_map = {}
            for index, option in enumerate(sorted(self.all_options)):
                self.bv_map[option] = index
            self.bv_len = len(self.all_options)
        bv_repr_list = ["0"] * self.bv_len
        for option_list in option_sequence_list:
            if len(option_list) == 0:
                continue
            option_name = option_list[0]
            assert option_name in self.bv_map, f'Error: {option_name} not in bv_map: {self.bv_map}'
            index = int(self.bv_map[option_name])
            assert index < self.bv_len, f'Error: index {index} out of range for bv_len {self.bv_len}'
            bv_repr_list[index] = "1"
        bv_repr = "".join(bv_repr_list)
        return bv_repr

    def log_solve_time(self, start_time):
        end_time = time.time()
        elapsed_time = end_time - start_time
        print(f"* Solve time: {elapsed_time:.2f} seconds")
        # append to file
        with open("TODO:", "a") as f:
            f.write(f"solve time: {elapsed_time:.4f} seconds\n")

    def solve(self, constraint_str: str, concrete_option_sequence: list = []):
        has_state_variable = False
        hasvar, varnames = self.check_decls(constraint_str)
        if not hasvar:
            print("No declare-fun found")
            return []
        self.update_name_mapping(varnames)
        name_mapping = self.get_solve_name_mapping()
        for varname in varnames:
            if "stdin" in varname:
                continue
            if "_data" in varname:
                continue
            if "const_arr" in varname:
                continue
            has_state_variable = True
            break
        if not has_state_variable:
            print("* No state variable found")
            return []
        # log start time
        start_time = time.time()
        s = z3.Solver()
        # add original constraints
        p = z3.parse_smt2_string(constraint_str)
        s.add(p)
        interested_var_names = set()
        for varname in varnames:
            logger.debug(f'Processing variable: {varname}')
            # get corresponding z3 variables
            if varname not in name_mapping:
                continue
            name_in_graph = name_mapping[varname]
            assert name_in_graph in self.z3_vars, f'Error: {name_in_graph} not in z3_vars: {self.z3_vars}'
            # get all adjacent edges for the variable
            adjacent_edges = self.getAdjacentEdgesForVarName(name_in_graph)
            possible_values = set()
            for adjacent_edge in adjacent_edges:
                # get the value of the variable
                value = adjacent_edge.value
                assert isinstance(value, str), f'Error: {value} is not a valid value for {name_in_graph}.'
                if value.startswith('__OPTVAL__'):
                    logger.warning(f'Skipping __OPTVAL__ value: {value} for {name_in_graph}')
                    continue
                possible_values.add(value)
            logger.debug(f'Possible values for {name_in_graph}: {possible_values}')
            z3_var = self.z3_vars[name_in_graph]
            if isinstance(z3_var, z3.ExprRef) and z3_var.sort() == z3.BitVecSort(32):
                intlen = 32
                assert intlen % 8 == 0, "intlen should be a multiple of 8: {}".format(intlen)
                bv_name = name_in_graph
                bv = z3_var
                additional_constraint = []
                for i in range(intlen // 8):
                    index = z3.BitVecVal(i, 32)
                    # get the i-th byte of the int variable
                    byte = z3.Extract(8 * (i + 1) - 1, 8 * i, bv)
                    # add the constraint to the solver
                    additional_constraint.append(z3.Select(z3.Array(varname, z3.BitVecSort(32), z3.BitVecSort(8)), index) == byte)
                assert len(additional_constraint) > 0, f'Error: additional_constraint is empty for {name_in_graph}.'
                s.add(z3.And(additional_constraint))
                interested_var_names.add(name_in_graph)
            elif isinstance(z3_var, z3.ExprRef) and z3_var.sort() == z3.BoolSort():
                # ((_ extract 0  0)  (select  x (_ bv0 32) ) )
                # z3_var -> ((_ extract 0  0)  (select  x (_ bv0 32) ) ) == (_ bv1 1)
                # not_z3_var -> ((_ extract 0  0)  (select  x (_ bv0 32) ) ) == (_ bv0 1)
                additional_constraint = []
                index = z3.BitVecVal(0, 32)
                last_bit_expr = z3.Extract(0, 0, z3.Select(z3.Array(varname, z3.BitVecSort(32), z3.BitVecSort(8)), index))
                constraint_1 = z3.Implies(z3_var == z3.BoolVal(True), last_bit_expr == z3.BitVecVal(1, 1))
                constraint_0 = z3.Implies(z3_var == z3.BoolVal(False), last_bit_expr == z3.BitVecVal(0, 1))
                additional_constraint.append(constraint_1)
                additional_constraint.append(constraint_0)
                s.add(z3.And(additional_constraint))
                interested_var_names.add(name_in_graph)
            elif isinstance(z3_var, z3.ExprRef) and z3_var.sort() == z3.StringSort():
                MAX_CMP_LEN = 3
                cases = []
                str_var = z3_var
                _, default_value = self._get_default_value(name_in_graph)
                if default_value is not None and default_value not in possible_values:
                    if default_value == 0:
                        possible_values.add("")
                for possible_value in possible_values:
                    if possible_value.startswith('"') or possible_value.startswith("'"):
                        assert possible_value.endswith('"')
                        possible_value = possible_value[1:-1]
                    else:
                        assert len(possible_value.split()) <= 1
                    assert len(possible_value) <= MAX_CMP_LEN
                    additional_constraint = []
                    for index in range(MAX_CMP_LEN):
                        if index >= len(possible_value):
                            char = '\0'
                        else:
                            char = possible_value[index]
                        byte = ord(char)
                        index_bv = z3.BitVecVal(index, 32)
                        additional_constraint.append(z3.Select(z3.Array(varname, z3.BitVecSort(32), z3.BitVecSort(8)), index_bv) == z3.BitVecVal(byte, 8))
                    if len(additional_constraint) > 0:
                        cases.append(z3.And(additional_constraint))
                if len(cases) > 0:
                    s.add(z3.Or(cases))
            else:
                assert False, f'Error: {z3_var} is not a valid expression.'
        print(f'Z3 Solver before extra conditions:')
        print(s)
        # convert p to z3 expression
        UNSAT_TOKEN = "UNSAT"
        z3_expr_p_all = z3.And(s.assertions())
        z3_expr_p = z3.simplify(z3_expr_p_all)
        if z3_expr_p == z3.BoolVal(False):
            print("Input constraint is unsatisfiable.")
            self.log_solve_time(start_time)
            return [[UNSAT_TOKEN]]

        # Decompose the concrete_option_sequence early to pass to get_extra_conditions_level
        option_sequence_list = [] # list[list]
        j = 0
        for i, seq in enumerate(concrete_option_sequence):
            if seq.startswith("-") and i > 0:
                # append last option sequence
                option_sequence_list.append(concrete_option_sequence[j:i])
                j = i
        if j < len(concrete_option_sequence):
            option_sequence_list.append(concrete_option_sequence[j:])
        logger.debug(f'Initial option_sequence_list: {option_sequence_list}')

        # Build blocked options map from visited sequences
        blocked_options = set()
        for option in self.all_options:
            bv_repr = self.get_bv(option_sequence_list + [[option]])
            if bv_repr in self._visited_seqs_bv:
                blocked_options.add(option)

        extra_conditions = self.get_extra_conditions_level(z3_expr_p, interested_var_names=list(interested_var_names), blocked_options=blocked_options)
        print(f'Extra conditions: {extra_conditions}')
        for extra_condition in extra_conditions:
            s.add(extra_condition)
        print("Z3 Solver:")
        print(s)
        print("Solve result:")
        print(s.check())
        if s.check() != z3.sat:
            self.log_solve_time(start_time)
            return [[UNSAT_TOKEN]]
        model = s.model()
        print("Model:")
        print(model)
        for varname in varnames:
            if varname not in name_mapping:
                continue
            z3_var = self.z3_vars[name_mapping[varname]]
            if isinstance(z3_var, z3.ExprRef) and z3_var.sort() == z3.BitVecSort(32):
                bv_name = name_mapping[varname]
                bv = z3.BitVec(bv_name, 32)
                # get the value of the BitVec variable
                value = model.evaluate(bv)
                logger.debug("bv value for {}: {}".format(varname, value))
            elif isinstance(z3_var, z3.ExprRef) and z3_var.sort() == z3.BoolSort():
                bool_name = name_mapping[varname]
                bool_var = z3.Bool(bool_name)
                # get the value of the Bool variable
                value = model.evaluate(bool_var)
                logger.debug("bool value for {}: {}".format(varname, value))
            elif isinstance(z3_var, z3.ExprRef) and z3_var.sort() == z3.StringSort():
                MAX_CMP_LEN = 3
                s = ""
                for index in range(MAX_CMP_LEN):
                    index_bv = z3.BitVecVal(index, 32)
                    byte = model.evaluate(z3.Select(z3.Array(varname, z3.BitVecSort(32), z3.BitVecSort(8)), index_bv))
                    char = chr(int(str(byte)))
                    # if char is printable, append it to the string
                    if char.isprintable():
                        s = char + s
                    else:
                        # if char is not printable, print its ASCII value
                        logger.warning(f'Non-printable character at index {index}: {byte}')
                logger.debug(f'str value for {varname}: {s} length: {len(s)}')
                name_in_graph = name_mapping[varname]
                adjacent_edges = self.getAdjacentEdgesForVarName(name_in_graph)
                possible_options = set()
                for adjacent_edge in adjacent_edges:
                    # get the value of the variable
                    value = adjacent_edge.value
                    _option = adjacent_edge.optionNode.name
                    assert isinstance(value, str), f'Error: {value} is not a valid value for {name_in_graph}.'
                    stripped_value = value.strip('"').strip("'")
                    if s == stripped_value:
                        logger.info(f'Found option: {_option} for {name_in_graph} with value: {s}')
                        possible_options.add(_option)
                if len(possible_options) > 0:
                    random_option = random.choice(list(possible_options))
                    option_element = [random_option]
                    # remove __option from option_sequence_list
                    option_sequence_list = self.adjust_option_sequence_list(option_sequence_list, random_option, option_element)
        # adjust the sequences
        sequences = []
        options = {}
        for level in range(1, self.MAX_LEVEL + 1):
            var_name = f'__OPTION__{level}__'
            if level not in options:
                options[level] = {"option": None, "value": None}
            option_model = model.eval(z3.String(var_name))
            option_str = option_model.as_string()
            options[level]["option"] = option_str
        for level in options:
            level_option = options[level]["option"]
            assert level_option is not None, f'Error: option_name is None for level {level}'
            if level_option in self._optionInfo and self._optionInfo[level_option]["has_optval"]:
                pruned_option = level_option.replace("-", "_")
                optval_name = f'__OPTVAL__{pruned_option}___{level}'
                option_model = model.eval(z3.String(optval_name))
                option_str = option_model.as_string()
                options[level]["value"] = option_str
        desymbolize_flag = False
        desymbolize_state_variables = set()
        for level in sorted(options.keys()):
            __option = options[level]["option"]
            __value = options[level]["value"]
            if __option.startswith("__OPTION__"):
                continue
            option_element = []
            assert __option is not None, f'option is None for level {level}'
            option_element.append(__option)
            if __value is not None:
                assert self._optionInfo[__option]["has_optval"], f'Error: {__option} has no optval, but value is {__value}'
                option_element.append(__value)
            if __option == "":
                desymbolize_flag = True
            # remove __option from option_sequence_list
            option_sequence_list = self.adjust_option_sequence_list(option_sequence_list, __option, option_element)
        # notify klee desymbolize
        desymbolize_probability = 1
        if random.random() < desymbolize_probability:
            desymbolize_flag = True
        if desymbolize_flag:
            all_var_names = self.z3_get_all_var_names(z3.And(p))
            for var_name in all_var_names:
                if var_name not in name_mapping:
                    continue
                assert var_name in name_mapping, f'Error: {var_name} not in name_mapping: {name_mapping}'
                name_in_graph = name_mapping[var_name]
                desymbolize_state_variables.add(name_in_graph)
            desymbolize_state_variables = set()
            ALL_TOKEN = "__ALL__"
            desymbolize_state_variables.add(ALL_TOKEN)
        # append option
        logger.info(f'option_sequence_list: {option_sequence_list}')
        candidates = []
        candidates.append(option_sequence_list)
        # deduplicate candidates
        for candidate in candidates:
            if len(candidate) == 0:
                continue
            candidate_str = str(candidate)
            if candidate_str not in self._visited_seqs:
                self._visited_seqs.add(candidate_str)
                self._visited_seqs_with_timestamp[candidate_str] = time.time()
                bv_repr = self.get_bv(candidate)
                self._visited_seqs_bv.add(bv_repr)
                if desymbolize_probability < 1:
                    sequences.append(candidate)
                # desymbolize
                if desymbolize_flag:
                    new_candidate = copy.deepcopy(candidate)
                    DESYMBOLIZE_TOKEN = "__DESYMBOLIZE__"
                    desymbolize_item = []
                    desymbolize_item.append(DESYMBOLIZE_TOKEN)
                    for var_name in sorted(desymbolize_state_variables):
                        desymbolize_item.append(var_name)
                    new_candidate.append(desymbolize_item)
                    sequences.append(new_candidate)

        self.log_solve_time(start_time)
        return sequences

    def adjust_option_sequence_list(self, option_sequence_list, __option, option_element):
        new_option_sequence_list = []
        for seq in option_sequence_list:
            if __option not in seq:
                new_option_sequence_list.append(seq)
        new_option_sequence_list.insert(0, option_element)
        return new_option_sequence_list