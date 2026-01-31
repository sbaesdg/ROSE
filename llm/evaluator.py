from custom_logger import logger
from renamer import Renamer
import ast
import operator
from functools import reduce

def evaluate(expr, default_values: dict = None, _renamer: Renamer = None):
    # return is_const, value
    logger.debug(f"evaluate: {expr}")
    if type(expr) == int:
        # basic types: int
        return True, expr
    elif type(expr) == str:
        # basic types: str
        if expr.startswith("0x"):
            # hex value
            return True, int(expr, 16)
        elif expr in ["${OPTVAL}", "${OPTVAL_INT}", "${OPTVAL_FP}", "${OPTVAL_FLOAT}"]:
            # TODO: OPTVAL_FP
            # special value
            return False, expr
        elif expr == "true":
            return True, "True"
        elif expr == "false":
            return True, "False"
        elif expr.startswith("\'") or expr.startswith("\""):
            assert len(expr) >= 2, f"invalid expression: {expr}"
            expr = expr[1:-1]
            return True, expr
        elif expr.isdigit():
            # decimal value: note that "0".isdigit() == True
            return True, int(expr)
        elif expr.startswith("-"):
            # negative value: -expr
            assert len(expr) >= 2, f"invalid expression: {expr}"
            is_const, value = evaluate(expr[1:], default_values, _renamer)
            if is_const:
                return True, -value
            else:
                return False, f"-{value}"
        elif expr.startswith("~"):
            is_const, value = evaluate(expr[1:], default_values, _renamer)
            if is_const:
                # bitwise NOT operation
                return True, ~int(value)
            else:
                # bitwise NOT operation with variable
                assert False, "Unimplemented bitwise NOT operation with variable"
                return False, f"~{value}"
        elif expr.startswith("(") and expr.endswith(")"):
            # expression: (expr)
            assert len(expr) >= 2, f"invalid expression: {expr}"
            expr = expr[1:-1]
            is_const, value = evaluate(expr, default_values, _renamer)
            return is_const, value
        else:
            last_field = _renamer.get_last_field(expr)
            if last_field in default_values:
                return False, expr
            logger.error(f"invalid expression: {expr}")
            logger.debug(f"expr: {expr}")
            logger.debug(f"default_values: {default_values}")
            assert False
    elif type(expr) == tuple:
        # tuple: (operator, operand1, operand2, ...)
        assert len(expr) == 3, f"invalid expression: {expr}"
        contain_optval = False
        if "${OPTVAL}" in expr[1] or "${OPTVAL_INT}" in expr[1] or "{OPTVAL_FP}" in expr[1] or "${OPTVAL_FLOAT}" in expr[1]:
            # TODO: OPTVAL_FP
            left_value = expr[1]
            contain_optval = True
            is_const_left = None
        else:
            is_const_left, left_value = evaluate(expr[1], default_values, _renamer)
        if "${OPTVAL}" in expr[2] or "${OPTVAL_INT}" in expr[2] or "{OPTVAL_FP}" in expr[2] or "${OPTVAL_FLOAT}" in expr[2]:
            # TODO: OPTVAL_FP
            right_value = expr[2]
            contain_optval = True
            is_const_right = None
        else:
            is_const_right, right_value = evaluate(expr[2], default_values, _renamer)
        operator = expr[0]
        if contain_optval:
            return False, f"({left_value}) {operator} ({right_value})"
        assert is_const_left is not None and is_const_right is not None, f"invalid expression: {expr}"
        if not is_const_left or not is_const_right:
            return False, f"({left_value}) {operator} ({right_value})"
        if operator == "+":
            return True, left_value + right_value
        elif operator == "-":
            return True, left_value - right_value
        elif operator == "*":
            return True, left_value * right_value
        elif operator == "/":
            assert right_value != 0, f"division by zero in expression: {expr}"
            return True, left_value / right_value
        elif operator == "&":
            return True, left_value & right_value
        elif operator == "|":
            return True, left_value | right_value
        elif operator == "^":
            return True, left_value ^ right_value
        else:
            logger.error(f"invalid operator: {operator}")
            logger.debug(f"expr: {expr}")
            assert False, f"invalid operator: {operator}"
    else:
        # invalid type
        logger.error(f"invalid expression: {expr}")
        assert False

class ConstantFolder(ast.NodeTransformer):
    def __init__(self):
        self.op_map = {
            ast.Add: operator.add,
            ast.Sub: operator.sub,
            ast.Mult: operator.mul,
            ast.Div: operator.truediv,
            ast.FloorDiv: operator.floordiv,
            ast.Mod: operator.mod,
            ast.Pow: operator.pow,

            ast.BitAnd: operator.and_,
            ast.BitOr: operator.or_,
            ast.BitXor: operator.xor,
            ast.LShift: operator.lshift,
            ast.RShift: operator.rshift,
        }

        self.unary_op_map = {
            ast.UAdd: operator.pos,
            ast.USub: operator.neg,
            ast.Not: operator.not_,
            ast.Invert: operator.invert,
        }

        self.op_identity = {
            ast.Add: 0,
            ast.Mult: 1,
            ast.BitOr: 0,
            ast.BitXor: 0,
            ast.BitAnd: -1,
        }

    def visit_UnaryOp(self, node):
        node.operand = self.visit(node.operand)
        
        if isinstance(node.operand, ast.Constant):
            op_type = type(node.op)
            if op_type in self.unary_op_map:
                try:
                    result = self.unary_op_map[op_type](node.operand.value)
                    return ast.Constant(value=result)
                except Exception:
                    pass
        
        return node

    def visit_BinOp(self, node):
        node.left = self.visit(node.left)
        node.right = self.visit(node.right)

        op_type = type(node.op)
        if op_type not in self.op_map:
            return node

        if not self._is_chain_of_same_op(node, op_type):
            return node

        flat = self._flatten_binop(node, op_type)
        constants = []
        variables = []

        for x in flat:
            if self._is_constant_value(x):
                constants.append(self._get_constant_value(x))
            else:
                variables.append(x)

        folded_const = None
        if constants:
            try:
                folded_const = reduce(self.op_map[op_type], constants)
            except Exception as e:
                print(f"Error folding constants: {e}")

        nodes = variables[:]
        if folded_const is not None:
            identity = self.op_identity.get(op_type)
            if identity is None or folded_const != identity or not nodes:
                nodes.append(ast.Constant(value=folded_const))

        if not nodes:
            return ast.Constant(value=self.op_identity.get(op_type, 0))
        elif len(nodes) == 1:
            return nodes[0]
        else:
            expr = nodes[0]
            for n in nodes[1:]:
                expr = ast.BinOp(left=expr, op=node.op, right=n)
            return expr

    def _is_constant_value(self, node):
        if isinstance(node, ast.Constant):
            return True
        if isinstance(node, ast.UnaryOp) and isinstance(node.operand, ast.Constant):
            return type(node.op) in self.unary_op_map
        return False

    def _get_constant_value(self, node):
        if isinstance(node, ast.Constant):
            return node.value
        if isinstance(node, ast.UnaryOp) and isinstance(node.operand, ast.Constant):
            op_type = type(node.op)
            if op_type in self.unary_op_map:
                return self.unary_op_map[op_type](node.operand.value)
        raise ValueError(f"Cannot get constant value from {ast.dump(node)}")

    def _flatten_binop(self, node, op_type):
        result = []
        def helper(n):
            if isinstance(n, ast.BinOp) and type(n.op) == op_type:
                helper(n.left)
                helper(n.right)
            else:
                result.append(n)
        helper(node)
        return result

    def _is_chain_of_same_op(self, node, op_type):
        if not isinstance(node, ast.BinOp) or type(node.op) != op_type:
            return False
        
        def contains_same_op_or_constant(n):
            if self._is_constant_value(n):
                return True
            if isinstance(n, ast.BinOp) and type(n.op) == op_type:
                return True
            return False
        
        return (contains_same_op_or_constant(node.left) or 
                contains_same_op_or_constant(node.right))

def pretty_dump(node, annotate_fields=True, include_attributes=False, indent='  '):
    def _format(node, level=0):
        if isinstance(node, ast.AST):
            fields = [(a, _format(b, level + 1)) for a, b in ast.iter_fields(node)]
            rv = '%s(' % node.__class__.__name__
            if fields:
                rv += '\n' + '\n'.join(
                    (indent * (level + 1)) + f'{a}={b}' for a, b in fields
                ) + '\n' + (indent * level) + ')'
            else:
                rv += ')'
            return rv
        elif isinstance(node, list):
            lines = ['[']
            for x in node:
                lines.append((indent * (level + 1)) + _format(x, level + 1) + ',')
            lines.append((indent * level) + ']')
            return '\n'.join(lines)
        return repr(node)

    return _format(node)

class ASTToCode(ast.NodeVisitor):
    def __init__(self):
        self.code = []
    
    def visit_Module(self, node):
        for stmt in node.body:
            self.visit(stmt)
    
    def visit_Expr(self, node):
        self.visit(node.value)
    
    def visit_Assign(self, node):
        for target in node.targets:
            self.visit(target)
        self.code.append(' = ')
        self.visit(node.value)
    
    def visit_BinOp(self, node):
        self.code.append('(')
        self.visit(node.left)
        self.code.append(' ')
        self.visit(node.op)
        self.code.append(' ')
        self.visit(node.right)
        self.code.append(')')
    
    def visit_UnaryOp(self, node):
        self.visit(node.op)
        self.code.append('(')
        self.visit(node.operand)
        self.code.append(')')
    
    def visit_Name(self, node):
        self.code.append(node.id)
    
    def visit_Constant(self, node):
        self.code.append(repr(node.value))
    
    def visit_Num(self, node):
        self.code.append(str(node.n))
    
    def visit_Str(self, node):
        self.code.append(repr(node.s))
    
    def visit_NameConstant(self, node):
        self.code.append(str(node.value))
    
    def visit_Add(self, node):
        self.code.append('+')
    
    def visit_Sub(self, node):
        self.code.append('-')
    
    def visit_Mult(self, node):
        self.code.append('*')
    
    def visit_Div(self, node):
        self.code.append('/')
    
    def visit_FloorDiv(self, node):
        self.code.append('//')
    
    def visit_Mod(self, node):
        self.code.append('%')
    
    def visit_Pow(self, node):
        self.code.append('**')
    
    def visit_LShift(self, node):
        self.code.append('<<')
    
    def visit_RShift(self, node):
        self.code.append('>>')
    
    def visit_BitOr(self, node):
        self.code.append('|')
    
    def visit_BitXor(self, node):
        self.code.append('^')
    
    def visit_BitAnd(self, node):
        self.code.append('&')
    
    def visit_UAdd(self, node):
        self.code.append('+')
    
    def visit_USub(self, node):
        self.code.append('-')
    
    def visit_Not(self, node):
        self.code.append('not ')
    
    def visit_Invert(self, node):
        self.code.append('~')
    
    def get_code(self):
        return ''.join(self.code)

def ast_to_string(tree: ast.AST) -> str:
    converter = ASTToCode()
    converter.visit(tree)
    return converter.get_code()

def simplify_expression(expr):
    tree = ast.parse(expr, mode='exec')

    folder = ConstantFolder()
    optimized = folder.visit(tree)
    ast.fix_missing_locations(optimized)

    code_str = ast_to_string(optimized)
    return code_str