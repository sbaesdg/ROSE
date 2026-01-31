import json
import re
import ast
from typing import Dict
import z3
from custom_logger import logger

def load_json(file_path):
    with open(file_path, 'r') as f:
        return json.load(f)

def str_to_json(s):
    s = re.sub(r'\'', r'"', s)
    try:
        res = json.loads(s)
    except json.JSONDecodeError as e:
        logger.error("Error decoding JSON: {}".format(e))
        logger.error("Input string: {}".format(s))
        assert False
    return res

class ASTToZ3Expr(ast.NodeVisitor):
    def __init__(self, z3_vars: Dict, _type=None):
        # z3_vars: {varname: Z3Expression, "Not": z3.Not, ...}
        self.z3_vars = z3_vars
        self._type = _type
        self.result = None
    
    def visit_BoolOp(self, node):
        left = self.visit(node.values[0])
        
        if isinstance(node.op, ast.And):
            result = left
            for value in node.values[1:]:
                right = self.visit(value)
                result = z3.And(result, right)
            return result
        elif isinstance(node.op, ast.Or):
            result = left
            for value in node.values[1:]:
                right = self.visit(value)
                result = z3.Or(result, right)
            return result
    
    def visit_UnaryOp(self, node):
        operand = self.visit(node.operand)
        
        if isinstance(node.op, ast.Not):
            return z3.Not(operand)
        elif isinstance(node.op, ast.UAdd):
            return operand
        elif isinstance(node.op, ast.USub):
            return -operand
    
    def visit_Compare(self, node):
        left = self.visit(node.left)
        
        result = None
        current_left = left
        
        for i, (op, comparator) in enumerate(zip(node.ops, node.comparators)):
            right = self.visit(comparator)
            
            if isinstance(op, ast.Eq):
                comparison = (current_left == right)
            elif isinstance(op, ast.NotEq):
                comparison = (current_left != right)
            elif isinstance(op, ast.Lt):
                comparison = (current_left < right)
            elif isinstance(op, ast.LtE):
                comparison = (current_left <= right)
            elif isinstance(op, ast.Gt):
                comparison = (current_left > right)
            elif isinstance(op, ast.GtE):
                comparison = (current_left >= right)
            elif isinstance(op, ast.In):
                if hasattr(right, '__iter__'):
                    comparison = z3.Or([current_left == item for item in right])
                else:
                    comparison = (current_left == right)
            elif isinstance(op, ast.NotIn):
                if hasattr(right, '__iter__'):
                    comparison = z3.And([current_left != item for item in right])
                else:
                    comparison = (current_left != right)
            else:
                raise NotImplementedError(f"unimplemented comparison operator {type(op)}")
            
            if result is None:
                result = comparison
            else:
                result = z3.And(result, comparison)
            
            current_left = right
        
        return result
    
    def visit_BinOp(self, node):
        left = self.visit(node.left)
        right = self.visit(node.right)
        
        if isinstance(node.op, ast.Add):
            return left + right
        elif isinstance(node.op, ast.Sub):
            return left - right
        elif isinstance(node.op, ast.Mult):
            return left * right
        elif isinstance(node.op, ast.Div):
            return left / right
        elif isinstance(node.op, ast.FloorDiv):
            return left / right
        elif isinstance(node.op, ast.Mod):
            return left % right
        elif isinstance(node.op, ast.Pow):
            return left ** right
        elif isinstance(node.op, ast.BitAnd):
            return left & right
        elif isinstance(node.op, ast.BitOr):
            return left | right
        elif isinstance(node.op, ast.BitXor):
            return left ^ right
        else:
            raise NotImplementedError(f"unimplemented binary operator {type(node.op)}")
    
    def visit_Name(self, node):
        if node.id in self.z3_vars:
            return self.z3_vars[node.id]
        else:
            raise ValueError(f"not found variable {node.id}")
    
    def visit_Constant(self, node):
        if self._type in ["char"]:
            if isinstance(node.value, int):
                assert 0 <= node.value <= 255, f"char value out of range: {node.value}"
                if node.value == 0:
                    return z3.StringVal("")
                char = chr(node.value)
                return z3.StringVal(char)
            elif isinstance(node.value, str):
                return z3.StringVal(node.value)
            else:
                assert False, f"Unsupported constant type: {type(node.value)}"
        # EXTENSION
        elif isinstance(node.value, bool):
            return z3.BoolVal(node.value)
        elif isinstance(node.value, int):
            return z3.BitVecVal(node.value, 32)
        elif isinstance(node.value, str):
            return z3.StringVal(node.value)
        else:
            return node.value
    
    def visit_Num(self, node):
        return node.n
    
    def visit_Str(self, node):
        return node.s
    
    def visit_NameConstant(self, node):
        return node.value
    
    def visit_Call(self, node):
        func_name = None
        if isinstance(node.func, ast.Name):
            func_name = node.func.id
        elif isinstance(node.func, ast.Attribute):
            func_name = node.func.attr
        
        if func_name and func_name in self.z3_vars:
            z3_func = self.z3_vars[func_name]
            args = [self.visit(arg) for arg in node.args]
            if func_name == "StrToInt":
                return z3.Int2BV(z3_func(*args), 32)
            else:
                return z3_func(*args)
        else:
            raise ValueError(f"not found function {func_name}")
    
    def visit_List(self, node):
        return [self.visit(item) for item in node.elts]
    
    def visit_Tuple(self, node):
        return tuple(self.visit(item) for item in node.elts)
    
    def visit_IfExp(self, node):
        test = self.visit(node.test)
        body = self.visit(node.body)
        orelse = self.visit(node.orelse)
        return z3.If(test, body, orelse)
    
    def visit(self, node):
        if node is None:
            return None
        
        method_name = 'visit_' + node.__class__.__name__
        visitor = getattr(self, method_name, self.generic_visit)
        result = visitor(node)
        
        if result is not None:
            self.result = result
        
        return result
    
    def generic_visit(self, node):
        raise NotImplementedError(f"not implemented visit method for {type(node)}")

def expr_ast_to_z3(expr: str, z3_vars: Dict, _type = None) -> z3.ExprRef:
    assert type(expr) == str, f"type(expr) should be str, but got {type(expr)}"
    ast_tree = ast.parse(expr, mode='eval')
    converter = ASTToZ3Expr(z3_vars, _type)
    return converter.visit(ast_tree.body)