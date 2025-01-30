import sys
from lark import Lark, Transformer, Tree
import lark
import os
import math

#print(f"Python version: {sys.version}")
#print(f"Lark version: {lark.__version__}")

#  run/execute/interpret source code
def interpret(source_code):
    cst = parser.parse(source_code)
    ast = LambdaCalculusTransformer().transform(cst)
    result_ast = evaluate(ast)
    result = linearize(result_ast)
    return result

# convert concrete syntax to CST
parser = Lark(open("grammar.lark").read(), parser='lalr')

# convert CST to AST
class LambdaCalculusTransformer(Transformer):
    def lam(self, args):
        name, body = args
        return ('lam', str(name), body)

    def app(self, args):
        new_args = [(arg.data, arg.children[0]) if isinstance(arg, Tree) and arg.data == 'int' else arg for arg in args]
        return ('app', *new_args)

    def var(self, args):
        token, = args
        return ('var', str(token))
    
    def prog(self, args):
        left, right = args
        return ("prog", left, right)

    def NAME(self, token):
        return str(token)
    
    def num(self, args):
        token, = args
        return ('num', float(token))
    
    def parens(self, args):
        expr, = args
        return expr

    def plus(self, args):
        left, right = args
        return ("plus", left, right)
    
    def minus(self, args):
        left, right = args
        return ("minus", left, right)
    
    def multiply(self, args):
        left, right = args
        return ("multiply", left, right)
    
    def divide(self, args):
        left, right = args
        return ("divide", left, right)
    
    def power(self, args):
        left, right = args
        return ("power", left, right)
    
    def log(self, args):
        left, right = args
        return ("log", left, "base", right)
    
    #def base(self, args):
     #  left, right = args
      # return ("base", left, right)
    
    def ifelse(self, args):
        left, middle, right = args
        return ("if", left, "then", middle, "else", right)
    
    def leq(self, args): 
        left, right = args
        return ("leq", left, right)
    
    def eq(self, args):
        left, right = args
        return ("eq", left, right)
    
    def let(self, args):
        name, left, right = args
        return ("let", name, "=", left, "in", right)
    
    def rec(self, args):
        name, left, right = args
        return ("letrec", name, "=", left, "in", right)
    
    def fix(self, args):
        right = args
        return ("fix", right)

# reduce AST to normal form
def evaluate(tree):
    if tree[0] == 'app':
        e1 = evaluate(tree[1])
        if e1[0] == 'lam':
            body = e1[2]
            name = e1[1]
            arg = tree[2]
            rhs = substitute(body, name, arg)
            result = evaluate(rhs)
            pass
        else:
            result = ('app', e1, tree[2])
            pass
    elif (tree[0] == 'plus'):
        return ('num', evaluate(tree[1]) + evaluate(tree[2]))
    elif (tree[0] == 'minus'):
        return  ('num', evaluate(tree[1]) - evaluate(tree[2]))
    elif (tree[0] == 'multiply'):
        return  ('num', evaluate(tree[1]) * evaluate(tree[2]))
    elif (tree[0] == 'divide'):
        return  ('num', evaluate(tree[1]) / evaluate(tree[2]))
    elif (tree[0] == 'power'):
        return  ('num', evaluate(tree[1]) ** evaluate(tree[2]))
    elif (tree[0] == 'log'):
        number = evaluate(tree[1])
        base = evaluate(tree[3])
        result = math.log(number[1], base[1])
        return ('num', float(result))
    elif (tree[0] == 'if'):
        condition = evaluate(tree[1])
        if condition[0] != 'num':
            return ('if', condition, tree[3], tree[5])
        if condition[1]:
            return evaluate(tree[3])
        else: 
            return evaluate(tree[5])
    elif (tree[0] == 'leq'):
        left = evaluate(tree[1])
        right = evaluate(tree[2])
        if left[0] == 'num' and right[0] == 'num':
            return ('num', left[1] <= right[1])
        return ('leq', left, right)
    elif (tree[0] == 'eq'):
        left = evaluate(tree[1])
        right = evaluate(tree[2])
        if left[0] == 'num' and right[0] == 'num':
            return ('num', left[1] == right[1])
        return ('eq', left, right)
    elif (tree[0] == 'let'):
        name = tree[1]
        value = evaluate(tree[3])
        body = tree[5]
        return evaluate(substitute(body, name, value))
    elif (tree[0] == 'letrec'):
        name = tree[1]
        value = tree[3]
        body = tree[5]
        fixed_value = ('fix', ('lam', name, evaluate(value)))
        return evaluate(substitute(body, name, fixed_value))
    elif (tree[0] == 'fix'):
        f = evaluate(tree[1])
        if f[0] == 'lam':
            return evaluate(('app', f, ('fix', f)))
        return ('fix', f)
    elif (tree[0] == 'prog'):
        first_result = evaluate(tree[1])  
        second_result = evaluate(tree[2])  
        return (first_result, second_result)  
    elif (tree[0] == 'cons'):
        return ('cons', evaluate(tree[1]), evaluate(tree[2]))
    elif (tree[0] == 'hd'):
        list_val = evaluate(tree[1])
        if list_val[0] == 'cons':
            return list_val[1]
    elif (tree[0] == 'tl'):
        list_val = evaluate(tree[1])
        if list_val[0] == 'cons':
            return list_val[2]
    elif (tree[0] == 'nil'):
        return tree
    elif (tree[0] == 'num'):
        return tree
    else:
        result = tree
    return result

# generate a fresh name 
# needed eg for \y.x [y/x] --> \z.y where z is a fresh name)
class NameGenerator:
    def __init__(self):
        self.counter = 0

    def generate(self):
        self.counter += 1
        # user defined names start with lower case (see the grammar), thus 'Var' is fresh
        return 'Var' + str(self.counter)

name_generator = NameGenerator()

# for beta reduction (capture-avoiding substitution)
# 'replacement' for 'name' in 'tree'
def substitute(tree, name, replacement):
    # tree [replacement/name] = tree with all instances of 'name' replaced by 'replacement'
    if tree[0] == 'var':
        if tree[1] == name:
            return replacement # n [r/n] --> r
        else:
            return tree # x [r/n] --> x
    elif tree[0] == 'lam':
        if tree[1] == name:
            return tree # \n.e [r/n] --> \n.e
        else:
            fresh_name = name_generator.generate()
            return ('lam', fresh_name, substitute(substitute(tree[2], tree[1], ('var', fresh_name)), name, replacement))
            # \x.e [r/n] --> (\fresh.(e[fresh/x])) [r/n]
    elif tree[0] == 'app':
        return ('app', substitute(tree[1], name, replacement), substitute(tree[2], name, replacement))
    elif tree[0] == 'let':
        return ('let', tree[1], substitute(tree[2], name, replacement), substitute(tree[3], name, replacement))
    elif tree[0] == 'letrec':
        return ('letrec', tree[1], substitute(tree[2], name, replacement), substitute(tree[3], name, replacement))
    elif tree[0] == 'nil':
        return tree
    elif tree[0] == 'cons':
        return ('cons', substitute(tree[1], name, replacement), substitute(tree[2], name, replacement))
    elif tree[0] == 'hd':
        return ('hd', substitute(tree[1], name, replacement))
    elif tree[0] == 'tl':
        return ('tl', substitute(tree[1], name, replacement))
    else:
        raise Exception('Unknown tree', tree)

def linearize(ast):
    if ast[0] == 'var':
        return ast[1]
    elif ast[0] == 'lam':
        return "(" + "\\" + ast[1] + "." + linearize(ast[2]) + ")"
    elif ast[0] == 'app':
        return "(" + linearize(ast[1]) + " " + linearize(ast[2]) + ")"
    elif ast[0] == 'num':
        return str(ast[1])
    elif ast[0] == 'plus':
        return linearize(ast[1]) + " + " + linearize(ast[2])
    elif ast[0] == 'minus':
        return linearize(ast[1]) + " - " + linearize(ast[2])
    elif ast[0] == 'neg':
        return "-" + linearize(ast[1])
    elif ast[0] == 'multiply':
        return linearize(ast[1]) + " * " + linearize(ast[2])
    elif ast[0] == 'divide':
        return linearize(ast[1]) + " / " + linearize(ast[2])
    elif ast[0] == 'power':
        return linearize(ast[1]) + " ^ " + linearize(ast[2])
    elif ast[0] == 'log':
        return linearize(ast[1]) + " log " + linearize(ast[2]) + " base"
    elif ast[0] == 'if':
        return "if" + linearize(ast[1]) + "then" + linearize(ast[2]) + "else" + linearize(ast[3])  
    elif ast[0] == 'leq': 
        return linearize(ast[1]) + "<=" + linearize(ast[2])
    elif ast[0] == 'eq':
        return linearize(ast[1]) + "==" + linearize(ast[2])
    elif ast[0] == 'let': 
        return "let" + linearize(ast[1]) + "=" + linearize(ast[2]) + "in" + linearize(ast[3])
    elif ast[0] == 'rec': 
        return "letrec" + linearize(ast[1]) + "=" + linearize(ast[2]) + "in" + linearize(ast[3])
    elif ast[0] == 'fix':
        return "fix" + linearize(ast[1])
    elif ast[0] == 'prog':
        return linearize(ast[1]) + ";;" + linearize(ast[2])
    elif ast[0] == 'cons':
        return linearize(ast[1]) + ":" + linearize(ast[2])
    elif ast[0] == 'hd':
        return "hd" + linearize(ast[1])
    elif ast[0] == 'tl':
        return "tl" + linearize(ast[1])
    elif ast[0] == 'nil':
        return "#"
    else:
        return ast

def main():
    import sys
    if len(sys.argv) != 2:
        #print("Usage: python interpreter.py <filename or expression>", file=sys.stderr)
        sys.exit(1)

    input_arg = sys.argv[1]

    if os.path.isfile(input_arg):
        # If the input is a valid file path, read from the file
        with open(input_arg, 'r') as file:
            expression = file.read()
    else:
        # Otherwise, treat the input as a direct expression
        expression = input_arg

    result = interpret(expression)
    print(f"\033[95m{result}\033[0m")

if __name__ == "__main__":
    main()
