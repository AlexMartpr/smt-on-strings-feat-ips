# from subprocess import Popen, PIPE, STDOUT, run
from solver.dpllt import check_sat
from solver.formula_generator import Generator
# from solver.lia import Lia_Formula
from solver.parser import Parser
# from solver.structures import *


# f = Generator().generate().to_formula()
p = Parser('tests/dpllt_tests/test_1.smt2')
f = p.to_formula()
print(f)
# f.print_dpll_view()
print()
result, model = check_sat(f)
print(result)

# dot_strings = []
# result = check_sat(f, dot_strings=dot_strings)

# s = 'digraph G {\n    ' + '\n    '.join([ds for ds in dot_strings]) + '\n}}'

# print(result)

# p = Popen(['dot', '-Tsvg', '-ograph.svg'], stdout=PIPE, stdin=PIPE, stderr=STDOUT)    
# p.communicate(input=bytes(s, encoding='utf8'))[0]
# run(['display', 'graph.svg'])