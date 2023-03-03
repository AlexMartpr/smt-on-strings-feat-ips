import context 
from solver.nielsen import Nielsen
from solver.parser import Parser

p = Parser('nielsen_tests/test2.smt2')
f = p.to_formula()
print(f)
literal = f.literals[0]
nielsen = Nielsen(literal=literal)
nielsen.transformation()
tree = nielsen.tree
print(tree.root)
