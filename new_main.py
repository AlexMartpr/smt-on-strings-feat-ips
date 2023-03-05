# from subprocess import Popen, PIPE, STDOUT, run
import argparse

from solver.dpllt import check_sat
from solver.formula_generator import Generator
from solver.parser import Parser
from solver.modify import modify, get_formula_from_model
from solver.nielsen import Nielsen



def algorithm(f, its):
    modify(f)
    print('FORMULA AFTER MODIFY')
    print(f)
    # exit(-1)
    res, model = check_sat(f)
    f = get_formula_from_model(model)
    # print('MODEL FROM DPLL')
    # for literal in model:
    #     print(literal)
    literal = Nielsen.find_literal(f.literals)
    if literal:
        nielsen = Nielsen(literal=literal, initial_model=f)
        res = nielsen.full_transformation(its)

    print(res)


def main():
    parser_args = argparse.ArgumentParser()
    parser_args.add_argument('-i', type=int, dest='itterations', default=10)

    args = parser_args.parse_args()
    its = args.itterations

    # f = Generator().generate().to_formula()
    # p = Parser('tests/dpllt_tests/test_1.smt2')
    # p = Parser('tests/parser_tests/test_10.smt2')
    p = Parser('tests/modification_tests/test_01.smt2')
    # p = Parser('tests/nielsen_tests/test2.smt2')
    f = p.to_formula()
    algorithm(f, its)
    print()


if __name__ == '__main__':
    main()