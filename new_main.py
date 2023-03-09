# from subprocess import Popen, PIPE, STDOUT, run
import argparse
from copy import deepcopy

from solver.dpllt import check_sat
from solver.formula_generator import Generator
from solver.parser import Parser
from solver.modify import modify, get_formula_from_model
from solver.nielsen import Nielsen



def algorithm(f, its):
    modify(f)
    print('FORMULA AFTER MODIFY')
    print(f)
    res, model = check_sat(f)
    f = get_formula_from_model(model)
    # print('MODEL FROM DPLL')
    # for literal in model:
    #     print(literal)
    literals = deepcopy(f.literals)
    possible_literals = []
    while len(literals) > 0:
        literal = Nielsen.find_literal(literals)
        if literal and literal not in possible_literals:
            possible_literals.append(literal)
        literals = literals[1:]

    models = []
    sum_res = []
    if len(possible_literals) > 0:
        for literal in possible_literals:
            nielsen = Nielsen(literal=literal, initial_model=f)
            res, _models = nielsen.full_transformation(its)
            sum_res.append(res)
            if res:
                models.extend(_models)            


    if any(sum_res):
        print('Модель имеет непротиворечивые разбиения')
        new_models = []
        # print(len(models))
        for idx, model in enumerate(models):
            flag = False
            for i in range(idx +1, len(models)):
                _flag = False
                if len(model.clauses) == len(models[i].clauses):
                    for clause, _clause in zip(model.clauses, models[i].clauses):
                        if clause == _clause:
                            _flag = True
                        else:
                            _flag = False
                            break
                    if _flag:
                        flag = True
                        break

            if not flag:
                new_models.append(model)

        # for idx, model in enumerate(new_models):
        #     print(f'Модель #{idx + 1}')
        #     print(model)

        if len(new_models) == 0:
            print('Разбиение привело к пустой модели')
    else:
        print('Модель противоречива')

    # if literal:
    #     nielsen = Nielsen(literal=literal, initial_model=f)
    #     res = nielsen.full_transformation(its)

    # print(res)


def main():
    parser_args = argparse.ArgumentParser()
    parser_args.add_argument('-i', type=int, dest='itterations', default=10)

    args = parser_args.parse_args()
    its = args.itterations

    # f = Generator().generate().to_formula()
    # p = Parser('tests/dpllt_tests/test_1.smt2')
    # p = Parser('tests/parser_tests/test_10.smt2')
    p = Parser('tests/modification_tests/test_03.smt2')
    # p = Parser('tests/nielsen_tests/test2.smt2')
    f = p.to_formula()
    algorithm(f, its)
    print()


if __name__ == '__main__':
    main()