from typing import Tuple
from solver.dpllt import check_sat
from solver.modify import get_char_view, from_char_view_to_string_view, get_formula_from_model, get_variables_from_model, prepare_and_apply_simplify, update_whole_formula, rem_strings_from_my_string, modify
from solver.structures import Clause, Literal, SubstitutionTree, Node, Atom, My_String, Substitution
from copy import deepcopy

class Nielsen:
    #Считаем, что в качетсве литерала передается уже нужный литерал. 
    #Под нужным литералом подразумевается следуюшая конструкция (=(str.++ ..)(str.++ ..))
    def __init__(self, literal:Literal, initial_model) -> None:
        self.init_literal = literal
        root = Node(literal=deepcopy(literal), index=0, model=initial_model)
        self.tree = SubstitutionTree(root=root)
        self.initial_model = initial_model
        self.substitutions_map = {}


    def get_substitutions(self, atom:Atom):
        left, right = atom.my_string1, atom.my_string2
        first_left, first_right = None, None

        if left.stype == 'str.++':
            concat_str_left = left.concats_strs
            first_left = concat_str_left[0]
        elif left.stype == 'variable' or left.stype == 'const':
            first_left = left

        if right.stype == 'str.++':
            concat_str_right = right.concats_strs
            first_right = concat_str_right[0]
        elif right.stype == 'variable' or right.stype == 'const':
            first_right = right

        # if left.stype == 'str.++' and right.stype == 'str.++':
        #     concat_str_left = left.concats_strs
        #     concat_str_right = right.concats_strs

        #     first_left = concat_str_left[0]
        #     first_right = concat_str_right[0]

        
            
        if first_left.stype == 'variable':
            #xT1 = tT2, t - const and x - variable
            if first_right.stype == 'const':
                # if first_left.var_name not in self.substitutions_map:
                #     self.substitutions_map[first_left.var_name] = []
                # else:

                #x=tx'
                new_left = My_String(stype='variable', var_name=first_left.var_name + "'")
                subst1_str = My_String(stype='str.++', concats_strs=[deepcopy(first_right), new_left])
                #x=empty
                subst2_str = My_String(stype='const', cont='')

                subst = Substitution(variable_name=first_left.var_name, from_left=True)
                #(subst, flag) flag - может ли подстановка быть пустой
                subst.add_subst((subst1_str, True))
                subst.add_subst((subst2_str, True))
                # self.substitutions_map[first_left.var_name].append(subst)
                print('Подстановка')
                print(subst, end='\n\n')

                return [subst]

                # return [(first_left, (subst1, True), (subst2, True))]
            #xT1 = yT2,  x and y - variables    
            elif first_right.stype == 'variable':
                # subst_1, subst_2 = None, None
                if first_left.var_name not in self.substitutions_map:
                    self.substitutions_map[first_left.var_name] = []
                if first_right.var_name not in self.substitutions_map:
                    self.substitutions_map[first_right.var_name] = []
                #x = yx'
                new_left = My_String(stype='variable', var_name=first_left.var_name + "'")
                subst1_str = My_String(stype='str.++', concats_strs=[deepcopy(first_right), new_left])
                #y = xy'
                new_right = My_String(stype='variable', var_name=first_right.var_name + "'")
                subst2_str = My_String(stype='str.++', concats_strs=[deepcopy(first_left), new_right])
                #x = y
                subst3_str = My_String(stype='variable', var_name=first_right.var_name)

                subst_1 = Substitution(variable_name=first_left.var_name, from_left=True)
                subst_1.add_subst((subst1_str, False))
                subst_1.add_subst((subst3_str, True))
                # self.substitutions_map[first_left.var_name].append(subst_1)


                subst_2 = Substitution(variable_name=first_right.var_name)
                subst_2.add_subst((subst2_str, False))
                # self.substitutions_map[first_right.var_name].append(subst_2)
                print('Подстановка')
                print(subst_1)
                print(subst_2, end='\n\n')
                return [subst_1, subst_2]

        return []


    # def transformation(self, literal):
    #     # atom = deepcopy(self.init_literal.atom)
    #     atom = literal.atom
    #     substs = self.get_substitutions(atom)
    #     res = []

    #     for subst in substs:
    #         #new nodes in tree
    #         new_atoms = self.apply_substitution(atom, subst)
    #         # new_nodes = []
    #         for _atom in new_atoms:
    #             left_str, right_str = _atom.my_string1, _atom.my_string2

    #             # print(f'Before Simplify = {_atom}')
    #             left_str, right_str = self.simplify_strings(left_str=left_str, right_str=right_str)
    #             if left_str.stype == right_str.stype == 'const' and left_str.cont == right_str.cont == '':
    #                     continue
    #             _atom.my_string1, _atom.my_string2 = left_str, right_str
    #             # print(f'After Simplify = {_atom}')

    #             is_sat = False
    #             is_cycle = False

    #             if left_str == right_str:
    #                 is_sat = True
    #             elif self.check_cycle(atom, _atom):
    #                 is_cycle = True
    #             #Не забыть подставить в negation правильное значение
    #             new_atom = _atom
    #             res.append(new_atom)

    #     return res

    
    def remove_literal_from_model(self, model, literal_to_delete):
        for clause in model.clauses:
            if literal_to_delete in clause.literals:
                clause.literals.remove(literal_to_delete)
            atom = literal_to_delete.atom
            if atom in model.atoms:
                model.atoms.remove(atom)

            string1 = atom.my_string1
            string2 = atom.my_string2 
            if string1 in model.strings:
                model.strings.remove(string1)
            if string2 in model.strings:
                model.strings.remove(string2)

            rem_strings_from_my_string(model.strings_counter, string1)
            rem_strings_from_my_string(model.strings_counter, string2)

        for my_string, counter in model.strings_counter.items():
            if counter <= 0 and my_string in model.strings:
                model.strings.remove(my_string)

        model.strings_counter = dict(filter(lambda el: el[1] > 0, model.strings_counter.items()))

    
    def full_transformation(self, itterations):
        """Преобразование Нильсена сделаем следующим образом:

        1.Берём уравнение из входной модели, которое подходит под преобразование.

        2.Затем выполняем разбиение этого уравнения, то есть делаем ноды(детей).

        В каждой ноде также находится новая модель, которая соотвествует подстановке, то есть
        все уравнения преобразованы с учетом подстановки.

        Проверка на завершение преобразования будет означать, что у ребёнка больше переменных, чем у родителя.

        3.Если получаем цикл, то прекращаем путь, то есть не порождаем новые ноды.

        4.Если получили sat, то есть нашли решение, то удаляем уравнение и не порождаем новые ноды.

        Уравнение будем менять, если превысили кол-во итераций или переменных стало больше. 
        """
        stack = [self.tree.root]

        count = 0
        count_itterations = 0
        flag = False

        while len(stack) != 0:
            if flag and count_itterations >= itterations:
                print(count_itterations)
                return 'bad'
            count += 1
            node = stack.pop()
            print(count)
            # print(node)
            atom = node.literal.atom
            substs = self.get_substitutions(atom)

            # if len(substs) == 0:
            #     new_literal = Nielsen.find_literal(node.model.literals, node.literal)
            #     #В модели нет больше подходящих литералов
            #     if not new_literal or new_literal.atom == atom:
            #         continue
            #     print(f'FOUND LITERAL = {new_literal}')
            #     new_node = Node(literal=deepcopy(new_literal), parent=node, index=self.tree.actual_index, model=deepcopy(new_model_copy))

            #     node.children.append(new_node)
            #     self.tree.actual_index += 1

            #     # print(new_model_copy)

            #     stack.append(new_node)
            #     continue

            for subst in substs:
                print('Применяем подстановку')
                print(atom)
                print('Подстановка:')
                print('\t' + str(subst))
                new_atoms = self.apply_substitution(deepcopy(atom), subst)
                for _atom in new_atoms:
                    print(_atom)
                print('Конец')
                new_models = self.apply_substitutions_and_get_new_models(node.model, subst)

                for new_model, _atom in zip(new_models, new_atoms):
                    # print(_atom)
                    literal_before = Literal(atom=deepcopy(_atom), negation=node.literal.negation)
                    count_itterations += 1

                    left_str, right_str = _atom.my_string1, _atom.my_string2

                    # print(f'Before Simplify = {_atom}')
                    left_str, right_str = self.simplify_strings(left_str=left_str, right_str=right_str)
                    _atom.my_string1, _atom.my_string2 = left_str, right_str
                    # print(f'After Simplify = {_atom}')

                    is_sat = False
                    is_cycle = False

                    if left_str == right_str:
                        is_sat = True
                    elif self.check_cycle(atom, _atom):
                        is_cycle = True
                    
                    if is_sat:
                        self.remove_literal_from_model(new_model, literal_before)

                    if is_cycle:
                        continue

                    new_model_copy = deepcopy(new_model)
                    is_changed = modify(new_model_copy)
                    res, model = check_sat(new_model_copy)
                    new_model_copy = get_formula_from_model(model)
                    # print(new_model_copy)
                    while True:
                        # print('FORMULA BEFORE MODIFY')
                        # print(new_model_copy)
                        is_changed = modify(new_model_copy)
                        # print('FORMULA AFTER MODIFY')
                        # print(new_model_copy)
                        if not is_changed:
                            break
                        res, model = check_sat(new_model_copy)
                        new_model_copy = get_formula_from_model(model)
                        # print(new_model_copy)
                    
                    initial_formula = node.parent.model if node.parent else node.model

                    init_variables = get_variables_from_model(initial_formula.literals)
                    variables = get_variables_from_model(new_model_copy.literals)

                    if variables > init_variables:
                        flag = True

                    
                    new_literal = Literal(atom=deepcopy(_atom), negation=node.literal.negation)
                    if new_literal not in new_model_copy.literals:
                        new_literal = Nielsen.find_literal(new_model_copy.literals)
                        #В модели нет больше подходящих литералов
                        if not new_literal:
                            continue
                        print(f'FOUND LITERAL = {new_literal}')

                    new_node = Node(literal=deepcopy(new_literal), parent=node, index=self.tree.actual_index, sat_marker=is_sat, cycle_marker=is_cycle, model=deepcopy(new_model_copy))

                    node.children.append(new_node)
                    self.tree.actual_index += 1

                    # print(new_model_copy)

                    stack.append(new_node)
            

        if flag:
            return 'bad'

        return 'good'


    def apply_substitution(self, atom: Atom, subst: Substitution) -> Atom:
        new_atoms = []
        var_name = subst.variable_name

        for sub in subst.substs:
            new_atom = deepcopy(atom)
            #Нужно менять и слева, и справа, так как могут быть и там, и там одинаковые переменные
            equation_element = new_atom.my_string1 
            self.change_equation(new_atom.my_string1, var_name, sub)
            equation_element = new_atom.my_string2 
            self.change_equation(new_atom.my_string2 , var_name, sub)
            new_atoms.append(new_atom)

        return new_atoms 


    def apply_substitutions_and_get_new_models(self, model, subst):
        new_models = []
        var_name = subst.variable_name

        for sub in subst.substs:
            new_model = self.apply_substitution_for_whole_model(deepcopy(model), var_name, sub)
            new_models.append(new_model)

        return new_models


    def apply_substitution_for_whole_model(self, model, var_name, sub):
        copy_formula = {}
        new_clauses = []

        for idx, clause in enumerate(model.clauses):
            for literal in clause.literals:
                atom = literal.atom
                # for sub in subst.substs:
                new_atom = deepcopy(atom)
                equation_element = new_atom.my_string1 
                self.change_equation(equation_element, var_name, sub)
                equation_element = new_atom.my_string2 
                self.change_equation(equation_element, var_name, sub)
                if new_atom == atom:
                    continue
                if idx not in copy_formula:
                    copy_formula[idx] = deepcopy(clause)
                if literal in copy_formula[idx].literals:
                    copy_formula[idx].literals.remove(literal)
                if not literal.negation:
                    new_literals = [Literal(atom=deepcopy(new_atom), negation=False)]
                    copy_formula[idx].literals.extend(new_literals)
                else:
                    new_literals = [Literal(atom=deepcopy(new_atom), negation=True)]
                    new_clauses.extend([Clause(literals=[deepcopy(_literal)]) for _literal in new_literals])

        
        update_whole_formula(copy_formula, model, new_clauses)

        return model


    def go_inside_my_string(self, my_string, var_name, sub_str):
        stype = my_string.stype

        if stype == 'variable':
            if my_string.var_name == var_name:
                if sub_str.stype == 'str.++':
                    my_string.stype = 'str.++'
                    my_string.concats_strs = sub_str.concats_strs
                    my_string.var_name = None
                else:
                    my_string.var_name = sub_str.var_name
        elif stype != 'const':
            if my_string.concats_strs:
                for i, _str in enumerate(my_string.concats_strs):
                    if _str.stype == 'variable' and _str.var_name == var_name:
                        if sub_str.stype == 'str.++':
                            my_string.concats_strs[i:i+1] = deepcopy(sub_str.concats_strs)
                        else:
                             my_string.concats_strs[i] = deepcopy(sub_str)
                    elif _str.stype != 'const':
                        self.go_inside_my_string(_str, var_name, sub_str)

            if my_string.replace_strs:
                for _str in my_string.replace_strs:
                    self.go_inside_my_string(_str, var_name, sub_str)


    def change_equation(self, eq_el: My_String | None, var_name, sub: Tuple[My_String, bool]):
        #Рекурсивно производим замену
        sub_str = sub[0]

        self.go_inside_my_string(eq_el, var_name, sub_str)


    def check_cycle(self, parent_atom: Atom, child_atom: Atom):
        left_parent, right_parent = parent_atom.my_string1, parent_atom.my_string2
        left_child, right_child = child_atom.my_string1, child_atom.my_string2

        return My_String.extend_eq(left_parent, left_child) and My_String.extend_eq(right_parent, right_child)


    def get_solutions(self):
        #Необходимые собрать все подстановки, которые привели к решению. 
        #То есть к ноде с маркером node.sat_marker = True
        pass

    
    def simplify_strings(self, left_str: My_String, right_str: My_String):
        l_char_view, r_char_view = get_char_view(left_str), get_char_view(right_str)
        prepare_and_apply_simplify(l_char_view, r_char_view)
        left_str = from_char_view_to_string_view(l_char_view)
        right_str = from_char_view_to_string_view(r_char_view)

        return left_str, right_str

    
    @staticmethod
    def find_literal(literals, not_found=None):
        for literal in literals:
            # print(f'{str(literal)}, {Nielsen.check_literal(literal)}')
            if Nielsen.check_literal(literal):
                if not not_found or literal != not_found:
                    return literal

        return None


    @staticmethod
    #Проверяем, что литерал может подойти под преобразование Нильсена.
    #Считаем, что подойдут все варианты, кроме вариантов с единственным(и) str.replace(_all)
    #в одной или каждой сторонe.
    def check_literal(literal:Literal):
        atom = literal.atom
        left, right = atom.my_string1, atom.my_string2

        if atom.ltype != '=':
            return False

        if left.stype == 'str.replace' or left.stype == 'str.replace_all':
            return False

        if right.stype == 'str.replace' or right.stype == 'str.replace_all':
            return False
        
        return True


