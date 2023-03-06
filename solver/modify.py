from copy import deepcopy
from solver.structures import Formula, My_String, Literal, Atom, Clause


is_changed = False


def set_is_changed(flag: bool):
    global is_changed
    is_changed = flag


def get_variables_from_model(model):
    global variables
    variables = 0

    def go_inside_my_string(my_string):
        global variables
        stype = my_string.stype

        if stype == 'variable':
            variables += 1
        elif stype != 'const':
            if my_string.concats_strs:
                for _str in my_string.concats_strs:
                    go_inside_my_string(_str)

            if my_string.replace_strs:
                for _str in my_string.replace_strs:
                    go_inside_my_string(_str) 


    for literal in model:
        atom = literal.atom
        left_str, right_str = atom.my_string1, atom.my_string2
        go_inside_my_string(left_str)
        go_inside_my_string(right_str)

    return variables


def get_formula_from_model(model):
    formula = Formula(
        strings=[],
        atoms=[deepcopy(literal.atom) for literal in model],
        literals=deepcopy(model),
        clauses=[Clause(literals=[deepcopy(literal) for literal in model])],
        strings_counter={}
    )

    for clause in formula.clauses:
        for literal in clause.literals:
            atom = literal.atom
            if atom not in formula.atoms:
                formula.atoms.append(atom)
            if literal not in formula.literals:
                formula.literals.append(literal)
            my_string1 = atom.my_string1
            my_string2 = atom.my_string2

            add_strings_from_my_string(formula.strings_counter, my_string1)
            add_strings_from_my_string(formula.strings_counter, my_string2)

            if my_string1 not in formula.strings:
                formula.strings.append(my_string1)
            if my_string2 not in formula.strings:
                formula.strings.append(my_string2)

    return formula


def get_char_view_word(eq):
    for el in eq:
        yield el 

    yield None


def get_char_view(my_str: My_String):
    view = []
    if my_str.concats_strs:
        for _str in my_str.concats_strs:
            if _str.stype == 'const':
                if len(_str.cont) == 0:
                    view.append(('char', ''))
                else:
                    view.extend([('char', val) for val in _str.cont])
                # view.extend([('char', val, False) for val in _str.cont[:-1]])
                # view.append(('char', _str.cont[-1], True)) 
            elif _str.stype == 'variable':
                view.append(('variable',  _str.var_name))
            else:
                view = []
                break
    else:               
        if my_str.stype == 'const':
            if len(my_str.cont) == 0:
                view.append(('char', ''))
            else:
                view.extend([('char', val) for val in my_str.cont])
            # view.extend([('char', val) for val in my_str.cont[:-1]])
            # view.append(('char', my_str.cont[-1], True)) 
        elif my_str.stype == 'variable':
            view.append(('variable', my_str.var_name))
        else:
            view = []

    return view


def check_conflict(left_char_view, right_char_view):
    # print('CHECK CONFLICT')
    # print(left_char_view)
    # print(right_char_view)
    first_el_l, first_el_r = left_char_view[0], right_char_view[0]

    if first_el_r[0] != 'char' or first_el_l[0] != 'char':
        return False, [[]], [[]]

    cut_l = [[]]
    cut_r = [[]]

    left_copy = deepcopy(left_char_view)
    right_copy = deepcopy(right_char_view)

    i = 0
    cut_idx = 0
    flag = False

    while True:
        if i >= len(left_copy) or i >= len(right_copy):
            break

        el_l, el_r = left_copy[i], right_copy[i]
        type_el_l, val_el_l = el_l[0], el_l[1]
        type_el_r, val_el_r = el_r[0], el_r[1]

        if type_el_l != 'char' or type_el_r != 'char':
            break
        # print(val_el_l)
        # print(val_el_r)
        if val_el_l != val_el_r:
            flag = True
            cut_l[cut_idx].append(val_el_l)
            cut_r[cut_idx].append(val_el_r)
        else:
            left_copy = left_copy[len(cut_l):]
            right_copy = right_copy[len(cut_r):]
            simplify(left_copy, right_copy)
            i = 0
            cut_idx += 1
            cut_l.append([])
            cut_r.append([])

        i += 1

    left_char_view[:] = left_copy
    right_char_view[:] = right_copy

    return flag, cut_l, cut_r


def prepare_and_check_conflict(left_char_view, right_char_view):
    flag, cut_l, cut_r = check_conflict(left_char_view,  right_char_view)
    left_char_view[:] = left_char_view[::-1]
    right_char_view[:] = right_char_view[::-1]
    if len(left_char_view) == 0 and len(right_char_view) == 0:
        return True, [[]], [[]], [[]], [[]]
    if len(left_char_view) == 0:
        left_char_view.append(('char', ''))
    elif len(right_char_view) == 0:
        right_char_view.append(('char', ''))    
    r_flag, r_cut_l, r_cut_r = check_conflict(left_char_view, right_char_view)
    left_char_view[:] = left_char_view[::-1]
    right_char_view[:] = right_char_view[::-1]

    # if len(left_char_view) == 0:
    #     left_char_view.append(('char', ''))
    
    # if len(right_char_view) == 0:
    #     right_char_view.append(('char', ''))

    flag |= r_flag

    return flag, cut_l, cut_r, r_cut_l, r_cut_r


def simplify(left, right):
    global is_changed
    idx = 0

    for (left_char, right_char) in zip(left, right):
        # print(str(left_char))
        # print(str(right_char))
        type_left = left_char[0]
        view_left = left_char[1]
        type_right = right_char[0]
        view_right = right_char[1]

        if type_left == type_right and view_left == view_right:
            # print('YES YES')
            is_changed = True
            idx += 1
        else:
            break

    left[:] = left[idx:]
    right[:] = right[idx:]

    # print(left)
    # print(right)
    # return left, right


def prepare_and_apply_simplify(left, right):
    # print('BEFORE SIMPLIFY')
    # print(left)
    # print(right)
    simplify(left, right)
    left[:] = left[::-1]
    right[:] = right[::-1]
    simplify(left, right)
    left[:] = left[::-1]
    right[:] = right[::-1]
    # print('AFTER SIMPLIFY')
    # print(left)
    # print(right)

    # if len(left) == 0:
    #     left.append(('char', ''))
    
    # if len(right) == 0:
    #     right.append(('char', ''))


def rem_strings_from_my_string(strings_counter, my_string):
    if my_string in strings_counter:
        strings_counter[my_string] -= 1

    if my_string.concats_strs:
        for _str in my_string.concats_strs:
            rem_strings_from_my_string(strings_counter, _str)

    if my_string.replace_strs:
        for _str in my_string.replace_strs:
            rem_strings_from_my_string(strings_counter, _str)


def add_strings_from_my_string(strings_counter, my_string):
    if my_string not in strings_counter:
        strings_counter[my_string] = 1
    else:
        strings_counter[my_string] += 1

    if my_string.concats_strs:
        for _str in my_string.concats_strs:
            add_strings_from_my_string(strings_counter, _str)

    if my_string.replace_strs:
        for _str in my_string.replace_strs:
            add_strings_from_my_string(strings_counter, _str)  


def update_whole_formula(copy_formula, formula, new_clauses):
    # print('COPY FORMULA')
    # for k, v in copy_formula.items():
    #     print(k)
    #     print(v)
    # print(copy_formula)
    for clause_idx, clause in copy_formula.items():
        # print(clause_idx)
        # print(formula.clauses[clause_idx])
        #Delete
        for literal in formula.clauses[clause_idx].literals:
            atom = literal.atom
            my_string1 = atom.my_string1
            my_string2 = atom.my_string2
            # print(my_string1)

            rem_strings_from_my_string(formula.strings_counter, my_string1)
            rem_strings_from_my_string(formula.strings_counter, my_string2)

            if my_string1 in formula.strings:
                formula.strings.remove(my_string1)
            if my_string2 in formula.strings:
                formula.strings.remove(my_string2)
            if atom in formula.atoms:
                formula.atoms.remove(atom)
            if literal in formula.literals:
                formula.literals.remove(literal)

        formula.clauses[clause_idx] = clause

        #Update
        for literal in clause.literals:
            atom = literal.atom
            if atom not in formula.atoms:
                formula.atoms.append(atom)
            if literal not in formula.literals:
                formula.literals.append(literal)
            my_string1 = atom.my_string1
            my_string2 = atom.my_string2

            add_strings_from_my_string(formula.strings_counter, my_string1)
            add_strings_from_my_string(formula.strings_counter, my_string2)

            if my_string1 not in formula.strings:
                formula.strings.append(my_string1)
            if my_string2 not in formula.strings:
                formula.strings.append(my_string2)

    formula.clauses = list(filter(lambda x: len(x.literals) > 0, formula.clauses))
    d = {}
    for idx, clause in enumerate(formula.clauses):
        if clause in d:
            formula.clauses.pop(idx)
        else:
            d[clause] = None
    d = {}
    for idx, literal in enumerate(formula.literals):
        if literal in d:
            formula.literals.pop(idx)
        else:
            d[literal] = None 
            
    for clause in new_clauses:
        #Update
        for literal in clause.literals:
            atom = literal.atom
            if atom not in formula.atoms:
                formula.atoms.append(atom)
            if literal not in formula.literals:
                formula.literals.append(literal)
            my_string1 = atom.my_string1
            my_string2 = atom.my_string2

            add_strings_from_my_string(formula.strings_counter, my_string1)
            add_strings_from_my_string(formula.strings_counter, my_string2)

            if my_string1 not in formula.strings:
                formula.strings.append(my_string1)
            if my_string2 not in formula.strings:
                formula.strings.append(my_string2)

    formula.clauses.extend(new_clauses)

    d = {}
    for idx, clause in enumerate(formula.clauses):
        if clause in d:
            formula.clauses.pop(idx)
        else:
            d[clause] = None
    d = {}
    for idx, literal in enumerate(formula.literals):
        if literal in d:
            formula.literals.pop(idx)
        else:
            d[literal] = None 

    for literal in formula.literals:
        exists = True
        for clause in formula.clauses:
            if literal not in clause.literals:
                exists = False
            else:
                exists = True
                break 
        if not exists:
            atom = literal.atom
            exists_atom = False
            formula.literals.remove(literal)
            for _literal in formula.literals:
                if atom == _literal.atom:
                    exists = True
                    break
            if not exists_atom:
                if atom in formula.atoms:
                    formula.atoms.remove(atom)
                my_str1, my_str2 = atom.my_string1, atom.my_string2
                rem_strings_from_my_string(formula.strings_counter, my_str1)
                rem_strings_from_my_string(formula.strings_counter, my_str2)

    for my_string, counter in formula.strings_counter.items():
        if counter <= 0 and my_string in formula.strings:
            formula.strings.remove(my_string)

    formula.strings_counter = dict(filter(lambda el: el[1] > 0, formula.strings_counter.items()))

    letter = ord('A')
    formula.simple_atmoms = {}
    for atom in formula.atoms:
        formula.simple_atmoms[atom] = chr(letter)
        letter += 1
    # print('ATOMS')
    # for atom in formula.atoms:
    #     print(atom)
    # print('LITERALS')
    # for literal in formula.literals:
    #     print(literal)

    # formula.literals.sort(key=lambda x: formula.simple_atmoms[x.atom])


def modify(formula):
    global is_changed
    is_changed = False
    copy_formula = {}
    res = {}
    new_clauses = []
    before_formula = deepcopy(formula)

    for idx, clause in enumerate(formula.clauses):
        # print('CLAUS: \n' + str(clause))
        for literal in clause.literals:
            atom = literal.atom
            # print('LITERAL: \n' + str(literal))
            # print('ATOM: \n' + str(atom))
            if atom.ltype == '=':
                left_str = atom.my_string1
                right_str = atom.my_string2
                if 'str.replace' not in left_str.stype and 'str.replace' not in right_str.stype:
                # if left_str.stype == 'str.++' or right_str.stype == 'str.++':
                    if idx not in copy_formula:
                        copy_formula[idx] = deepcopy(clause)
                    print('LITERAL: \n' + str(literal))
                    # print('ATOM: \n' + str(atom))
                    
                    char_view_left = get_char_view(left_str)
                    char_view_right = get_char_view(right_str)
                    
                    # print('LEFT CHAR VIEW: ' + str(char_view_left))
                    # print('RIGHT CHAR VIEW: ' + str(char_view_right))

                    res['clause'] = clause
                    res['literal'] = literal
                    res['left'] = char_view_left
                    res['right'] = char_view_right
                    res['clause_idx'] = idx
                    rt = cutting(copy_formula, res)
                    # new_clauses.extend(list(dict.fromkeys(rt)))
                    new_clauses.extend(rt)
            elif check_contains_need_normalize(literal):
                    is_changed = True
                    if idx not in copy_formula:
                        copy_formula[idx] = deepcopy(clause)

                    to_delete, more_clauses, more_literals = normalize_contains(literal)

                    if literal in copy_formula[idx].literals:
                        copy_formula[idx].literals.remove(literal)

                    if not to_delete:
                        # new_clauses.extend(list(dict.fromkeys(more_clauses)))
                        new_clauses.extend(more_clauses)
                        if literal in copy_formula[idx].literals:
                            copy_formula[idx].literals.remove(literal)
                        copy_formula[idx].literals.extend(more_literals)
                        # copy_formula[idx].literals.extend(list(dict.fromkeys(more_literals)))
                    

    # print('NEW CLAUSES')
    # for clause in new_clauses:
    #     print(clause)
    
    update_whole_formula(copy_formula, formula, new_clauses)

    if formula.clauses == before_formula.clauses:
        return False

    return True

    # return is_changed
             

def add_multi(element, multiset):
    type_element = element[0]
    view_element = element[1]

    if type_element == 'char':
        if 'const' not in multiset:
            multiset['const'] = {'count': 1, 'val': view_element}
        else:
            multiset['const']['count'] += 1
            multiset['const']['val'] += str(view_element)

    elif type_element == 'variable':
        if view_element not in multiset:
            multiset[view_element] = 1
        else:
            multiset[view_element] += 1


def from_char_view_to_string_view(char_view):
    concat_strs = []

    str_view = ''
    is_empty_char = False

    if len(char_view) == 0:
        return My_String(stype='const', cont='')

    for char in char_view:
        char_type = char[0]
        char_view = char[1]
        
        if char_type == 'char':
            if char_view == '':
                is_empty_char = True

            str_view += char_view

            # if char[2]:
            #     concat_strs.append(My_String(stype='const', cont=str_view))
        else:
            if len(str_view)!=0:
                concat_strs.append(My_String(stype='const', cont=str_view))
                str_view = ''
            concat_strs.append(My_String(stype='variable', var_name=char_view))

    if is_empty_char or len(str_view)!=0:
        concat_strs.append(My_String(stype='const', cont=str_view))

    if len(concat_strs) == 1:
        el = concat_strs[0]
        return el 

    return My_String(stype='str.++', concats_strs=concat_strs)


def get_char_view_from_multi(multi):
    char_view = []

    for key, val in multi.items():
        if key == 'const':
            str_view = val['val']
            for ch in str_view:
                char_view.append(('char', ch))
        else:
            for _ in range(val):
                char_view.append(('variable', key))

    return char_view


def split(mult_l, mult_r) -> Atom:
    print('SPLIT')
    my_str1 = get_char_view_from_multi(mult_l)
    my_str2 = get_char_view_from_multi(mult_r)

    if len(my_str1) == 0 and len(my_str2) == 0:
        return None

    my_str1 = from_char_view_to_string_view(my_str1)
    my_str2 = from_char_view_to_string_view(my_str2)
    print(str(my_str1))
    print(str(my_str2))

    return Atom(ltype='=', my_string1=my_str1, my_string2=my_str2)


def left_right_itteration(left, right):
    multiset_l = {}
    multiset_r = {}
    new_atoms = []

    # print('LEFT = ' + str(left))
    # print('RIHT = ' + str(right))

    #L->R
    idx = 0
    for (w_l, w_r) in zip(get_char_view_word(left), get_char_view_word(right)):
        #нужная последняя проверка на split
        if w_l is None or w_r is None:
            break

        idx += 1
        # print('ELEMENT LEFT = ' + str(w_l))
        # print('ELEMENT RIGHT = ' + str(w_r))

        add_multi(w_l, multiset_l)
        add_multi(w_r, multiset_r)

        if multiset_l == multiset_r:
            atom = split(multiset_l, multiset_r)
            print(atom)
            # упрощение после разрезания
            left[:] = left[idx:]
            right[:] = right[idx:]
            prepare_and_apply_simplify(left, right)

            multiset_l = {}
            multiset_r = {}
            idx = 0
            if atom is not None:
                new_atoms.append(atom)
                print('NEW ATOM: ' + str(atom))
        
        # idx += 1

    return new_atoms


def cutting(copy_formula, eq):
    global is_changed
    new_clauses = []
    is_changed = False

    if len(eq['left']) == 0:
        return new_clauses

    clause = eq['clause']
    literal = eq['literal']
    left, right = eq['left'], eq['right']
    idx = eq['clause_idx']
    negation = literal.negation

    prepare_and_apply_simplify(left, right)
    #Если после упрощения ничего не осталось
    # if len(left) == len(right) == 1:
    #     left_type = left[0][0]
    #     right_type = right[0][0]
    #     left_val = left[0][1]
    #     right_val = right[0][1]

    #     if left_type == right_type == 'char' and left_val == right_val == '':
    #         if literal in copy_formula[idx].literals:
    #             copy_formula[idx].literals.remove(literal)
    #         return new_clauses

    if len(left) == len(right) == 0:
        # print("EQUAL")
        # print(literal)
        if literal in copy_formula[idx].literals:
            copy_formula[idx].literals.remove(literal)
        return new_clauses

    if len(left) == 0:
        left.append(('char', ''))
    elif len(right) == 0:
        right.append(('char', ''))

    to_delete, cut_l, cut_r, r_cut_l, r_cut_r = prepare_and_check_conflict(left, right)
    # print('TO DELETE: ' + str(to_delete))
    # print(left)
    # print(right)
    
    #Удаляем полностью правило
    if to_delete and not negation:
        is_changed = True
        if literal in copy_formula[idx].literals:
            copy_formula[idx].literals.remove(literal)
        return new_clauses

    # Оставляем правило, но удаляем не равные и равные буквы
    if to_delete and negation:
        while len(left) > 0 and len(right) > 0 and (left[0][0] != 'variable' or right[0][0] != 'variable'):
            left = left[1:]
            right = right[1:]

        if len(left) == 0 and len(right) == 0:
            if literal in copy_formula[idx].literals:
                copy_formula[idx].literals.remove(literal)
            return new_clauses

        # if len(left) == 0:
        #     left.append(('char', ''))

        # if len(right) == 0:
        #     right.append(('char', ''))

        left = left[::-1]
        right = right[::-1]

        while len(left) > 0 and len(right) > 0 and (left[0][0] != 'variable' or right[0][0] != 'variable'):
            left = left[1:]
            right = right[1:]


        if len(left) == 0 and len(right) == 0:
            if literal in copy_formula[idx].literals:
                copy_formula[idx].literals.remove(literal)
            return new_clauses

        # if len(left) == 0:
        #     left.append(('char', ''))

        # if len(right) == 0:
        #     right.append(('char', ''))

        left = left[::-1]
        right = right[::-1]

    new_atoms = left_right_itteration(left, right)
    # new_atoms = new_atoms[:len(new_atoms) - 1]
    # print('left_right_itteration')
    # print(left)
    # print(right)

    #R -> L
    left = left[::-1]
    right = right[::-1]
    new_atoms.extend(left_right_itteration(left, right))
    left = left[::-1]
    right = right[::-1]
    # print('reverse left_right_itteration')
    # print(left)
    # print(right)

    # print(new_atoms)

    #Оставшаяся часть после разрезания
    if len(left) != 0 or len(right) != 0:
        if len(left) == 0:
            left.append(('char', ''))
        elif len(right) == 0:
            right.append(('char', ''))
        # flag = False
        # if len(left) == 1 and len(right) == 1:
        #     left_type = left[0][0]
        #     right_type = right[0][0]
        #     left_val = left[0][1]
        #     right_val = right[0][1]

        #     if left_type == 'char' and right_type == 'char' and left_val == '' and right_val == '':
        #         flag = True

        # if not flag:
        #     last_left = from_char_view_to_string_view(left)   
        #     last_right = from_char_view_to_string_view(right)
        #     atom = Atom(ltype='=', my_string1=last_left, my_string2=last_right)
        #     if atom != literal.atom:
        #         new_atoms.append(atom)
        #         print('NEW ATOM: ' + str(atom))

        to_delete, cut_l, cut_r, r_cut_l, r_cut_r = prepare_and_check_conflict(left, right)
        print('TO DELETE: ' + str(to_delete))
        # print(left)
        # print(right)
        
        #Удаляем полностью правило
        if to_delete and not negation:
            is_changed = True
            if literal in copy_formula[idx].literals:
                copy_formula[idx].literals.remove(literal)
            return new_clauses

        # Оставляем правило, но удаляем не равные и равные буквы
        if to_delete and negation:
            while len(left) > 0 and len(right) > 0 and (left[0][0] != 'variable' or right[0][0] != 'variable'):
                left = left[1:]
                right = right[1:]

            if len(left) == 0 and len(right) == 0:
                if literal in copy_formula[idx].literals:
                    copy_formula[idx].literals.remove(literal)
                return new_clauses

            # if len(left) == 0:
            #     left.append(('char', ''))

            # if len(right) == 0:
            #     right.append(('char', ''))

            left = left[::-1]
            right = right[::-1]

            while len(left) > 0 and len(right) > 0 and (left[0][0] != 'variable' or right[0][0] != 'variable'):
                left = left[1:]
                right = right[1:]


            if len(left) == 0 and len(right) == 0:
                if literal in copy_formula[idx].literals:
                    copy_formula[idx].literals.remove(literal)
                return new_clauses

            # if len(left) == 0:
            #     left.append(('char', ''))

            # if len(right) == 0:
            #     right.append(('char', ''))

            left = left[::-1]
            right = right[::-1]

        if len(left) > 0 or len(right) > 0:
            if len(left) == 0:
                left.append(('char', ''))
            elif  len(right) == 0:
                right.append(('char', ''))
        last_left = from_char_view_to_string_view(left)   
        last_right = from_char_view_to_string_view(right)
        atom = Atom(ltype='=', my_string1=last_left, my_string2=last_right)
        if atom != literal.atom:
            new_atoms.append(atom)
            print('NEW ATOM: ' + str(atom))

    if len(new_atoms) > 0:
        is_changed = True
    else:
        return new_clauses

    if literal in copy_formula[idx].literals:
        copy_formula[idx].literals.remove(literal)
    
    if negation:
        # if literal in copy_formula[idx].literals:
        #     copy_formula[idx].literals.remove(literal)
        new_literals = [Literal(atom=deepcopy(_atom), negation=True) for _atom in new_atoms]
        copy_formula[idx].literals.extend(new_literals) 
    else:
        new_literals = [Literal(atom=deepcopy(_atom), negation=False) for _atom in new_atoms]
        new_clauses.extend([Clause(literals=[deepcopy(_literal)]) for _literal in new_literals])

    return new_clauses


def overlap(Q_1, Q_2):
    if Q_2 in Q_1 or Q_1 == Q_2:
        return 'full'
    
    if Q_1 in Q_2:
        return 'partial'

    #prefix Q_1 and suffix Q_2
    q_1, q_2 = Q_1[0], Q_2[-1]
    if q_1 == q_2:
            return 'partial'
    # for q_1, q_2 in zip(Q_1, Q_2[::-1]):
    #     if q_1 == q_2:
    #         return 'partial'
    #     else:
    #         break

    #suffix Q_1 and prefix Q_2
    q_1, q_2 = Q_1[-1], Q_2[0]
    if q_1 == q_2:
            return 'partial'
    # for q_1, q_2 in zip(Q_1[::-1], Q_2):
    #     if q_1 == q_2:
    #         return 'partial'
    #     else:
    #         break

    return 'null'


def check_contains_need_normalize(literal: Literal):
    atom = literal.atom
    left_str, right_str = atom.my_string1, atom.my_string2
    if atom.ltype == 'str.contains':
        if left_str.stype == 'str.++' and right_str.stype == 'const' and len(left_str.concats_strs) >= 3:
            return True

        if right_str.stype == 'str.++' and left_str.stype == 'const' and len(right_str.concats_strs) >= 3:
            return True  

    return False


def normalize_contains(literal: Literal):
    atom = literal.atom
    negation = literal.negation
    left_str, right_str = atom.my_string1, atom.my_string2

    if right_str.stype == 'str.++':
        left_str, right_str = deepcopy(right_str), deepcopy(left_str)

    i = 1
    count = len(left_str.concats_strs)
    new_literals = []
    new_clauses = []
    to_delete = False

    for el in left_str.concats_strs[1:]:
        if el.stype == 'const' and i < (count - 1):
            flag = overlap(el.cont, right_str.cont)
            print(f'OVERLAP({el.cont}, {right_str.cont}) = {flag}')

            if flag == 'full':
                to_delete = True
            elif flag == 'null':
                my_string1 = deepcopy(left_str.concats_strs[i-1])
                my_string2 = deepcopy(left_str.concats_strs[i+1])

                # if len(left_str.concats_strs[:i]) > 1:
                #     my_string1 = My_String(stype='str.++', concats_strs=left_str.concats_strs[:i])
                # else:
                #     my_string1 = left_str.concats_strs[0]

                # if len(left_str.concats_strs[i+1:]) > 1:
                #     my_string2 = My_String(stype='str.++', concats_strs=left_str.concats_strs[i+1:])
                # else:
                #     my_string2 = left_str.concats_strs[:-1]

                if negation:
                    atom1 = Atom(ltype='str.contains', my_string1=my_string1, my_string2=right_str)
                    atom2 = Atom(ltype='str.contains', my_string1=my_string2, my_string2=right_str)
                    new_clauses.append(Clause(literals=[Literal(atom=atom1, negation=True)]))
                    new_clauses.append(Clause(literals=[Literal(atom=atom2, negation=True)]))
                else:
                    atom1 = Atom(ltype='str.contains', my_string1=my_string1, my_string2=right_str)
                    atom2 = Atom(ltype='str.contains', my_string1=my_string2, my_string2=right_str)
                    new_literals.append(Literal(atom=atom1, negation=False))
                    new_literals.append(Literal(atom=atom2, negation=False))

            break

        i += 1

    return to_delete, new_clauses, new_literals
