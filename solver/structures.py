from copy import deepcopy
from typing import List

class My_String():
    """
    stype - один из:
    'const' , 'variable', 'str.++' , 'str.replace', 'str.replace_all'
    """

    def __init__(self, stype, cont=None, var_name=None, concats_strs=None, replace_strs=None):
        if stype not in ['const', 'variable', 'str.++', 'str.replace', 'str.replace_all']:
            raise Exception(
                f'Указан неверный stype при создании My_String: {stype}')
        if 'str.rep' in stype and (len(replace_strs) != 3 or replace_strs[1].cont == ''):
            raise Exception(f'Ошибка при создании my_string: stype={stype}, replace_strs={[str(rs) for rs in replace_strs]}')

        if concats_strs:
            concats_strs = list(
                filter(lambda x: x is not None and x.cont != '', concats_strs))
            if len(concats_strs) == 1:
                    the_only_str= concats_strs[0]
                    self.stype = the_only_str.stype
                    self.cont = the_only_str.cont
                    self.var_name = the_only_str.var_name
                    self.concats_strs = the_only_str.concats_strs
                    self.replace_strs = the_only_str.replace_strs
                    return
        self.stype = stype
        self.cont = cont
        self.var_name = var_name
        self.concats_strs = concats_strs
        self.replace_strs = replace_strs
        self.could_be_empty = False

    def __str__(self):
        if self.cont is not None:
            # s = f'"{self.cont}"'
            return f'"{self.cont}"'
        elif self.var_name:
            # s = f'<{self.var_name}>'
            return self.var_name
        elif self.concats_strs:
            s = 'str.++'
            for cs in self.concats_strs:
                s += ' ' + str(cs)
        else:
            s = self.stype
            for cs in self.replace_strs:
                s += ' ' + str(cs)
        return f'({s})'

    def __eq__(self, o):
        if self.stype != o.stype:
            return False

        if self.stype == 'const':
            return self.cont == o.cont

        if self.var_name:
            return  self.var_name == o.var_name

        if self.stype == 'str.++':
            return self.concats_strs == o.concats_strs

        return self.replace_strs == o.replace_strs


    @staticmethod
    def extend_eq(my_string1, my_string2):
        if my_string1.stype != my_string2.stype:
            return False

        if my_string1.stype == 'const':
            return my_string1.cont == my_string2.cont

        if my_string1.var_name:
            return  my_string1.var_name == my_string2.var_name or \
                    my_string1.var_name + "'" == my_string2.var_name or \
                    my_string2.var_name + "'" == my_string1.var_name

        if my_string1.stype == 'str.++':
            if len(my_string1.concats_strs) != len(my_string2.concats_strs):
                return False 
            
            for str1, str2 in zip(my_string1.concats_strs, my_string2.concats_strs):
                rt = My_String.extend_eq(str1, str2)
                if not rt:
                    return False

            return True

        if len(my_string1.replace_strs) != len(my_string2.replace_strs):
                return False 
            
        for str1, str2 in zip(my_string1.replace_strs, my_string2.replace_strs):
            rt = My_String.extend_eq(str1, str2)
            if not rt:
                return False

        return True


    def __hash__(self):
        return len(self.__str__())


class Atom():
    """
    ltype - один из:
    '=', 'str.contains'
    """

    def __init__(self, ltype, my_string1, my_string2):
        if ltype not in ['=', 'str.contains']:
            raise Exception(
                f'Указан неверный ltype при создании Atom: {ltype}')
        self.ltype = ltype
        self.my_string1 = my_string1
        self.my_string2 = my_string2

    def __str__(self):
        return f'({self.ltype} {str(self.my_string1)} {str(self.my_string2)})'

    def __eq__(self, o):
        return self.ltype == o.ltype and self.my_string1 == o.my_string1 and self.my_string2 == o.my_string2

    def __hash__(self):
        return len(self.__str__())


class Literal():
    def __init__(self, atom, negation, decisive=False):
        self.atom = atom
        self.negation = negation
        self.decisive = decisive

    def __str__(self):
        return f'{"(not " if self.negation else ""}{str(self.atom)}{")" if self.negation else ""}'

    def __eq__(self, o):
        return self.negation == o.negation and self.atom == o.atom

    def get_conjugate(self, decisive=False):
        """Возвращает объект сопряженного литерала"""
        return Literal(self.atom, not self.negation, decisive=decisive)

    def get_copy(self, decisive=False):
        """Возвращает объект-копию литерала"""
        return Literal(self.atom, self.negation, decisive=decisive)

    def __hash__(self):
        return len(self.__str__())


class Clause():
    def __init__(self, literals):
        self.literals = literals

    def __str__(self):
        s = '(or\n'
        for lw in self.literals:
            s += f'    {str(lw)}\n'
        s += '  )\n'
        return s

    def __eq__(self, o):
        for x in self.literals:
            if x not in o.literals:
                return False
        for x in o.literals:
            if x not in self.literals:
                return False
        return True

    def __hash__(self):
        return len(self.__str__())


class Formula():
    def __init__(self, **kwargs):
        """
        либо без аргументов,
        либо {
            strings: [],
            atoms: [],
            literals: [],
            clauses: [],
            strings_counter: {}
        }
        """
        if not kwargs:
            return
        self.strings = kwargs['strings']
        self.atoms = kwargs['atoms']
        self.literals = kwargs['literals']
        self.clauses = kwargs['clauses']
        self.strings_counter = kwargs['strings_counter']
        if 'logic' in kwargs:
            self.logic = kwargs['logic']

        self.simple_atmoms = {}
        letter = ord('A')
        for atom in self.atoms:
            self.simple_atmoms[atom] = chr(letter)
            letter += 1

        self.literals.sort(key=lambda x: self.simple_atmoms[x.atom])

    def __str__(self):
        try:
            s = '\n###FORMULA:###\n'
            s += 'STRINGS:\n'
            for x in self.strings:
                s += '  ' + str(x)+'\n'
            s += 'ATOMS:\n'
            for x in self.atoms:
                s += '  ' + str(x)+'\n'
            s += 'LITERALS:\n'
            for x in self.literals:
                s += '  ' + str(x)+'\n'
            s += 'CLAUSES:\n'
            for x in self.clauses:
                s += '  ' + str(x)+'\n'
            return s
        except:
            return "ПУСТАЯ ФОРМУЛА"

    def copy(self):
        return deepcopy(self)

    def extend_clauses(self, m):
        cop = self.copy()
        for lm in m:
            literal = deepcopy(lm)
            ext_clause = Clause([literal.get_conjugate()])
            cop.clauses.append(ext_clause)

        return cop

    def dpll_literal_view(self, literal):
        return f'{"(not " if literal.negation else ""}{self.simple_atmoms[literal.atom]}{")" if literal.negation else ""}'

    def dpll_clause_view(self, clause):
        return f'(or {" ".join([self.dpll_literal_view(literal) for literal in clause.literals])})'

    def print_dpll_view(self):
        for clause in self.clauses:
            # print(f'(or {" ".join([self.dpll_literal_view(literal) for literal in clause.literals])})')
            print(self.dpll_clause_view(clause))


#Структуры, необходимые для реализации преобразования Нильсена
class Substitution():
    #substs - array of tuples, where tuple is (substitution(My_String), could_be_empty(Bool))
    def __init__(self, variable_name, substs=None, from_left=True) -> None:
        self.variable_name = variable_name
        self.substs = []
        self.from_left = from_left

    def add_subst(self, subst):
        self.substs.append(subst)

    def __str__(self) -> str:
        s = ''
        s += str(self.variable_name) + '\n'
        for sub in self.substs:
            s += f'({str(sub[0])}, {sub[1]})'
        return s 


class Node():
    def __init__(self, literal=None, parent=None, substitutions=None, children=None, index=0, sat_marker=False, cycle_marker=False, model=None) -> None:
        self.parent = parent
        self.children = children or [] 
        
        #массив подстановок по отношению к детям
        self.substitutions = substitutions

        self.literal = literal
        
        #0 index for root
        self.index = index

        #помечаем ноду, обозначающую, что уравнение можно решить
        self.sat_marker = sat_marker

        self.cycle_marker = cycle_marker

        self.model = model


    def __eq__(self, __o: object) -> bool:
        if type(__o) is not Node:
            return False

        return self.index == __o.index

    def __hash__(self) -> int:
        return hash(self.index)

    def __str__(self) -> str:
        s = ''
        s += f'Index node = {self.index}\n'
        if self.parent:
            s += f'\tparent index = {self.parent.index}\n'
        s += f'\tliteral = {self.literal}\n'
        s += f'\tsat_marker = {self.sat_marker}\n'
        s += f'\tcycle_marker = {self.cycle_marker}\n'
        # print(s)
        
        if len(self.children) > 0:
            # print(len(self.children))
            for child in self.children:
                s +='' + str(child)
        
        return s


class SubstitutionTree():
    def __init__(self, root:Node) -> None:
        self.root = root 
        self.substitutions_edges = {}
        self.actual_index = 1

    def add(self, atom: Atom, subst):
        pass
        
    def delete_subst(self, atom:Atom, subst):
        pass

    def get_substitutions(self, path):
        #path - массив индексов вершин
        res = []
        for i in range(len(path) - 1):
            subst = self.substitutions_edges[(path[i], path[i + 1])]
            res.append((path[i], path[i + 1], subst))

        return res

    def __str__(self) -> str:
        return str(self.root)