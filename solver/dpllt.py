from .structures import *
from .lia import Lia_Formula


def call_lia(formula=None, m=None):
    return Lia_Formula(formula=formula, m=m).check_sat()


def call_theory(f, m):
    """
    По идее, теория вызывается просто на набор Литералов, 
    мб для этого определить отдельную структуру?
    """
    return True


def literal_in_m(literal, m):
    not_literal = literal.get_conjugate()
    for x in m:
        if x == literal:
            return 0
        if x == not_literal:
            return 1
    return 'u'


def check_if_zero_without(c, literal, m):
    i = c.literals.index(literal)
    for x in c.literals[:i] + c.literals[i+1:]:
        if literal_in_m(x, m) != 0:
            return False
    return True


def unit_propagate(m, f):
    for c in f.clauses:
        for literal in c.literals:
            if literal_in_m(literal, m) == 'u' and check_if_zero_without(c, literal, m):
                m.append(literal.get_conjugate())
                # print('[m] <-', f.dpll_literal_view(literal.get_conjugate()), '<==>', f.dpll_literal_view(literal), ' = 1')
                # print('[m] ', ' '.join([f.simple_atmoms[literal.atom]+':'+str(literal_in_m(literal, m)) for literal in f.literals]))
                # print('\n')
                return unit_propagate(m, f)

    return m, f


def check_broken(m, f, dot_strings=False):
    for c in f.clauses:
        if any([literal_in_m(literal, m) for literal in c.literals]):
            continue
        # print(get_m_state(m, f), '->', f'"{f.dpll_clause_view(c)}"')
        if dot_strings is not None:
            dot_strings.append(f'{get_m_state(m, f)}->"{f.dpll_clause_view(c)}"')
        return True
    return False


def decide(m, f):
    for c in f.clauses:
        for literal in c.literals:
            if literal_in_m(literal, m) == 'u':
                s = f.dpll_literal_view(literal)
                # print('Decide: ', s,)
                return literal


def check_node(m, f, old_m, dot_strings=None):
    if dot_strings is not None:
        # ds = f'{get_m_state(old_m, f)}' if old_m is not None else '"start"' + f' -> {get_m_state(m, f)}'
        # dot_strings.append(ds)
        dot_strings.append(f'{get_m_state(old_m, f) if old_m is not None else "start"}->{get_m_state(m, f)}')

    # print(get_m_state(old_m, f) if old_m else 'start', '->', get_m_state(m, f))

    before_prop = m.copy()
    # 1 распространяем переменные
    m, f = unit_propagate(m, f)
    if m != before_prop:
        diff = []
        for literal in m:
            if literal not in before_prop:
                if literal.negation:
                    diff.append(f'{f.simple_atmoms[literal.atom]}:{(literal_in_m(literal, m) + 1)%2}')
                else:
                    diff.append(f'{f.simple_atmoms[literal.atom]}:{literal_in_m(literal, m) }')
        diff.sort(key=lambda x: x[0]) 
        if dot_strings is not None:
            dot_strings.append(f'{get_m_state(before_prop, f)}->{get_m_state(m, f)} [label="{diff}"]')
        # print(get_m_state(before_prop, f), '->', get_m_state(m, f), f' [label="{diff}"]')

    # 2 проверяем, не сломало ли ничего распространение
    if check_broken(m, f, dot_strings=dot_strings):
        return False
    """
    в данный момент lia вызывается на каждом ветвлении
    """
    # 3 теперь можно проверить полученную модель в lia
    if not call_lia(m=m):
        if dot_strings is not None:
            dot_strings.append(f'{get_m_state(m, f)}-> "ошибка в LIA"')
        print('Противоречие в LIA')
        return False
    print()

    # 4 проверяем, осталось ли чего неопределенного в m
    if len(m) == len(f.atoms):
        # print('MODEL:')
        return call_theory(f, m)

    # 4 если осталось, то порождаем 2 ветки
    new_literal = decide(m, f)

    old_m = deepcopy(m)
    m += [new_literal]
    sat = check_node(m, f, old_m, dot_strings)

    if not sat:
        m = deepcopy(old_m)
        m += [new_literal.get_conjugate()]
        sat = check_node(m, f, old_m, dot_strings)

    return sat

    # return check_node(m + [new_literal], f, m, dot_strings) or check_node(m+[new_literal.get_conjugate()], f, m, dot_strings)


def get_m_state(m, f):
    return f'"{" ".join(list(filter(None, [f.dpll_literal_view(literal)+":"+str(literal_in_m(literal, m)) if not literal.negation else None for literal in f.literals])))}"'


def check_sat(f, dot_strings=None):
    if dot_strings is not None:
        legend = ['subgraph clusterMain {', 
        'graph [labelloc="b" labeljust="r" label=<<TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">']
        legend.extend(['<TR><TD>' + str(atom) + '</TD><TD>' + simple_value + '</TD></TR>' for atom, simple_value in f.simple_atmoms.items()])
        legend.append('</TABLE>>];')
        dot_strings.extend(legend)
    # if not call_lia(formula=f, m=None):
    #     print('Формула не прошла проверку в lia')
    #     return False


    model = []
    res = check_node(model, f, None, dot_strings=dot_strings)
    # return check_node([], f, None, dot_strings=dot_strings)
    return res, model
