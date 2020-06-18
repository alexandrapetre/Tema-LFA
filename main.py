#!/usr/bin/env python
import sys
import pickle

from regex import RegEx
from regular_expression import RegularExpression
from nfa import NFA
from dfa import DFA

import graphviz

try:
    from graphviz import Digraph
except ImportError:
    pass

EMPTY_SET = 0
EMPTY_STRING = 1
SYMBOL = 2
STAR = 3
CONCATENATION = 4
ALTERNATION = 5

_SIMPLE_TYPES = {EMPTY_SET, EMPTY_STRING, SYMBOL}


def rename_states(target, reference):
    off = max(reference.states) + 1
    target.start_state += off
    target.states = set(map(lambda s: s + off, target.states))
    target.final_states = set(map(lambda s: s + off, target.final_states))
    new_delta = {}
    for (state, symbol), next_states in target.delta.items():
        new_next_states = set(map(lambda s: s + off, next_states))
        new_delta[(state + off, symbol)] = new_next_states

    target.delta = new_delta


def new_states(*nfas):
    state = 0
    for nfa in nfas:
        m = max(nfa.states)
        if m >= state:
            state = m + 1

    return state, state + 1

def re_to_nfa(re):
    """Convert a Regular Expression to a Nondeterminstic Finite Automaton"""
    # TODO Thompson's algorithm
    alfabet = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
    #cazuri de baza
    if re.type == EMPTY_SET:
        return NFA(alfabet, {0}, 0, set(), {})
    elif re.type == EMPTY_STRING:
       return NFA(alfabet, {0, 1}, 0, {1}, {(0, ""): {1}})
    elif re.type == SYMBOL:
        return NFA(alfabet, {0, 1}, 0, {1}, {(0, re.symbol): {1}})
    #concatenare
    elif (re.type == CONCATENATION):
        A1 = re_to_nfa(re.lhs)
        A2 = re_to_nfa(re.rhs)
        rename_states(A2,A1)
        q0, qf = new_states(A1, A2)
        delta = A1.delta
        delta.update(A2.delta)
        delta.update({(q0, ""): {A1.start_state}})
        for x in range(len(list(A1.final_states))):
            delta.update({(list(A1.final_states)[x], ""):{A2.start_state}})
        for x in range(len(list(A2.final_states))):
            delta.update({(list(A2.final_states)[x], ""):{qf}})
        states = A1.states | A2.states | {q0, qf}
        return NFA(alfabet, states, q0, {qf}, delta )
    #alternation
    elif (re.type == ALTERNATION) :
        A1 = re_to_nfa(re.lhs)
        A2 = re_to_nfa(re.rhs)
        rename_states(A2,A1)
        q0, qf = new_states(A1, A2)
        delta = A1.delta
        delta.update(A2.delta)
        delta.update({(q0, ""): {A1.start_state, A2.start_state}})
        for x in range(len(list(A1.final_states))):
            delta.update({(list(A1.final_states)[x], ""):{qf}})
        for x in range(len(list(A2.final_states))):
            delta.update({(list(A2.final_states)[x], ""):{qf}})
        states = A1.states | A2.states | {q0, qf}
        return NFA(alfabet, states, q0, {qf}, delta)
    #star
    elif (re.type == STAR) :
        A1 = re_to_nfa(re.lhs)
        q0, qf = new_states(A1)
        delta = A1.delta
        delta.update({ (q0, ""): {A1.start_state, qf} })
        for x in range(len(list(A1.final_states))):
            delta.update({(list(A1.final_states)[x], ""):{A1.start_state, qf}})
        states = A1.states | {q0, qf}
        return NFA(alfabet, states, q0, {qf}, delta)



def function_closure(state, delta_nfa):

    new_state = []
    new_state.append(state)
    it = 0
    for it in new_state:
        key = (it, "")
        if key in delta_nfa:
            values = delta_nfa[it, ""]
            for st in values:
                if st not in new_state:
                    new_state.append(st)

    return new_state


def nfa_to_dfa(nfa):

    alfabet = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
    delta = {}
    stari_dfa = []
    final_dfa = set()
    e_closure = {}

    stari_nfa = nfa.states
    start_nfa = nfa.start_state
    final_nfa = nfa.final_states
    delta_nfa = nfa.delta

    for state in stari_nfa:
        closure = function_closure(state, delta_nfa)
        e_closure[state] = closure

    start = e_closure[start_nfa]
    stari_dfa.append(start)

    for contor1 in stari_dfa:
        for i in range (len(alfabet)):
            stare_noua = []
            curent = contor1
            for k in range (len(curent)):
                if (curent[k], alfabet[i]) in delta_nfa:
                    for elem in delta_nfa[curent[k], alfabet[i]]:
                        if elem not in stare_noua:
                            stare_noua.append(elem)
           
            for contor2 in stare_noua:
                for elem in e_closure[contor2]:
                    if elem not in stare_noua:
                        stare_noua.append(elem)

            if stare_noua not in stari_dfa:
                stari_dfa.append(stare_noua)

            state1 = stari_dfa.index(curent)
            delta[state1, alfabet[i]] = stari_dfa.index(stare_noua)


    for fin in final_nfa:
        for s in stari_dfa:
            if fin in s:
                final_dfa.add(stari_dfa.index(s))

    indecsi = []
    for i in range(0, len(stari_dfa)):
        indecsi.append(i)

    start_dfa = stari_dfa.index(start)

    return DFA(alfabet, indecsi, start_dfa, final_dfa, delta)




if __name__ == "__main__":
    valid = (len(sys.argv) == 4 and sys.argv[1] in ["RAW", "TDA"]) or \
            (len(sys.argv) == 3 and sys.argv[1] == "PARSE")
    if not valid:
        sys.stderr.write(
            "Usage:\n"
            "\tpython3 main.py RAW <regex-str> <words-file>\n"
            "\tOR\n"
            "\tpython3 main.py TDA <tda-file> <words-file>\n"
            "\tOR\n"
            "\tpython3 main.py PARSE <regex-str>\n"
        )
        sys.exit(1)

    if sys.argv[1] == "TDA":
        tda_file = sys.argv[2]
        with open(tda_file, "rb") as fin:
            parsed_regex = pickle.loads(fin.read())
    else:
        regex_string = sys.argv[2]
        # TODO "regex_string" conține primul argument din linia de comandă,
        # șirul care reprezintă regexul cerut. Apelați funcția de parsare pe el
        # pentru a obține un obiect RegEx pe care să-l stocați în
        # "parsed_regex"
        #
        # Dacă nu doriți să implementați parsarea, puteți ignora această parte.

        alfabet = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
        stack = [] 

        parsed_regex = None
        start = 0
        end = 0
        last = None
        modify = regex_string
        newString = regex_string
        signs = "+?*."
        brackets ="[]-"
        stack_string = []
        stack_symbols = []
        stack_par = []
        stack_square = []
        regex = None
        k = 1
        ceva = 0
        ok = 1
        square = 0
        start1 = 0
        end1 = 0
        ok1 = 1
        tuplet = None
        par = 0
        set1 = {}
        set1 = set()


        
        for i in range (len(regex_string)):
            last = None
            if modify[i] == '(':
                ceva = 1
                ok = 2
                start = i
            if modify[i] == ')':
                ok = 0
                end = i 
                ceva = 0
            if ok == 2:
                end = i + 1

            if len(regex_string) == 1 and regex_string[i] != '.':
                regex = RegEx(1, regex_string[i],None)
            elif regex_string[i] == '.':
                regex = RegEx(2, None, None)
            
            if regex_string[i] == '[':
                square = 1
                start1 = i
                ók1 = 2
            if regex_string[i] == ']':
                square = 2
                end1 = i
                ok1 = 0

            if ok1 == 2:
                end1 = start1 + 1

            if regex_string[i] == '-':
                if tuplet != None:
                    tuplet = (regex_string[i-1], regex_string[i+1])
                    set1.add(tuplet)
                else:
                    tuplet = (regex_string[i-1], regex_string[i+1])
                    set1.add(tuplet)

            if square == 1 and regex_string[i] not in brackets:
                if (i - 1) >= 0 and (i + 1) < len(regex_string):
                    if regex_string[i - 1] not in brackets:
                        if regex_string[i+1] == ']':
                            element = regex_string[i]
                            set1.add(element)
                        elif regex_string[i+1] != '-':
                            element = regex_string[i]
                            set1.add(element)
                    elif regex_string[i - 1] == '[':
                        if regex_string[i + 1] != '-':
                            element = regex_string[i]
                            set1.add(element)
            if square == 2:
                square = 3
                par = 1
                regex = RegEx(3, set1, None)
                stack_string.append(regex)

            count2 = ""

            if regex_string[i] == '{':
                k = 0
                count1 = regex_string[i+1]
                if regex_string[i+2] != '}': 
                    count2 = regex_string[i + 3]
                else:
                    elem = RegEx(1, regex_string[i-1], None)
                    regex = RegEx(7, elem, (int(count1),int(count1)))
                if count1 == ',':
                    count2 = regex_string[i + 2]
                    elem = RegEx(1, regex_string[i-1], None)
                    regex = RegEx(7, elem, (-1, int(count2)))
                elif count2 == '}':
                    elem = RegEx(1, regex_string[i-1], None)
                    regex = RegEx(7, elem, (int(count1), -1))
                elif count2 != "":
                    elem = RegEx(1, regex_string[i-1], None)
                    regex = RegEx(7, elem, (int(count1), int(count2)))

            if ok == 0:
                ok = 1
                while stack_par != []:
                    regex = stack_par.pop()
                    if stack_par != []:
                        regex2 = stack_par.pop()
                        if regex2 == '|':
                            count = 0
                            while stack_par != []:
                                regex2 = stack_par.pop()
                                count = count + 1
                                if stack_par != [] and count < c - start - 1:
                                    regex1 = stack_par.pop()
                                    count = count + 1
                                    regex3 = RegEx(8, regex2, regex1)
                                    regex5 = regex3
                                    stack_par.append(regex5)
                                else:
                                    regex3 = RegEx(9, regex2, regex)
                                    regex = regex3
                                    stack_par.append(regex)
                                    break
                        else:
                            regex3 = RegEx(8, regex2, regex)
                            regex = regex3
                            stack_par.append(regex)
                    else:
                        stack_string.append(regex)

            if regex_string[i] == '|':
                if ceva == 1:
                    c = i
                    stack_par.append(regex_string[i])
                else:
                    stack_string.append(regex_string[i])

            

            if regex_string[i] in alfabet:
                elem11 = RegEx(1, regex_string[i],None)
                if ceva == 1:
                    stack_par.append(elem11)
                elif square != 1:
                    stack_string.append(elem11)

            if regex_string[i] == '*':
                if ceva == 1:
                    reg1 = stack_par.pop()
                    regNew1 = RegEx(5, reg1, None)
                    stack_par.append(regNew1)
                else:
                    reg = stack_string.pop()
                    regNew = RegEx(5, reg, None)
                    stack_string.append(regNew)

            if regex_string[i] == '?':
                if ceva == 1:
                    reg1 = stack_par.pop()
                    regNew1 = RegEx(4, reg1, None)
                    stack_par.append(regNew1)
                else:
                    reg = stack_string.pop()
                    regNew = RegEx(4, reg, None)
                    stack_string.append(regNew)


            if regex_string[i] == '+':
                if ceva == 1:
                    reg1 = stack_par.pop()
                    regNew1 = RegEx(6, reg1, None)
                    stack_par.append(regNew1)
                else:
                    reg = stack_string.pop()
                    regNew = RegEx(6, reg, None)
                    stack_string.append(regNew)

        while stack_string != [] :
            if k != 0:
                regex = stack_string.pop()
                if stack_string != []:
                    regex2 = stack_string.pop()
                    if regex2 == '|':
                        while stack_string != []:
                                    regex2 = stack_string.pop()
                                    if stack_string != []:
                                        regex1 = stack_string.pop()
                                        regex3 = RegEx(8, regex2, regex1)
                                        regex5 = regex3
                                        stack_string.append(regex5)
                                    else:
                                        regex3 = RegEx(9, regex2, regex)
                                        regex = regex3
                                        stack_string.append(regex)
                                        break
                    else:
                        regex3 = RegEx(8, regex2, regex)
                        regex = regex3
                        stack_string.append(regex)
            else:
                break

        ##########################################################################

        stack_elems = []
        stack_par = []
        k = 1
        reg_expr = None
        stack_acolade = []
        stack_elem1 = []
        start = 0
        end = 0
        c = 0
        modify = regex_string
        open_set = []
        closed_set = []
        contor = 0
        stack_brackets = []
        stack_temp = []
        tuplet = None
        square = 0
        start1 = 0
        end1 = 0
        ok1 = 1
        tuplet = None
        par = 0
        set1 = {}
        set1 = set()
        punct = 0
        stack_punct = []
        var = 0


        for i in range (len(regex_string)):

            if regex_string[i] == '.':
                punct = 1
                for j in range (len(alfabet)):
                    element = alfabet[j]
                    reg_expr1 = RegularExpression(2, element, None)
                    stack_punct.append(reg_expr1)

            if punct == 1:
                ok = 0
                for j in range (len(stack_punct)) :
                    if j + 1 != (len(stack_punct)): 
                        if j == 0:
                            reg_expr =  RegularExpression(5, stack_punct[j], stack_punct[j +1])
                        elif j > 0 and j+1 < (len(stack_punct)):
                            reg_expr2 = RegularExpression(5, reg_expr, stack_punct[j + 1])
                            reg_expr = reg_expr2
                stack_elems.append(reg_expr)
       
           
            if modify[i] == '(':
                ceva = 1
                ok = 2
                start = i
                open_set.append(i)
                contor = contor + 1
            if modify[i] == ')':
                ok = 0
                end = i 
                ceva = 0
                closed_set.append(i)
                closed_set.reverse()
            if ok == 2:
                end = i + 1

            if regex_string[i] == '[':
                square = 1
                start1 = i
                ok1 = 2
            if regex_string[i] == ']':
                square = 2
                end1 = i
                ok1 = 0

            if ok1 == 2:
                end1 = start1 + 1

            if regex_string[i] == '-':
                if tuplet != None:
                    tuplet = (regex_string[i-1], regex_string[i+1])
                    for j in range (ord(regex_string[i-1]), ord(regex_string[i+1]) +1):
                        elem1 = chr(j)
                        reg_expr = RegularExpression(2,elem1, None)
                        stack_brackets.append(reg_expr)
                        stack_temp.append(elem1)
                else:
                    tuplet = (regex_string[i-1], regex_string[i+1])
                    set1.add(tuplet)
                    for j in range (ord(regex_string[i-1]), ord(regex_string[i+1]) + 1):
                        elem1 = chr(j)
                        reg_expr = RegularExpression(2, elem1, None)
                        stack_brackets.append(reg_expr)
                        stack_temp.append(elem1)

            if square == 1 and regex_string[i] not in brackets:
                if (i - 1) >= 0 and (i + 1) < len(regex_string):
                    if regex_string[i - 1] not in brackets:
                        if regex_string[i+1] == ']':
                            element = regex_string[i]
                            reg_expr = RegularExpression(2,element, None)
                            stack_brackets.append(reg_expr)
                            stack_temp.append(element)
                        elif regex_string[i+1] != '-':
                            element = regex_string[i]
                            reg_expr = RegularExpression(2,element, None)
                            stack_brackets.append(reg_expr)
                    elif regex_string[i - 1] == '[':
                        if regex_string[i + 1] != '-':
                            element = regex_string[i]
                            reg_expr = RegularExpression(2,element, None)
                            stack_brackets.append(reg_expr)
                    
    
            if square == 2:
                square = 3
                k = 0
                for j in range (len(stack_brackets)) :
                    if j + 1 != (len(stack_brackets)): 
                        if j == 0:
                            reg_expr =  RegularExpression(5, stack_brackets[j], stack_brackets[j +1])
                        elif j > 0 and j+1 < (len(stack_brackets)):
                            reg_expr2 = RegularExpression(5, reg_expr, stack_brackets[j + 1])
                            reg_expr = reg_expr2
                stack_elems.append(reg_expr)

            if regex_string[i] in alfabet and var == 0 :
                elem1 = RegularExpression(2, regex_string[i], None)
                if ceva == 1:
                    stack_par.append(elem1)
                elif square != 1:
                    stack_elems.append(elem1)

            if regex_string[i] == '|':
                if ceva == 1:
                    c = i
                    stack_par.append(regex_string[i])
                else:
                    stack_elems.append(regex_string[i])

            if ok == 0 and punct == 0:
                ok = 1
                while stack_par != []:
                    reg_expr = stack_par.pop()
                    if stack_par != []:
                        reg_expr2 = stack_par.pop()
                        if reg_expr2 == '|':
                            count = 0
                            while stack_par != []:
                                reg_expr2 = stack_par.pop()
                                count = count + 1
                                if stack_par != [] and count < c - start - 1:
                                    reg_expr1 = stack_par.pop()
                                    count = count + 1
                                    reg_expr3 = RegularExpression(4, reg_expr2, reg_expr1)
                                    reg_expr5 = reg_expr3
                                    stack_par.append(reg_expr5)
                                else:
                                    reg_expr3 = RegularExpression(5, reg_expr2, reg_expr)
                                    reg_expr = reg_expr3
                                    stack_par.append(reg_expr)
                                    break
                        else:
                            reg_expr3 = RegularExpression(4, reg_expr2, reg_expr)
                            reg_expr = reg_expr3
                            stack_par.append(reg_expr)
                    else:
                        stack_elems.append(reg_expr)

            if regex_string[i] == '*':
                if ceva == 1:
                    reg_expr1 = stack_par.pop()
                    reg_expr = RegularExpression(3,reg_expr1, None)
                    stack_par.append(reg_expr)
                else:
                    reg_expr1 = stack_elems.pop()
                    reg_expr = RegularExpression(3,reg_expr1, None)
                    stack_elems.append(reg_expr)


            if regex_string[i] == '?':
                if ceva == 1:
                    reg_expr1 = stack_par.pop()
                    reg_expr2 = RegularExpression(1, None, None)
                    reg_expr = RegularExpression(5,reg_expr2, reg_expr1)
                    stack_par.append(reg_expr)
                else:
                    reg_expr1 = stack_elems.pop()
                    reg_expr2 = RegularExpression(1, None, None)
                    reg_expr = RegularExpression(5,reg_expr2, reg_expr1)
                    stack_elems.append(reg_expr)


            if regex_string[i] == '+':
                if ceva == 1:
                    reg_expr1 = stack_par.pop()
                    reg_expr2 = reg_expr1
                    reg_expr2 = RegularExpression(3, reg_expr2, None)
                    reg_expr = RegularExpression(4,reg_expr1, reg_expr2)
                    stack_par.append(reg_expr)
                else:
                    reg_expr1 = stack_elems.pop()
                    reg_expr2 = reg_expr1
                    reg_expr2 = RegularExpression(3, reg_expr2, None)
                    reg_expr = RegularExpression(4,reg_expr1, reg_expr2)
                    stack_elems.append(reg_expr)


            count2 = ""

            if regex_string[i] == '{':
                var = 1
                stack_elems.pop()
                q = 0
                count1 = regex_string[i + 1]
                if regex_string[i + 2] != '}' : 
                    count2 = regex_string[i + 3]
                else:
                    for j in range (int(count1) - 1) :
                        if j == 0:
                            reg_expr1 = RegularExpression(2, regex_string[i-1],None)
                            reg_expr2 = reg_expr1
                            reg_expr3 = RegularExpression(4, reg_expr2, reg_expr1)
                            reg_expr = reg_expr3
                            stack_elems.append(reg_expr)
                        else:
                            reg_expr1 =  stack_elems.pop()
                            reg_expr2 = RegularExpression(2, regex_string[i-1], None)
                            reg_expr3 = RegularExpression(4, reg_expr2, reg_expr1)
                            reg_expr = reg_expr3
                            stack_elems.append(reg_expr)

                if count1 == ',':
                    for j in range (int(regex_string[i+2]) + 1):
                        if j == 0:
                            reg_expr1 = RegularExpression(1, None, None)
                            stack_acolade.append(reg_expr1)
                        else:
                            if j == 1:
                                reg_expr1 = RegularExpression(2, regex_string[i-1],None)
                                reg_expr = reg_expr1
                                stack_elem1.append(reg_expr)
                            else:
                                reg_expr1 =  stack_elem1.pop()
                                reg_expr2 = RegularExpression(2, regex_string[i-1], None)
                                reg_expr3 = RegularExpression(4, reg_expr2, reg_expr1)
                                reg_expr = reg_expr3
                                stack_elem1.append(reg_expr)
                            stack_acolade.append(reg_expr)

                    while stack_acolade != []:
                        reg_expr = stack_acolade.pop()
                        if stack_acolade != []:
                            reg_expr2 = stack_acolade.pop()
                            reg_expr3 = RegularExpression(5, reg_expr2, reg_expr)
                            reg_expr = reg_expr3
                            stack_acolade.append(reg_expr)

                elif count2 == '}':
                    for j in range (int(regex_string[i+1])-1):
                        if j == 0:
                            reg_expr1 = RegularExpression(2, regex_string[i-1],None)
                            reg_expr2 = reg_expr1
                            reg_expr3 = RegularExpression(4, reg_expr2, reg_expr1)
                            reg_expr = reg_expr3
                            stack_elems.append(reg_expr)
                        else:
                            reg_expr1 =  stack_elems.pop()
                            reg_expr2 = RegularExpression(2, regex_string[i-1], None)
                            reg_expr3 = RegularExpression(4, reg_expr2, reg_expr1)
                            reg_expr = reg_expr3
                            stack_elems.append(reg_expr)
                    elem = RegularExpression(2, regex_string[i-1], None)
                    reg_expr1 = RegularExpression(3, elem, None)
                    reg_expr2 = stack_elems.pop()
                    reg_expr = RegularExpression(4, reg_expr2, reg_expr1)

                elif count2 != "":
                    for j in range (int(count1), int(count2) + 1):
                        if j == 0:
                            reg_expr1 = RegularExpression(1, None, None)
                            stack_acolade.append(reg_expr1)
                        elif j == (int(count1)):
                            for k1 in range (int(count1)):
                                if k1 == 0:
                                    reg_expr1 = RegularExpression(2, regex_string[i-1],None)
                                    reg_expr = reg_expr1
                                    stack_elem1.append(reg_expr)
                                else:
                                    reg_expr1 =  stack_elem1.pop()
                                    reg_expr2 = RegularExpression(2, regex_string[i-1], None)
                                    reg_expr3 = RegularExpression(4, reg_expr2, reg_expr1)
                                    reg_expr = reg_expr3
                                    stack_elem1.append(reg_expr)
                            stack_acolade.append(reg_expr)
                        else:
                            if (len(stack_acolade)) == 2 and q == 0:
                                stack_acolade.pop()
                                q = 1
                            reg_expr1 = stack_elem1.pop()
                            reg_expr2 = RegularExpression(2, regex_string[i-1], None)
                            reg_expr3 = RegularExpression(4, reg_expr2, reg_expr1)
                            reg_expr = reg_expr3
                            stack_elem1.append(reg_expr)
                        stack_acolade.append(reg_expr)


                    while stack_acolade != []:
                        reg_expr = stack_acolade.pop()
                        if stack_acolade != []:
                            reg_expr2 = stack_acolade.pop()
                            reg_expr3 = RegularExpression(5, reg_expr2, reg_expr)
                            reg_expr = reg_expr3
                            stack_acolade.append(reg_expr)

                if regex_string[i+2] != '}':
                    stack_elems.append(reg_expr)

            if regex_string[i] == '}':
                var = 0

        #print(stack_elems[1])

        while stack_elems != []:
            if k != 0:
                reg_expr = stack_elems.pop()
                if stack_elems != []:
                    reg_expr2 = stack_elems.pop()
                    if reg_expr2 == '|':
                        while stack_elems != []:
                            reg_expr2 = stack_elems.pop()
                            if stack_elems != []:
                                reg_expr1 = stack_elems.pop()
                                reg_expr3 = RegularExpression(4, reg_expr1, reg_expr2)
                                reg_expr4 = reg_expr3
                                stack_elems.append(reg_expr4)
                            else:
                                reg_expr3 = RegularExpression(5, reg_expr2, reg_expr)
                                reg_expr = reg_expr3
                                stack_elems.append(reg_expr)
                                break
                    else:
                        reg_expr3 = RegularExpression(4, reg_expr2, reg_expr)
                        reg_expr = reg_expr3
                        stack_elems.append(reg_expr)
            else:
                break

        nfa = re_to_nfa(reg_expr)
        dfa = nfa_to_dfa(nfa)

        if sys.argv[1] == "PARSE":
            print(str(regex))
            sys.exit(0)

    # În acest punct, fie că a fost parsat, fie citit direct ca obiect, aveți
    # la dispoziție variabila "parsed_regex" care conține un obiect de tip
    # RegEx. Aduceți-l la forma de Automat Finit Determinist, pe care să puteți
    # rula în continuare.

    with open(sys.argv[3], "r") as fin:
        content = fin.readlines()


    for word in content:
        # TODO la fiecare iterație, "word" conținue un singur cuvânt din
        # fișierul de input; verificați apartenența acestuia la limbajul
        # regexului dat și scrieți rezultatul la stdout.
        ok = 0
        delta_dfa = dfa.delta
        state = dfa.start_state
        final_dfa = dfa.final_states

        for letter in word:
            if (state, letter) in delta_dfa:
                new_state = delta_dfa[(state, letter)]
                state = new_state

        for fin in final_dfa:
            if fin == state:
                ok = 1
                print("True")
                break

        if ok == 0:
            print("False")

        pass
