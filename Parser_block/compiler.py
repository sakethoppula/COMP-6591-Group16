import os
import sys

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import ply.yacc as yacc

import ply.lex as lex


class Rule(object):
    def __init__(self, head={}, body={}, type="rule"):
        self.head = head 
        self.body = body
        self.type = type
    def __repr__(self):
        return "%r" % (self.__dict__)
    def __str__(self) -> str:
        h_s = '('
        for a in self.head.terms:
            h_s = h_s + str (a) + ' ,'
        h_s = h_s[:-2]
        h_s = f'{h_s}) :-'
        h_s = f'{str(self.head.predicate)} {h_s}'

        b_s = ''
        for b in self.body:
            if str(b.type) == "predicate":
                i_s = '('
                for a in b.terms:
                    i_s = i_s + str (a) + ' ,'
                i_s = i_s[:-2]
                i_s = f'{i_s})'
                s = f'{str(b.predicate)} {i_s}'
                b_s = b_s + s + ' ,'
            elif str(b.type) == "constraint":
                s = f'{str(b.termX)} {str(b.operator)} {str(b.termY)}'
                b_s = b_s + s + ' ,'
            else:
                print("nothing")
        return str(h_s + b_s[:-1])
     
class Fact(object):
    def __init__(self, fact, type = "fact"):
        self.fact = fact
        self.fact.type = type
        self.type = type
        self.record = set()

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return self.__dict__ == other.__dict__
        else:
            return False

    def __ne__(self, other):
        return not self.__eq__(other)

    def __repr__(self):
        return "%r" % (self.__dict__)
    def __str__(self) -> str:
        s1 = '('
        for a in self.fact.terms:
            s1 = s1 + str(a) + ','
        s1 = s1[:-1]
        s1 = f'{s1})'
        s = f'{str(self.fact.predicate)} {s1}'
        if self.fact.isNegated:
            s = f"not {s}"
        return str(s)

class Predicate(object):
    def __init__(self, name="", terms=[], isNegated=False, type = "predicate"):
        self.predicate = name
        self.terms = terms
        self.isNegated = isNegated
        self.type = type

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return self.__dict__ == other.__dict__
        else:
            return False

    def __ne__(self, other):
        return not self.__eq__(other)

    def __repr__(self):
        return "%r" % (self.__dict__)
   
   
class Constraint(object):
    def __init__(self, termX="", operator="", termY="", type = "constraint"):
        self.termX = termX
        self.operator = operator
        self.termY = termY
        self.type = type
    def __repr__(self):
        return "%r" % (self.__dict__)

reserved = {'not' : 'NOT'}

tokens = [ 'TURNSTILE', 'DOT', 'LEFT_PAR', 'RIGHT_PAR', 'COMMA', 'CONSTANT', 'VARIABLE', 'OPERATOR'] + list(reserved.values())

t_ignore = ' \t'

t_TURNSTILE = r'\:\-'
t_DOT = r'\.'
t_LEFT_PAR = r'\('
t_RIGHT_PAR = r'\)'
t_COMMA = r'\,'
t_VARIABLE = r'[A-Z][A-Za-z0-9_]*'
t_OPERATOR = r'[!<>=](=)?'

def t_CONSTANT(t):
    r'[a-z0-9_][a-zA-Z_0-9]*'
    t.type = reserved.get(t.value, 'CONSTANT')
    return t

def t_comment(t):
    r"[ ]*\%[^\n]*"

def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

def t_error(t):
    print(f"Illegal character '{t.value[0]}'")
    t.lexer.skip(1)

lexer = lex.lex(debug=False)

errorList = []
def p_program(p):
    '''program : 
        | facts rules
        | facts
        | rules'''
    if len(p) == 2:
        p[0] = p[1]
    elif len(p) == 3:
        p[0] = p[1] + p[2]
    elif len(p) == 4:
        p[0] = p[1] + p[2] + p[3]

def p_facts_list(p):
    '''facts : facts fact'''
    p[0] = p[1] + [p[2]]

def p_facts(p):
    '''facts :  fact'''
    p[0] = [p[1]]

def p_fact(p):
    '''fact : block DOT'''
    p[0] = Fact(p[1])

def p_rules_list(p):
    '''rules : rules rule'''
    p[0] = p[1] + [p[2]]

def p_rules(p):
    '''rules :  rule'''
    p[0] = [p[1]]

def p_rule(p):
    '''rule : head TURNSTILE body DOT'''
    p[0] = Rule(p[1], p[3], 'rule')

def p_head(p):
    '''head : block'''
    p[0] = p[1]

def p_body(p):
    '''body : blocklist'''
    p[0] = p[1]

def p_blocklist1(p):
    '''blocklist : blocklist COMMA block'''
    p[0] = p[1] + [p[3]]

def p_blocklist2(p):
    '''blocklist : blocklist COMMA constraint'''
    p[0] = p[1] + [p[3]]

def p_blocklist3(p):
    '''blocklist : block'''
    p[0] = [p[1]]

def p_block(p):
    '''block : CONSTANT LEFT_PAR atomlist RIGHT_PAR'''
    p[0] = Predicate(p[1], p[3], False)

def p_negatedblock(p):
    '''block : NOT CONSTANT LEFT_PAR atomlist RIGHT_PAR'''
    p[0] = Predicate(p[2], p[4], True)

def p_atomlist1(p):
    '''atomlist : atomlist COMMA atom'''
    p[0] = p[1] + [p[3]]

def p_atomlist2(p):
    '''atomlist : atom'''
    p[0] = [p[1]]

def p_atomvariable(p):
    '''atom : VARIABLE'''
    p[0] = p[1]

def p_atomconstant(p):
    '''atom : CONSTANT'''
    p[0] = p[1]

def p_constraintvariable(p):
    '''constraint : VARIABLE OPERATOR VARIABLE'''
    p[0] = Constraint(p[1], p[2], p[3])

def p_constraintconstant(p):
    '''constraint : VARIABLE OPERATOR CONSTANT'''
    p[0] = Constraint(p[1], p[2], p[3])

def p_error(p):
    errorList.append(f"Syntax error in input! {str(p)}" + "\n")
    print("Syntax error in input! ", p)

out = open('output.res', 'w')
parser = yacc.yacc(start='program', write_tables=False, debug=False)


if __name__ == '__main__':
    parser = yacc.yacc(start='program')
    
    while True:
        try:
            s = input('datalog > ')
        except EOFError:
            break
        if not s: continue
        prog = parser.parse(s)
        print(prog)
