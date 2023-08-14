import lists

import os
import sys
import copy
import networkx as nx
import logging
import time
import argparse
import matplotlib.pyplot as plt

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import Parser_block.compiler
from Parser_block.compiler import Fact, Predicate

def print_to_output_file(l):
    Parser_block.compiler.out.write(l)

def EDB_int(EDB, rules):
    initEDB = []
    for i in range(len(rules)):
        rule = rules[i]
        newFacts = matchGoals(EDB, rule, i)
        if not newFacts:
            continue
        for f in newFacts:
            print_to_output_file(f"nf: {f}\n")
        initEDB.extend(newFacts)
    return initEDB


def check_program_validity(facts, rules):
    '''
    Checks the list of rules and facts to see if they are having the correct format and raises an alert if not
    '''
    warning = False
    for fact in facts.copy():
        if not isLowerCaseList(fact.fact.terms):
            facts.remove(fact)
            warning = True

    for rule in rules.copy():
        bList = []
        pList = []
        for s in [x.terms for x in rule.body if x.type == 'predicate']:
            bList.extend(s)
        for s in [[x.termX] for x in rule.body if x.type == 'constraint']:
            if isUpperCase(s):
                pList.extend(s)
        for s in [[x.termY] for x in rule.body if x.type == 'constraint']:
            if isUpperCase(s):
                pList.extend(s)
        remove = False
        for p in pList:
            if p not in bList:
                rules.remove(rule)
                warning = True
                remove = True
                break
        if remove:
            continue
        bList = []
        nList = []
        for s in [x.terms for x in rule.body if x.type == 'predicate' and not x.isNegated]:
            bList.extend(s)
        for s in [x.terms for x in rule.body if x.type == 'predicate' and x.isNegated]:
            nList.extend(s)
        remove = False
        for p in nList:
            if p not in bList:
                rules.remove(rule)
                warning = True
                remove = True
                break
        if remove:
            continue
        if isLowerCaseList(rule.head.terms):
            break
        for t in rule.head.terms:
            vList = []
            for s in [x.terms for x in rule.body if x.type == 'predicate']:
                vList.extend(s)

            if t not in vList:
                rules.remove(rule)
                warning = True
                break

    return


def reset_facts():
    '''Clears record of a fact ever being used'''
    for fact in lists.facts:
        fact.record.clear()

def matchGoals(facts, rule, ruleIndex):  
    negation_list = []
    n_facts = facts.copy()
    for nb in rule.body:
        if nb.type == 'predicate' and nb.isNegated:
            b_facts = get_facts_by_predicate(n_facts, nb.predicate)
            if isLowerCaseList(nb.terms):
                if nb.terms in [x.fact.terms for x in b_facts]:
                    return
            else:
                for b_fact in b_facts:
                    if len(b_fact.fact.terms) == len(nb.terms):
                        termsKey = nb.terms.copy()
                        termsValue = b_fact.fact.terms.copy()
                        for i in range(len(nb.terms)):
                            if isLowerCase(nb.terms[i]):
                                if b_fact.fact.terms[i] != nb.terms[i]:
                                    break
                                termsKey.remove(nb.terms[i])
                                termsValue.remove(b_fact.fact.terms[i])
                            if i == len(nb.terms)-1 and checkUnifiable(tuple(termsKey), termsValue):
                                negation_list.append({tuple(termsKey):termsValue})
                                n_facts.remove(b_fact)
    binding = {}

    semiDict = []
    restBody = rule.body.copy()
    if lists.SEMI_NAIVE_IMPLEMENTATION:
        restBody.clear()

        nonLinearBody = {}
        tempBody = rule.body.copy()
        while len(tempBody) != 0:
            body = tempBody[0]
            if body.type == 'predicate' and not body.isNegated:
                b = [x for x in rule.body if x.type == 'predicate' and x.predicate == body.predicate]
                if len(b) == 2:
                    for bb in b:
                        tempBody.remove(bb)
                    nonLinearBody[body.predicate] = b
                else:
                    restBody.append(body)
                    tempBody.remove(body)
            else:
                restBody.append(body)
                tempBody.remove(body)


        for key, value in nonLinearBody.items():
            incremental_facts = get_facts_by_predicate(facts, key)
            path_facts = get_facts_by_predicate(lists.PATH, key)

            for b_fact in incremental_facts:
                if not unifyBinding(b_fact.fact, value[0], binding):
                    continue
            for b_fact in incremental_facts:
                if not unifyBinding(b_fact.fact, value[1], binding):
                    continue
            semiDict.extend(globalUnify(binding, rule.body, negation_list))

            for b_fact in incremental_facts:
                if not unifyBinding(b_fact.fact, value[0], binding):
                    continue
            for b_fact in path_facts:
                if not unifyBinding(b_fact.fact, value[1], binding):
                    continue
            semiDict.extend(globalUnify(binding, rule.body, negation_list))

            for b_fact in path_facts:
                if not unifyBinding(b_fact.fact, value[0], binding):
                    continue
            for b_fact in incremental_facts:
                if not unifyBinding(b_fact.fact, value[1], binding):
                    continue
            semiDict.extend(globalUnify(binding, rule.body, negation_list))
        if len(restBody) == 0 and semiDict:
            return matchHeader(rule, binding, facts, semiDict)


    for b in range(len(restBody)):
        body = rule.body[b]

        if body.type == 'predicate':
            if body.isNegated:
                continue

            b_facts = get_facts_by_predicate(n_facts, body.predicate, ruleIndex, b)
            if isLowerCaseList(body.terms):
                exist = body.terms in [x.fact.terms for x in b_facts]
                if exist == body.isNegated:
                    return
                else:
                    continue

            if len(b_facts) == 0:
                return
            for b_fact in b_facts:
                if not unifyBinding(b_fact.fact, body, binding):
                    continue
        if not binding:
            break
    if not binding and isLowerCaseList(rule.head.terms):
        fact = Fact(rule.head)
        return [] if checkFactExist(facts, fact) else [fact]
    dict = globalUnify(binding, rule.body, negation_list)
    dict.extend(semiDict)
    return matchHeader(rule, binding, facts, dict)

def filterBinding(binding, variable):
    for value in binding.values():
        for key in value.keys(): 
            for l in value[key].copy(): 
                for i in range(len(l)):
                    if l[i] not in variable[key[i]] and l in value[key]:
                        value[key].remove(l)

def globalUnify(binding, body, negation_list):
    variable = bindingToVariable(binding, body, negation_list)
    builtInVariable, builtInBody = getBuiltInTerm(body)
    dict = []
    for value in binding.values():
        for key, v in value.items():
            dictNew = getDicFromTuplesByTerm(key, v, builtInVariable, builtInBody)
            filterDicByNewTermDic(dict, dictNew)
    return dict


def getBuiltInTerm(body):
    builtInBody = []
    builtInVariable = set()
    for b in body:
        if b.type == 'constraint':
            builtInBody.append(b)
            if not isLowerCase(b.termX):
                builtInVariable.add(b.termX)
            if not isLowerCase(b.termY):
                builtInVariable.add(b.termY)
    return builtInVariable, builtInBody

def checkBodyNegative(predicate, key, body):
    return next(
        (
            b.isNegated
            for b in body
            if b.type == 'predicate'
            and b.predicate == predicate
            and b.terms == list(key)
        ),
        False,
    )

def checkUnifiable(key, value):
    dict = {}
    for i in range(len(key)):
        if key[i] not in dict:
            dict[key[i]] = set()
        dict[key[i]].add(value[i])
    return all(len(v) == 1 for v in dict.values())


def bindingToVariable(binding, body, negation_list):
    variable = {}
    negativeValue = []
    for bindingKey, value in binding.items():
        for key, keyValue in value.items():
            localVariable = {}
            for v in value[key].copy():
                if {key:v} in negation_list or not checkUnifiable(key, v):
                    value[key].remove(v)
            for i in range(len(key)): #(X, X)
                listNew = [v[i] for v in value[key]]
                list = listNew
                if key[i] in variable:
                    list = variable[key[i]]
                variable[key[i]] = set(listNew).intersection(list)
    return variable

def mergeTwoDict(dict1, dict2):
    for key, value in dict1.items():
        if key in dict2.keys() and value != dict2[key]:
            return
    dict = dict1.copy()
    dict1.update(dict2)
    for key, value in dict1.items():
        if key in dict.keys():
            dict1[key] = value.union(dict[key])
    if not checkIfDicSetUnifiable(dict1):
        return
    return dict1

def getDicFromTuplesByTerm(key, value, builtInVariable, builtInBody):
    dictList = []
    for v in value:
        dic = {key[i]: {v[i]} for i in range(len(key))}
        if set(key) >= builtInVariable and len(builtInVariable) > 0 and not evaluateBuiltInPredicate(dic, builtInBody):
            continue
        dictList.append(dic)
    return dictList

def checkIfDicSetUnifiable(dict):
    return all(len(value) == 1 for key, value in dict.items())

def filterDicByNewTermDic(dict, dictNew):
    if len(dict) == 0:
        dict.extend(dictNew)
        return
    filterList = []
    for dic in dict:
        for d in dictNew:
            dicFilter = dic.copy()
            logdic = dicFilter.copy()
            if newDic := mergeTwoDict(dicFilter, d):
                filterList.append(dicFilter)
    list = filterList.copy()
    for f in list:
        if not checkIfDicSetUnifiable(f):
            filterList.remove(f)
    dict.clear()
    dict.extend(filterList)

def matchHeader(rule, binding, facts, dict):
    header = rule.head
    builtInVariable, builtInBody = getBuiltInTerm(rule.body)
    newFacts = []
    for d in dict:
        if evaluateBuiltInPredicate(d, builtInBody):
            term = [list(d[x])[0] for x in header.terms]
            fact = Fact(Predicate(header.predicate, term, header.isNegated))
            if not (checkFactExist(facts, fact) or checkFactExist(newFacts, fact)):
                newFacts.append(fact)
    return newFacts

def checkConstraint(dict, cons, verbose=True):

    if isLowerCase(cons.termX):
        x = cons.termX
    elif isinstance(dict[cons.termX], set):
        x = list(dict[cons.termX])[0]
    else:
        x = dict[cons.termX]
    if isLowerCase(cons.termY):
        y = cons.termY
    elif isinstance(dict[cons.termY], set):
        y = list(dict[cons.termY])[0]
    else:
        y = dict[cons.termY]

    if x and y:
        operator = cons.operator
        if operator == ">=":
            return x >= y
        elif operator == "<=":
            return x <= y
        elif operator == ">":
            return x > y
        elif operator == "<":
            return x < y
        elif "!" in operator:
            return x != y
        elif operator in ["==", "="]:
            return x == y
        else:
            return False

def evaluateBuiltInPredicate(dict, builtin, verbose=True):

    return not any(
        body.type == 'constraint' and not checkConstraint(dict, body, verbose)
        for body in builtin
    )

def checkFactExist(facts, fact):
    for fs in facts:
        if fs.fact == fact.fact:
            return True
    return any(fs.fact == fact.fact for fs in lists.PATH)


def unifyBinding(p1, p2, binding):
    if len(p1.terms) != len(p2.terms):
        return False
    variable = binding[p2.predicate] if p2.predicate in binding.keys() else {}
    termsKey = p2.terms.copy()
    termsValue = p1.terms.copy()
    for i in range(len(p2.terms)):
        if isLowerCase(p2.terms[i]):
            if p1.terms[i] != p2.terms[i]:
                return False
            termsKey.remove(p2.terms[i])
            termsValue.remove(p1.terms[i])
    value = variable[tuple(termsKey)] if tuple(termsKey) in variable.keys() else []
    value.append(termsValue)
    variable[tuple(termsKey)] = value
    binding[p2.predicate] = variable
    return True
def isUpperCaseList(list):
    return all(i[0].isupper() for i in list)

def isLowerCaseList(list):
    return not any(i[0].isupper() for i in list)

def isUpperCase(c):
    return c[0].isupper()

def isLowerCase(c):
    return not c[0].isupper()

def get_facts_by_predicate(facts, name, ruleIndex=None, bodyIndex=None, termLength=None):
    if ruleIndex and bodyIndex:
        return (
            [
                x
                for x in facts
                if f"{ruleIndex}.{bodyIndex}" not in x.record
                and x is not None
                and x.fact.predicate == name
                and len(x.fact.terms) == termLength
            ]
            if termLength
            else [
                x
                for x in facts
                if f"{ruleIndex}.{bodyIndex}" not in x.record
                and x is not None
                and x.fact.predicate == name
            ]
        )
    if termLength:
        return [x for x in facts if x is not None and x.fact.predicate == name and len(x.fact.terms) == termLength]
    else:
        return [x for x in facts if x is not None and x.fact.predicate == name]