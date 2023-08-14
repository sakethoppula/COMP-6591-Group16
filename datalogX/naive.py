from utils import reset_facts, matchGoals, print_to_output_file
import lists

def naive_engine(facts, rules):
    '''Driver file for initiation of Naive method of bottom up eval'''
    while True:
        rules_facts = []
        reset_facts()
        for i in range(len(rules)):
            rule = rules[i]
            if newFacts := matchGoals(facts, rule, i):
                rules_facts.extend(newFacts)
        if not rules_facts:
            break
        for f in rules_facts:
            print_to_output_file(f"nf: {f}\n")
        facts.extend(rules_facts)
