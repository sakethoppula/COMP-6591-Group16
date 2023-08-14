from utils import matchGoals, print_to_output_file, EDB_int
import lists

def semi_naive_recursion(EDB, incremental, rules):
    originIncremental = incremental.copy()
    recursionFacts = []
    incremental.extend(EDB)
    for i in range(len(rules)):
        rule = rules[i]
        if not {
            x.predicate for x in rule.body if x.type == 'predicate'
        }.intersection({x.fact.predicate for x in originIncremental}):
            continue
        newFacts = matchGoals(incremental, rule, i)

        if not newFacts:
            continue
        for f in newFacts:
            print_to_output_file(f"nf: {f}\n")
        recursionFacts.extend(newFacts)

    return recursionFacts

def semi_naive_engine(EDB, rules):
    incremental = EDB_int(EDB, rules)
    lists.PATH.extend(incremental)
    recursionFacts = semi_naive_recursion(EDB, incremental, rules)
    if len(recursionFacts) == 0:
        return
    while len(recursionFacts) != 0:
        lists.PATH.extend(recursionFacts)
        recursionFacts = semi_naive_recursion(EDB, recursionFacts, rules)