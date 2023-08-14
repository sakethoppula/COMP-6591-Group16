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

from semi_naive import semi_naive_recursion, semi_naive_engine
from naive import naive_engine
from utils import check_program_validity,print_to_output_file
import lists


def main(file):
    '''
    Main function that processes the input file by calling the Parser block and then performs safety checks and then initiates generation 
    of the fixed point.
    '''
    parser = Parser_block.compiler.parser
    program = parser.parse(file.read())
    for e in Parser_block.compiler.errorList:     
        print_to_output_file(e)
    if not program:
        print('Invalid Input')
        return
    for p in program:
        if p.type == 'fact':
            lists.facts.append(p)
        elif p.type == 'rule':
            lists.rules.append(p)

    #calls the saftey checker
    check_program_validity(lists.facts, lists.rules)

    #Define a graph for the rules
    G = nx.DiGraph() 
    
    #print facts to file
    print_to_output_file("FACT:\n")
    for f in lists.facts:
        print_to_output_file(str(f) + "\n")

    #print rules to file
    negated = False
    print_to_output_file("\nRULE:\n")
    for r in lists.rules:
        print_to_output_file(str(r) + "\n")
        for body in r.body:
            if body.type == 'predicate':
                weight = 1
                if body.isNegated:
                    weight = 0
                    negated = True
                edge = (body.predicate, r.head.predicate)

                if body.predicate == r.head.predicate:
                    G.add_node(body.predicate)
                else:
                    G.add_edge(body.predicate, r.head.predicate)


    nx.draw(G)
    plt.savefig("network.png")
    #Prepare to generate new facts
    print_to_output_file("\n{}\n".format("\nNEW FACTS:\n"))


    cycle = list(nx.simple_cycles(G))

    if not cycle:
        depends = nx.topological_sort(G) #Uses topological sorting to produce linear ordering of nodes
        dependsList = list(depends)
        if not dependsList:
            return

    if not lists.SEMI_NAIVE_IMPLEMENTATION:
        naive_engine(lists.facts, lists.rules)
    else:
        semi_naive_engine(lists.facts, lists.rules)



if __name__ == '__main__':
    # lists.initialize()
    print("Welcome to DatalogX!")

    display_text = '''
Please select an option from the list below
1. Run Naive evaluation with Input.pl
2. Run Semi-Naive evaluation with Input.pl
3. Run both evaualtions and compare times for Input.pl
'''
    print(os.getcwd())
    output_sentence = "Please find the results generated in p.res file"
    
    print(display_text)
    choice = int(input("Enter your choice: "))
    if choice == 1:
        lists.SEMI_NAIVE_IMPLEMENTATION = False
        start = time.time()
        #change to your local file path here 
        file = open("C:\\Users\\Saketh\\Downloads\\COMP6591_Group16-main\\COMP6591_Group16-main\\Datalog-master\\input.pl", 'r')
        main(file)
        print(f"Total time: {time.time() - start} seconds")
        print(output_sentence)
        print('='*100 + '\n')
        
    elif choice == 2:
        lists.SEMI_NAIVE_IMPLEMENTATION = True
        #change to your local file path here 
        file = open("C:\\Users\\Saketh\\Downloads\\COMP6591_Group16-main\\COMP6591_Group16-main\\Datalog-master\\input.pl", 'r')
        start = time.time()
        main(file)
        print(f"Total time: {time.time() - start} seconds")
        print(output_sentence)
        print('='*100 + '\n')
    elif choice == 3:
        lists.SEMI_NAIVE_IMPLEMENTATION = False
        start = time.time()
        #change to your local file path here 
        file = open("C:\\Users\\Saketh\\Downloads\\COMP6591_Group16-main\\COMP6591_Group16-main\\Datalog-master\\input.pl", 'r')
        main(file)
        print(f"Total time for Naive Evaluation: {time.time() - start} seconds")

        lists.SEMI_NAIVE_IMPLEMENTATION = True
        #change to your local file path here 
        file = open("C:\\Users\\Saketh\Downloads\\COMP6591_Group16-main\\COMP6591_Group16-main\\Datalog-master\\input.pl", 'r')
        start = time.time()
        main(file)
        print(f"Total time for Semi Naive Evaluation: {time.time() - start} seconds")
        print('='*100 + '\n')



   