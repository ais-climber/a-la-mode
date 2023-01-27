from alamode.Net import Net
from alamode.InterpretedNet import InterpretedNet

import random as rand
import itertools
from random import randint
import numpy as np
import math

def random_chunk(li, min_chunk, max_chunk):
    """
    Helper function to partition the list 'li' into randomly
    sized chunks (with at minimum 'min_chunk' elements and
    at maximum 'max_chunk' elements).

    Author: User roippi, in their answer to
    https://stackoverflow.com/questions/21439011/best-way-to-split-a-list-into-randomly-sized-chunks
    """
    it = iter(li)
    while True:
        nxt = list(itertools.islice(it,randint(min_chunk,max_chunk)))
        if nxt:
            yield nxt
        else:
            break

def precedes(layers, n1, n2):
    """
    Helper function to determine whether node n1 is in
    a layer that immediately precedes the layer of node n2.
    """
    i = [k for k in range(len(layers)) if n1 in layers[k]][0]
    j = [k for k in range(len(layers)) if n2 in layers[k]][0]

    return i + 1 == j

def generate_random_net(max_elements=25):
    """
    Function to generate a random (smallish) BFNN.
    """
    # Note: we require that num_nodes <= 26, since we use the letters of the alphabet
    #     as node names.  (There is no need to generate bigger nets for this.)
    nodes = [chr(i) for i in range(ord('a'), ord('z')+1)][:rand.randint(1, min(max_elements, 25))]
    layers = list(random_chunk(nodes.copy(), 1, math.ceil(len(nodes)/2)))

    weight_vals = list(range(-10, 11))
    weights = {(i, j) : np.random.choice([0.0, rand.choice(weight_vals)], 1, p=[0.15, 0.85])[0]
                for i in nodes for j in nodes if precedes(layers, i, j)}

    # For now we don't vary the threshold and the rate.  (The real action happens
    # when we vary the weights.)
    threshold = 0.0
    rate = 1.0

    return Net(nodes, layers, weights, threshold, rate)

countermodels = dict()
def countermodel_search(formula, n, max_elements=25, premises=[]):
    """
    A function to perform a countermodel search via
    naiive random generate-and-test.

    'premises' is optional.  If given, then we are checking the
    inference rule
        premises
        --------
        formula
    """
    print(f"Searching for a countermodel for {formula}...")

    # Search previously-found countermodels first (i.e. those
    # stored in the 'countermodels' dictionary)
    for (F, model) in countermodels.keys():
        is_model = True
        if premises != []:
            is_model = model.is_model_of_rule(premises, formula)
        else:
            is_model = model.is_model(formula)

        if not(is_model):
            print("Countermodel found!")
            print(f"{formula} fails in this model:")
            print(model)
            return

    # Search randomly generated models
    for i in range(n):
        net = generate_random_net(max_elements)

        # ('::',      2, OpAssoc.RIGHT),
        # ('know',    1, OpAssoc.RIGHT),
        # ('typ',     1, OpAssoc.RIGHT),
        # ('<know>',  1, OpAssoc.RIGHT),
        # ('<typ>',   1, OpAssoc.RIGHT),
        # ('not',     1, OpAssoc.RIGHT),
        # ('and',     2, OpAssoc.LEFT),
        # ('or',      2, OpAssoc.LEFT),
        # ('->',      2, OpAssoc.RIGHT),
        # ('<->',     2, OpAssoc.RIGHT)
        
        # WARNING: the order of special_tokens is important!
        #   e.g. '<know>' must be removed before 'know',
        #    and '<->' must be removed before '->'
        special_tokens = ['::', '<know↓>', 'know↓', '<know>', 'know', '<typ>', 'typ', 'not', 'and', 'or', '<->', '->', '(', ')']

        propositions = []
        for F in premises+[formula]:
            only_props = F

            for token in special_tokens:
                only_props = only_props.replace(token, '')

            propositions += only_props.split()

        propositions = list(set(propositions))
        prop_sets = [set(list(rand.sample(net.nodes, k=rand.randint(1, len(net.nodes))))) for P in propositions]
        
        # alpha = [F.replace('->', '').replace('<->', '').replace('(', '').replace(')', '') 
        #     for F in premises+[formula]
        #     if F not in []]
        # propositions = list(set([word for F in alpha for word in F.split()]))
        
        # We permute the order of the propositions in our mapping
        # in case a specific order gives us a countermodel.
        for prop_order in itertools.permutations(propositions):
            prop_map = {prop_order[i] : prop_sets[i] for i in range(len(propositions))}
            model = InterpretedNet(net, prop_map)

            is_model = True
            if premises != []:
                is_model = model.is_model_of_rule(premises, formula)
            else:
                is_model = model.is_model(formula)

            if not(is_model):
                print("Countermodel found!")
                print(f"{formula} fails in this model:")
                print(model)
                return
    
    print(f"No counterexample found. (Searched {n} randomly-generated models.)\n")

# countermodel_search("(T A) → (T(T A))", 20) # Should come up with no counterexamples
# countermodel_search("A → (T A)", 20, max_elements=5) # Should come up with an easy counterexample