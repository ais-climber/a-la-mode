"""
Functions to actually build Interpreted Nets and Preferential Models.
"""
from alamode.PrefModel import PrefModel
from alamode.FeedforwardNet import FeedforwardNet
from alamode.InterpretedNet import InterpretedNet

import networkx as nx

from itertools import chain, combinations

def PrefModel_from_InterpretedNet(model : InterpretedNet):
        """
        Function to construct a classical Preferential Model from 
        a Neural Net Model.
        """
        # All worlds and sets of worlds.
        # We get the powerset using the usual recipe from
        # https://docs.python.org/3/library/itertools.html#itertools-recipes
        worlds = set(model.net.nodes)
        powerset = list(chain.from_iterable(combinations(list(worlds), r) for r in range(len(list(worlds))+1)))

        # We get the f and g mappings from Reach and Propagate.
        # f(w) = {X | w ∉ Reach(X^C)}
        f = {w : [set(X) for X in powerset 
                      if w not in model.net.reach(worlds.difference(set(X)))]
                 for w in worlds}
        
        # g(w) = {X | w ∉ Propagate(X^C)}
        g = {w : [set(X) for X in powerset 
                      if w not in model.net.propagate(worlds.difference(set(X)))]
                 for w in worlds}

        # The pref_prop_map is just the original prop_map, but it maps
        # to truth values instead of sets.
        # NOTE: Again, in order for the interpretation to work, we need to take
        #       the *complement* of the proposition mapping!!!
        # 
        # TODO: Again, explain why this is what we should expect
        #       (it seems very counterintuitive!)
        # 
        pref_prop_map = {(p, w) : (False if w in model.prop_map[p] else True)
                            for p in model.prop_map.keys()
                            for w in worlds }

        return PrefModel(worlds, f, g, pref_prop_map)


def InterpretedNet_from_PrefModel(model : PrefModel):
        """
        Function to construct a Neural Network model from 
        a Preferential Model.
        """
        nodes = set(model.universe)
        
        # We pick edges intended to match the behavior of f(w).
        # Note that weights are picked arbitrarily; the activation
        # function is not actually going to use them.
        ARBITRARY_WEIGHT = 0.0
        graph = nx.DiGraph()
        graph.add_weighted_edges_from(
            [(u, v, ARBITRARY_WEIGHT)
                for u in nodes for v in nodes
                if u in model.core(model.f, v) and u != v])
        # NOTE: We *force* irreflexivity in the graph, since the network really
        #       shouldn't have self-loops!
        
        # We pick an activation function that is intended to match the behavior of g(w).
        def activation_function(n, m_vec, x_vec, weights_vec):
            size = len(m_vec)
            assert len(x_vec) == size
            assert len(weights_vec) == size

            active_preds = [m_vec[i] for i in range(size) if x_vec[i] == 1.0]
            
            if nodes.difference(active_preds) not in model.g[n]:
                return 1.0
            else:
                return 0.0

        # NOTE: Again, in order for the interpretation to work, we need to take
        #       the *complement* of the proposition mapping!!!
        # 
        # TODO: Again, explain why this is what we should expect
        #       (it seems very counterintuitive!)
        propositions = list(set([pair[0] for pair in model.prop_map.keys()]))
        net_prop_map = {p : set([n for n in nodes if model.prop_map[(p, n)] == False]) 
                            for p in propositions}

        # TODO: We currently do not support learning rates in the translation!
        net = FeedforwardNet(nodes, graph, activation_function, rate=None)
        return InterpretedNet(net, net_prop_map)