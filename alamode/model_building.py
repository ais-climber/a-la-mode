"""
Functions to actually build Interpreted Nets and Preferential Models.
"""
from alamode.PrefModel import PrefModel
from alamode.old_tensorflow_keras.Net import Net
from alamode.InterpretedNet import InterpretedNet

from itertools import chain, combinations
from tensorflow import Tensor

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
        f = {w : set([X for X in powerset 
                      if w not in model.net.reach(worlds.difference(set(X)))]) 
                for w in worlds}
        
        # g(w) = {X | w ∉ Propagate(X^C)}
        g = {w : set([X for X in powerset 
                      if w not in model.net.propagate(worlds.difference(set(X)))]) 
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

        # TODO: get layers from the graph edges somehow...
        # layers = [['a', 'b', 'c', 'd', 'e'], ['f', 'g'], ['h']]
        

        # Note that weights are picked arbitrarily; the activation
        # function is not actually going to use them.
        ARBITRARY_WEIGHT = 0.0
        weights = {(u, v) : ARBITRARY_WEIGHT 
                        for u in nodes for v in nodes
                        if u in model.core(model.f, v)}

        # TODO: Get the m_i that correspond to this x... somehow?
        # What type is the activation function in Tensorflow?
        # 
        def activation_function(x : Tensor) -> Tensor:
            pass

        propositions = list(set([pair[0] for pair in model.prop_map.keys()]))
        net_prop_map = {p : set([n for n in nodes if model.prop_map[(p, n)] == True]) 
                            for p in propositions}

        # TODO: We currently do not support learning rates in the translation!
        # net = Net(nodes, layers, weights, activation_function, rate=None)
        # return InterpretedNet(net, net_prop_map)

        pass