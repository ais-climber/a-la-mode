import sys
import os
sys.path.append(os.path.abspath('../../'))

import networkx as nx

from alamode.activation_functions import binary_step
from alamode.FeedforwardNet import FeedforwardNet
from alamode.InterpretedNet import InterpretedNet
from alamode.PrefModel import PrefModel
from alamode.model_building import *

import pytest

#--------------------------------------------------------------------
# Tests for activation functions
#--------------------------------------------------------------------

# TODO: Unit tests for 

#--------------------------------------------------------------------
# Tests for Feedforward Nets and Interpreted Nets
#--------------------------------------------------------------------

#------------------------------------------------
# Net 0: Trivial zero-node graph
#------------------------------------------------
nodes0 = []
graph0 = nx.DiGraph()
graph0.add_weighted_edges_from([])
rate0 = 1.0
prop_map0 = dict({})
net0 = FeedforwardNet(nodes0, graph0, binary_step, rate0)
interp0 = InterpretedNet(net0, prop_map0)

#------------------------------------------------
# Net 1: Trivial one-node graph
#------------------------------------------------
nodes1 = ['a']
graph1 = nx.DiGraph()
graph1.add_weighted_edges_from([])
rate1 = 1.0
prop_map1 = {'P': {'a'}, 'Q': set({})}
net1 = FeedforwardNet(nodes1, graph1, binary_step, rate1)
interp1 = InterpretedNet(net1, prop_map1)

#------------------------------------------------
# Net 2: The 'penguin_neural.py' example Net.
#   Irreflexive, anti-transitive, and acyclic
#------------------------------------------------
nodes2 = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h']
graph2 = nx.DiGraph()
graph2.add_weighted_edges_from(
    [['a', 'f', 1.0], ['b', 'f', 0.0], ['c', 'f', 0.0],
     ['d', 'f', 0.0], ['e', 'f', 0.0], ['a', 'g', 0.0],
     ['b', 'g', -2.0], ['c', 'g', 3.0], ['d', 'g', 3.0],
     ['e', 'g', 3.0], ['f', 'h', 2.0], ['g', 'h', -2.0]])
rate2 = 1.0
prop_map2 = {'P': {'a'}, 'R': {'a', 'b'}, 
            'S': {'b', 'c'}, 'T': {'b', 'd'}, 
            'U': {'b', 'e'}, 'Q': {'h'}}
net2 = FeedforwardNet(nodes2, graph2, binary_step, rate2)
interp2 = InterpretedNet(net2, prop_map2)

#------------------------------------------------
# Net 3: A FeedforwardNet that is reflexive
#   in places, transitive in places, but still
#   acyclic.
#------------------------------------------------
# TODO

#------------------------------------------------
# Net 4: A FeedforwardNet that is completely
#   reflexive and transitive, but of course still
#   acyclic
#------------------------------------------------
# TODO

#------------------------------------------------
# Net 5: TODO
#------------------------------------------------
# TODO 

# TODO: Unit tests for reach
# TODO: Unit tests for inverse_reach
# TODO: Unit tests for propagate
# TODO: Unit tests for hebb_update
# TODO: Unit tests for _parse
# TODO: Unit tests for _eval
# TODO: Unit tests for _interpret
# TODO: Unit tests for is_model
# TODO: Unit tests for is_model_of_rule

#--------------------------------------------------------------------
# Tests for Preferential (Neighborhood) Models
#--------------------------------------------------------------------

#------------------------------------------------
# Model 0: Trivial zero-element model
#------------------------------------------------
worlds0 = set([])
f0 = dict({})
g0 = dict({})
prop_map0 = dict({})
model0 = PrefModel(worlds0, f0, g0, prop_map0)

#------------------------------------------------
# Model 1: Trivial one-element model
#------------------------------------------------
worlds1 = set(['a'])
f1 = { 'a': [{'a'}] }
g1 = { 'a': [ ] }
prop_map1 = { ('P', 'a') : True, ('Q', 'a') : False }
model1 = PrefModel(worlds1, f1, g1, prop_map1)

#------------------------------------------------
# Model 2: A full Preferential Model, with
#   all the properties.  Also has non-monotonic g
#   Note that we got this model by converting
#   from a Feedforward Net.
#------------------------------------------------
worlds2 = set(['a', 'b', 'c'])
f2 = { 'a': [{'c', 'a'}, {'a'}, {'c', 'a', 'b'}, {'a', 'b'}],
      'b': [{'a', 'b'}, {'c', 'a', 'b'}, {'c', 'b'}, {'b'}],
      'c': [{'c', 'a', 'b'}] }
g2 = { 'a': [{'c', 'a'}, {'a'}, {'c', 'a', 'b'}, {'a', 'b'}],
      'b': [{'a', 'b'}, {'c', 'a', 'b'}, {'c', 'b'}, {'b'}],
      'c': [{'c', 'a'}, {'c', 'a', 'b'}, {'c'}] }
prop_map2 = { ('P', 'c'): True, ('P', 'a'): False, ('P', 'b'): True, 
             ('R', 'c'): True, ('R', 'a'): False, 
             ('R', 'b'): False, ('Q', 'c'): False, 
             ('Q', 'a'): True, ('Q', 'b'): True }
model2 = PrefModel(worlds2, f2, g2, prop_map2)

#------------------------------------------------
# Model 3: A model that satisfies all of
#   the properties *except* the interaction
#   properties
#------------------------------------------------
# TODO

#------------------------------------------------
# Model 4: A model where f is a filter, and
#   we have the interaction properties, but
#   g is neither reflexive nor transitive.
#------------------------------------------------
# TODO

#------------------------------------------------
# Model 5: A model that satisfies *none* of
#   the Preferential Model properties.
#------------------------------------------------
# TODO 

# TODO: Unit tests for _parse
# TODO: Unit tests for _eval
# TODO: Unit tests for interpret
# TODO: Unit tests for is_model
# TODO: Unit tests for is_model_of_rule

def test_core():
    # TODO: core tests for model0
    #   Is this well-defined?  Should I test for
    #   not being well-defined?

    assert model1.core(model1.f, 'a') == {'a'}
    assert model1.core(model1.g, 'a') == {'a'}

    assert model2.core(model2.f, 'a') == {'a'}
    assert model2.core(model2.f, 'b') == {'b'}
    assert model2.core(model2.f, 'c') == {'c', 'a', 'b'}
    assert model2.core(model2.g, 'a') == {'a'}
    assert model2.core(model2.g, 'b') == {'b'}
    assert model2.core(model2.g, 'c') == {'c'}

    # TODO: test model3, model4, model5

def test_is_closed_under_fin_intersection():
    assert model0.is_closed_under_fin_intersection(model0.f) == True
    assert model0.is_closed_under_fin_intersection(model0.g) == True

    assert model1.is_closed_under_fin_intersection(model1.f) == True
    assert model1.is_closed_under_fin_intersection(model1.g) == True

    assert model2.is_closed_under_fin_intersection(model2.f) == True
    assert model2.is_closed_under_fin_intersection(model2.g) == True

    # TODO: test model3, model4, model5

def test_is_closed_under_superset():
    assert model0.is_closed_under_superset(model0.f) == True
    assert model0.is_closed_under_superset(model0.g) == True

    assert model1.is_closed_under_superset(model1.f) == True
    assert model1.is_closed_under_superset(model1.g) == True

    assert model2.is_closed_under_superset(model2.f) == True
    assert model2.is_closed_under_superset(model2.g) == False

    # TODO: test model3, model4, model5

def test_is_reflexive():
    assert model0.is_reflexive(model0.f) == True
    assert model0.is_reflexive(model0.g) == True

    assert model1.is_reflexive(model1.f) == True
    assert model1.is_reflexive(model1.g) == True

    assert model2.is_reflexive(model2.f) == True
    assert model2.is_reflexive(model2.g) == True

    # TODO: test model3, model4, model5

def test_is_transitive():
    assert model0.is_transitive(model0.f) == True
    assert model0.is_transitive(model0.g) == True

    assert model1.is_transitive(model1.f) == True
    assert model1.is_transitive(model1.g) == True

    assert model2.is_transitive(model2.f) == True
    assert model2.is_transitive(model2.g) == True

    # TODO: test model3, model4, model5

def test_is_acyclic():
    pass

def test_g_contains_f():
    assert model0.g_contains_f(model0.f, model0.g) == True
    assert model1.g_contains_f(model1.f, model1.g) == False
    assert model2.g_contains_f(model2.f, model2.g) == True

    # TODO: test model3, model4, model5

def test_f_is_skeleton_of_g():
    assert model0.f_is_skeleton_of_g(model0.f, model0.g) == True
    assert model1.f_is_skeleton_of_g(model1.f, model1.g) == True
    assert model2.f_is_skeleton_of_g(model2.f, model2.g) == True

    # TODO: test model3, model4, model5

#--------------------------------------------------------------------
# Tests for Model-Building
#--------------------------------------------------------------------

#------------------------------------------------
# Built Models: Preferential Models built from
#   our Interpreted Nets above
#------------------------------------------------
built_model0 = PrefModel_from_InterpretedNet(interp0)
built_model1 = PrefModel_from_InterpretedNet(interp1)
built_model2 = PrefModel_from_InterpretedNet(interp2)
# TODO: Do the same for model3, model4, model5

#------------------------------------------------
# Built Nets: Neural networks built from our
#   Preferential Models above.
#------------------------------------------------
built_net0 = InterpretedNet_from_PrefModel(model0)
built_net1 = InterpretedNet_from_PrefModel(model1)
built_net2 = InterpretedNet_from_PrefModel(model2)
# TODO: Do the same for model3, model4, model5

#------------------------------------------------
# We will check that our model-building procedures
# preserve truth for the following test formulas.
#------------------------------------------------
test_formulas = [
    # Modal axioms for know
    "(know (P and Q)) <-> (know P and know Q)",
    "(know P) -> P",
    "(know P) -> P",
    "(know P) -> (know know P)",
    "(know ((know (P -> (know P))) -> P)) -> P",

    # Modal axioms for typ
    "(typ P) -> P",
    "(typ P) -> (typ typ P)",

    # Interaction axioms
    "(know P) -> (typ P)"
    # TODO: Skeleton axiom

    # Some non-axioms that are only true for *some* models/nets
    # TODO: come up with clever ones based on our models/nets above
]

def test_PrefModel_from_InterpretedNet():
    # We test each model separately so that it's clearer which
    # test failed.
    # TODO: Do permutations of propositions, just to exercize
    #   more interpretations.
    for fml in test_formulas:
        assert built_model0.is_model(fml) == interp0.is_model(fml)

    for fml in test_formulas:
        assert built_model1.is_model(fml) == interp1.is_model(fml)
        print(built_model1.is_model(fml))

    for fml in test_formulas:
        assert built_model2.is_model(fml) == interp2.is_model(fml)
        print(built_model2.is_model(fml))

def test_InterpretedNet_from_PrefModel():
    # We test each model separately so that it's clearer which
    # test failed.
    for fml in test_formulas:
        assert built_net0.is_model(fml) == model0.is_model(fml)

    for fml in test_formulas:
        assert built_net1.is_model(fml) == model1.is_model(fml)

    for fml in test_formulas:
        assert built_net2.is_model(fml) == model2.is_model(fml)

    # TODO: test model3, model4, model5

if __name__ == "__main__":
    pytest.main()