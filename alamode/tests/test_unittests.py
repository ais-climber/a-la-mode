import sys
import os
sys.path.append(os.path.abspath('../../'))

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
# Tests for Feedforward Nets
#--------------------------------------------------------------------

# TODO: Make six different Feedforward Nets:
#   - One that is 'trivial' -- empty net, etc.
#   - One that is 'trivial' with graph of size 1
#   - One that is *reflexive but ow acyclic*, just to double-check that the acyclic assert works
#   - One that is just a huge, deep, complicated net.
#   - One that is designed to learn nothing new after Hebbian update
#   - One that is designed to learn something new after Hebbian update

# TODO: Unit tests for 

#--------------------------------------------------------------------
# Tests for Interpreted Nets
#--------------------------------------------------------------------

# (for each of the nets above, make 2 different propositional valuations, varying overlap)

# TODO: Unit tests for 

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
             ('Q', 'c'): True, ('Q', 'a'): False, 
             ('Q', 'b'): False, ('R', 'c'): False, 
             ('R', 'a'): True, ('R', 'b'): True }
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

# TODO: Unit tests for PrefModel_from_InterpretedNet
#       Use the interpreted nets above, convert them to pref models,
#        and double-check that
#          1) the properties that held before still hold, and
#          2) the properties that *didn't* hold before still *don't* hold
# TODO: Unit tests for InterpretedNet_from_PrefModel
#       Do the same, but using the preferential models above.

if __name__ == "__main__":
    pytest.main()