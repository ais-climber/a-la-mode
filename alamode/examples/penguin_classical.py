# This is the penguin example, re-done in classical preferential models.
# (This is just a test to make sure I implemented neighborhood models correctly.)

import os
os.environ['TF_CPP_MIN_LOG_LEVEL'] = '3'
from alamode.PrefModel import PrefModel

# I got the following neighborhood model from this neural net:
#       nodes = set(['a', 'b', 'c'])
#       layers = [['a', 'b'], ['c']]
#       weights = { ('a', 'c'): 1.0, ('b', 'c'): -2.0 }
#       threshold = 0.0
#       rate = 1.0
#       prop_map = {'bird': {'a'}, 'penguin': {'a', 'b'}, 'flies': {'c'}}
# 
# In both, we should expect:
#       penguin -> bird :  True
#       bird => flies :  True
#       penguin => flies :  False

worlds = set(['a', 'b', 'c'])

f = { 'a': {('c', 'a'), ('a',), ('c', 'a', 'b'), ('a', 'b')}, 
      'b': {('a', 'b'), ('c', 'a', 'b'), ('c', 'b'), ('b')},
      'c': {('c', 'a', 'b')} }

g = { 'a': {('c', 'a'), ('a',), ('c', 'a', 'b'), ('a', 'b')},
      'b': {('a', 'b'), ('c', 'a', 'b'), ('c', 'b'), ('b')},
      'c': {('c', 'a'), ('c', 'a', 'b'), ('c')} }

prop_map = { ('bird', 'c'): True, ('bird', 'a'): False, ('bird', 'b'): True, 
             ('penguin', 'c'): True, ('penguin', 'a'): False, 
             ('penguin', 'b'): False, ('flies', 'c'): False, 
             ('flies', 'a'): True, ('flies', 'b'): True }

model = PrefModel(worlds, f, g, prop_map)

print("penguin -> bird : ", model.is_model("penguin -> bird"))
print("bird => flies : ", model.is_model("(typ bird) -> flies"))
print("penguin => flies : ", model.is_model("(typ penguin) -> flies"))
print("penguin -> flies : ", model.is_model("penguin -> flies"))
print()


# TODO: Error in code -- both of these give False, but only one can be false!
# print("penguin -> flies : ", model.is_model("penguin -> flies"))
# print("not (penguin -> flies) : ", model.is_model("not (penguin -> flies)"))