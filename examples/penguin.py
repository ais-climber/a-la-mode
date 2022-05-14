# This example serves to illustrate how Hebbian learning can update
# a net's knowledge of conditional statements, e.g. how a net that thinks that
#     birds fly, and
#     penguins in particular fly
# can come to believe that
#     birds (typically) fly, but
#     penguins do not fly
# We rely on the neural network already knowing
# certain animals (that share features with penguins)
# that *don't* fly.

from neuralsemantics.core.BFNN import *
from neuralsemantics.core.Model import *

nodes = set(['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'])
layers = [['a', 'b', 'c', 'd', 'e'], ['f', 'g'], ['h']]
weights = {('a', 'f'): 1.0, ('a', 'g'): 0.0, 
           ('b', 'f'): 0.0, ('b', 'g'): -2.0, 
           ('c', 'f'): 0.0, ('c', 'g'): 3.0, 
           ('d', 'f'): 0.0, ('d', 'g'): 3.0,
           ('e', 'f'): 0.0, ('e', 'g'): 3.0,
           ('f', 'h'): 2.0, ('g', 'h'): -2.0}
threshold = 0.0
rate = 1.0
prop_map = {'bird': {'a'}, 'penguin': {'a', 'b'}, 
            'orca': {'b', 'c'}, 'zebra': {'b', 'd'}, 
            'panda': {'b', 'e'}, 'flies': {'h'}}

net = BFNN(nodes, layers, weights, threshold, rate)
model = Model(net, prop_map)

print("penguin → bird : ", model.is_model("penguin → bird"))
print("bird ⇒ flies : ", model.is_model("bird ⇒ flies"))
print("penguin ⇒ flies : ", model.is_model("penguin ⇒ flies"))
print()
print("orca+ zebra+ panda+ (bird ⇒ flies) : ", model.is_model("orca+ (zebra+ (panda+ (bird ⇒ flies)))")) # should be True
print("orca+ zebra+ panda+ (penguin ⇒ flies) : ", model.is_model("orca+ (zebra+ (panda+ (penguin ⇒ flies)))")) # should be False

# Is this a counterexample to monotonicity?
print(model.is_model("(orca+ (orca+ (orca+ (◻penguin)))) → (orca+ (orca+ (orca+ (◻bird))))")) # Hope it is False