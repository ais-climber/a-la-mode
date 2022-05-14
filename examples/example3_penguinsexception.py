from neuralsemantics.core.model import *

nodes = set(['a', 'b', 'c', 'd', 'e', 'f'])
layers = [['a', 'b', 'c'], ['d', 'e'], ['f']]
weights = {('a', 'd'): 0.0, ('a', 'e'): 1.0, 
           ('b', 'd'): 0.0, ('b', 'e'): 1.0, 
           ('c', 'd'): 1.0, ('c', 'e'): 1.0, 
           ('d', 'f'): -2.0, ('e', 'f'): 2.0}
threshold = 0.0
rate = 1.0
prop_map = {'bird': {'b'}, 'robin': {'a', 'b'}, 'penguin': {'b', 'c'}, 'flies': {'f'}}

net = BFNN(nodes, layers, weights, threshold, rate)
model = Model(net, prop_map)

print("penguin → bird : ", model.is_model("penguin → bird"))
print("bird ⇒ flies : ", model.is_model("bird ⇒ flies"))
print("(bird ∧ penguin) ⇒ flies : ", model.is_model("(bird ∧ penguin) ⇒ flies"))