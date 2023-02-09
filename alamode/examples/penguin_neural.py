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

import os
os.environ['TF_CPP_MIN_LOG_LEVEL'] = '3'
from alamode.Net import Net
from alamode.InterpretedNet import InterpretedNet

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

net = Net(nodes, layers, weights, threshold, rate)
model = InterpretedNet(net, prop_map)

print("penguin -> bird : ", model.is_model("penguin -> bird"))
print("bird => flies : ", model.is_model("(typ bird) -> flies"))
print("penguin => flies : ", model.is_model("(typ penguin) -> flies"))
print()

birds_fly = "orca :: zebra :: panda :: ((typ bird) -> flies)"
penguins_dont_fly = "orca :: zebra :: panda :: ((typ penguin) -> flies)"

print(f"{birds_fly} : ", model.is_model(birds_fly)) # should be True
print(f"{penguins_dont_fly} : ", model.is_model(penguins_dont_fly)) # should be False
# TODO: Last sentence is not working!
#       (means Hebbian update is probably broken...)
