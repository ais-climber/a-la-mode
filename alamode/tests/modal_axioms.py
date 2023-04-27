# We check axioms for K, T, and P+ to see if
# we can find any countermodels via a random search.
# 
# We should hope that no countermodels are found
# (since otherwise there is an error in our proofs!)

from alamode.countermodel_search import countermodel_search

#--------------------------------------------------------------------
# Axioms for propositional logic
#--------------------------------------------------------------------

# countermodel_search("A -> A", 1000)
# countermodel_search("A -> (B -> A)", 1000)
# countermodel_search("(A -> (B -> C)) -> ((A -> B) -> (A -> C))", 1000)
# countermodel_search("((not A) -> (not B)) -> (B -> A)", 1000)

#--------------------------------------------------------------------
# Axioms for graph-reachability and forward propagation
#--------------------------------------------------------------------

# # Modal Laws for 'know'
# countermodel_search("know A", 1000, premises=["A"]) # Nec (Operator from Set->Set)
# countermodel_search("(know (A and B)) <-> (know A and know B)", 1000) # K (Monotonic)
# countermodel_search("(know A) -> A", 1000) # T (Inclusive)
# countermodel_search("(know A) -> (know know A)", 1000) # 4 (Idempotent)
# countermodel_search("(know ((know (A -> (know A))) -> A)) -> A", 1000) # Grz (Acyclic)

# # Modal Laws for 'know↓'
# countermodel_search("know↓ A", 1000, premises=["A"]) # Nec (Operator from Set->Set)
# countermodel_search("(know↓ (A and B)) <-> (know↓ A and know↓ B)", 1000) # K (Monotonic)
# countermodel_search("A -> (know (<know↓> A))", 1000) # (Back)
# countermodel_search("A -> (know↓ (<know> A))", 1000) # (Forth)

# # Modal Laws for 'typ'
# countermodel_search("typ A", 1000, premises=["A"]) # Nec (Operator from Set->Set)
# countermodel_search("(typ A) -> A", 1000) # T (Inclusive)
# countermodel_search("(typ A) -> (typ typ A)", 1000) # 4 (Idempotent)

# countermodel_search("(typ A) -> (know A)", 1000, max_elements=5)

# # Minimal Cause / Skeleton
# countermodel_search("(<know↓> B) -> ((typ A) <-> (typ ((<know↓> B) -> (typ A))))", 1000)

# # Cumulative (KLM Conditional Property)
# countermodel_search("(((typ A) -> B) and (B -> A)) -> ((typ A) <-> (typ B))", 1000)

# TODO next:
# - draw graphs for subset size 1
# - get different colors for different subset choices -- think about color choice!
# - draw contour to be a little closer to the actual bounded nodes
# - implement neighborhood semantics
# - implement translation back and forth

#--------------------------------------------------------------------
# Check that these axioms are preserved when we convert from
# a Neural Model to a Neighborhood Model.
#--------------------------------------------------------------------



#--------------------------------------------------------------------
# Reduction Axioms for Unstable Hebbian Learning
#--------------------------------------------------------------------

# # Reduction axioms for P+
# # Propositions
# countermodel_search("(A :: B) <-> B", 100)
# # Negation
# countermodel_search("(A :: (not (B))) <-> (not (A+ (B)))", 100)
# countermodel_search("(A :: (not (typ B))) <-> (¬ (A+ (T B)))", 100)
# # Conjunction
# countermodel_search("(A+ (B ∧ C)) ↔ ((A+ B) ∧ (A+ C))", 100)
# countermodel_search("(A+ ((T B) ∧ (T C))) ↔ ((A+ (T B)) ∧ (A+ (T C)))", 100)
# # Nested Box
# countermodel_search("((T A)+ B) ↔ (A+ B)", 100)
# countermodel_search("((T A)+ (T B)) ↔ (A+ (T B))", 100)

# # No Surprises
# countermodel_search("(A+ (T B)) → (T (A+ B))", 100)
# countermodel_search("(A+ (T(T B))) → (T (A+ (T B)))", 100)

# # Typicality Preservation
# countermodel_search("((T (A+ B)) ∧ (T A)) → (A+ (T B))", 100)
# countermodel_search("((T (A+ (T B))) ∧ (T A)) → (A+ (T(T B)))", 100)

# countermodel_search("(typ penguin) -> flies", 1000, premises=["penguin -> bird", "(typ bird) -> flies"])


# #---------------------------------------------------------------------------------------------------------
# # Net construction for poster
# import os
# os.environ['TF_CPP_MIN_LOG_LEVEL'] = '3'

# import networkx as nx
# import matplotlib.pyplot as plt

# from alamode.FeedforwardNet import FeedforwardNet
# from alamode.InterpretedNet import InterpretedNet
# from alamode.activation_functions import binary_step

# from alamode.PrefModel import PrefModel
# from alamode.model_building import *

# nodes = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h']
# graph = nx.DiGraph()

# graph.add_weighted_edges_from(
#     [('a', 'e', -9.0), 
#      ('a', 'f', -2.0), 
#      ('a', 'g', -2.0), 
#      ('a', 'h', 0.0), 
#      ('b', 'e', 1.0), 
#      ('b', 'f', 0.0), 
#      ('b', 'g', 9.0), 
#      ('b', 'h', 3.0), 
#      ('c', 'e', 0.0), 
#      ('c', 'f', 8.0), 
#      ('c', 'g', -9.0), 
#      ('c', 'h', 0.0), 
#      ('d', 'e', -8.0), 
#      ('d', 'f', -3.0), 
#      ('d', 'g', 2.0), 
#      ('d', 'h', 6.0),
#      ('e', 'h', 0.0), 
#      ('f', 'h', 0.0), 
#      ('g', 'h', 0.0)]) 
# rate = 1.0
# prop_map = {
#     'bird': {'b', 'e'}, 
#     'flies': {'g', 'e'},
#     'penguin': {'b', 'c', 'a', 'f', 'e'}, 
# }

# net = FeedforwardNet(nodes, graph, binary_step, rate)
# net_model = InterpretedNet(net, prop_map)
# pref_model = PrefModel_from_InterpretedNet(net_model)

# print(net_model)
# print(pref_model)

# print("NET MODEL")
# print("penguin -> bird : ", net_model.is_model("penguin -> bird"))
# print("bird => flies : ", net_model.is_model("(typ bird) -> flies"))
# print("penguin => flies : ", net_model.is_model("(typ penguin) -> flies"))

# print("\n\nPREF MODEL")
# print("penguin -> bird : ", pref_model.is_model("penguin -> bird"))
# print("bird => flies : ", pref_model.is_model("(typ bird) -> flies"))
# print("penguin => flies : ", pref_model.is_model("(typ penguin) -> flies"))

# print(pref_model.f['a'])
# print(pref_model.f['b'])
# print(pref_model.g['a'])
# print(pref_model.g['b'])

# net_model.draw(show_labels=True)
# plt.show()