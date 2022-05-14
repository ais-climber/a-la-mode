from neuralsemantics.core.model import *

nodes = set(['a', 'b', 'c', 'd'])
layers = [['a'], ['b', 'c'], ['d']]
weights = {('a', 'b'): 0.0, ('a', 'c'): 6.0, ('b', 'd'): -4.0, ('c', 'd'): 9.0}
threshold = 0.0
rate = 1.0

prop_map = {'A': {'b', 'c'}, 'B': {'d', 'c', 'a'}, 'C': {'a'}}

net = BFNN(nodes, layers, weights, threshold, rate)
model = Model(net, prop_map)

print("Counterexample to Iter Property")
print("i.e. A+ B+ C → (A ∧ A+ B)+ C")
print()
print(model)

print("Checking Iter Property:")
print("Iter w Propositions \t", "A+ B+ C → (A ∧ A+ B)+ C \t", model.is_model("(A+ (B+ C)) → ((A ∧ (A+ B))+ C)")) # (should be True)
print("Iter w Nested ◻ \t", "A+ B+ ◻C → (A ∧ A+ B)+ ◻C \t", model.is_model("(A+ (B+ (◻C))) → ((A ∧ (A+ B))+ (◻C))")) # (should be False)
print()

print("Trace of semantics:")
print("◻A \t\t", model.interpret("◻A")) # Expect {b, c, d}
print("◻B \t\t", model.interpret("◻B")) # Expect {a, c, d}
print("◻C \t\t", model.interpret("◻C")) # Expect {a, c, d}
print()
print("◻(A ∧ A+ ◻B) \t", model.interpret("◻(A ∧ (A+ (◻B)))"))
print("◻A \t\t", model.interpret("◻A"))
print("A+ ◻B \t\t", model.interpret("A+ (◻B)"))
print()
print("A+ B+ ◻C \t", model.interpret("A+ (B+ (◻C))"))
print("(A ∧ A+ B)+ ◻C \t", model.interpret("(A ∧ (A+ B))+ (◻C)"))