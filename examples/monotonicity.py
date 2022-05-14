# Example 1 - Monotonicity Failure
from neuralsemantics.core.BFNN import *
from neuralsemantics.core.Model import *

nodes = set(["a", "b", "c", "d", "e"])
layers = [["a", "b"], ["c", "d"], ["e"]]
weights = { ("a", "c") : 2,  ("b", "c") : -2, # the '4' weights here are 2+ what I would expect... something's wrong
            ("c", "e") : 2,  ("d", "e") : -1 }
threshold = 1
rate = 1

prop_map = {
    "p" : set(["a"]),
    "q" : set(["a", "b"]),
    "r" : set(["c", "d"])
}

net = BFNN(nodes, layers, weights, threshold, rate)
model = Model(net, prop_map)

print("Counterexample to Monotonicity:")
print(model)

print("Checking properties:")
print("ND \t\t", "p+ ◻q → ◻ (p+ q) \t\t", model.is_model("(p+ (◻ q)) → (◻ (p+ q))")) # ND
print("PP \t\t", "◻ (p+ q) ∧ ◻p → p+ ◻q \t\t", model.is_model("(◻ (p+ q)) ∧ (◻p) → (p+ (◻ q))")) # PP
print("Monotonicity \t", "(q → p) → (q+ ◻r → p+ ◻r) \t", model.is_model("(q → p) → ((q+ (◻r)) → (p+ (◻r)))")) # Monotonic (should be False)
print()

print("Trace of semantics:")
print("◻p \t\t", model.interpret("◻p"))       # Expect {a, c, e}
print("◻q \t\t", model.interpret("◻q"))       # Expect {a, b}
print("◻r \t\t", model.interpret("◻r"))       # Expect {c, d}
print("p+ ◻r \t\t", model.interpret("p+ (◻r)")) # Expect {c, d, e}
print("q+ ◻r \t\t", model.interpret("q+ (◻r)")) # Expect {c, d}

# Same example, but using brand associations:
# All bajablast is mountaindew,
# but exposure to bajablast can remind us/lead us to think of taco bell
# but mountaindew in general does not remind us of taco bell.
# prop_map = {
#     "mountaindew" : set(["a"]),
#     "bajablast" : set(["a", "b"]),
#     "tacobell" : set(["c", "d"])
# }
# print(model.is_model("(bajablast → mountaindew)"))
# print(model.is_model("(mountaindew+ (◻tacobell)) → (bajablast+ (◻tacobell))"))
# print(model.is_model("(bajablast+ (◻tacobell)) → (mountaindew+ (◻tacobell))"))