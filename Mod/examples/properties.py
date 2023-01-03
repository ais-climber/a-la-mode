# We check axioms for K, T, and P+ to see if
# we can find any countermodels via a random search.
# 
# We should hope that no countermodels are found
# (since otherwise there is an error in our proofs!)

from Mod.countermodel_search import countermodel_search

# S4 Modal Laws for K
countermodel_search("(K(A ∧ B)) ↔ (K A ∧ K B)", 100) # K
countermodel_search("(K A) → A", 100) # T
countermodel_search("(K A) → (K K A)", 100) # 4
countermodel_search("K A", 100, premises=["A"]) # Nec

# ENT4* Modal Laws for T
countermodel_search("(T A) → A", 100)
countermodel_search("(T A) → T(T A)", 100)
countermodel_search("T A", 100, premises=["A"]) # Nec

# Reduction axioms for P+
# Propositions
countermodel_search("(A+ B) ↔ B", 100)
# Negation
countermodel_search("(A+ (¬ (B))) ↔ (¬ (A+ (B)))", 100)
countermodel_search("(A+ (¬ (T B))) ↔ (¬ (A+ (T B)))", 100)
# Conjunction
countermodel_search("(A+ (B ∧ C)) ↔ ((A+ B) ∧ (A+ C))", 100)
countermodel_search("(A+ ((T B) ∧ (T C))) ↔ ((A+ (T B)) ∧ (A+ (T C)))", 100)
# Nested Box
countermodel_search("((T A)+ B) ↔ (A+ B)", 100)
countermodel_search("((T A)+ (T B)) ↔ (A+ (T B))", 100)

# No Surprises
countermodel_search("(A+ (T B)) → (T (A+ B))", 100)
countermodel_search("(A+ (T(T B))) → (T (A+ (T B)))", 100)

# Typicality Preservation
countermodel_search("((T (A+ B)) ∧ (T A)) → (A+ (T B))", 100)
countermodel_search("((T (A+ (T B))) ∧ (T A)) → (A+ (T(T B)))", 100)
