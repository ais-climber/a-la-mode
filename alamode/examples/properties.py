# We check axioms for K, T, and P+ to see if
# we can find any countermodels via a random search.
# 
# We should hope that no countermodels are found
# (since otherwise there is an error in our proofs!)

from alamode.countermodel_search import countermodel_search

#--------------------------------------------------------------------
# Axioms for graph-reachability and forward propagation
#--------------------------------------------------------------------

# # Modal Laws for 'know'
# countermodel_search("know A", 1000, premises=["A"]) # Nec
# countermodel_search("(know (A and B)) <-> (know A and know B)", 1000) # K
# countermodel_search("(know A) -> A", 1000) # T
# countermodel_search("(know A) -> (know know A)", 1000) # 4

# # Modal Laws for 'know↓'
# countermodel_search("know↓ A", 1000, premises=["A"]) # Nec
# countermodel_search("(know↓ (A and B)) <-> (know↓ A and know↓ B)", 1000) # K
# countermodel_search("A -> (know (<know↓> A))", 1000) # Forward
# countermodel_search("A -> (know↓ (<know> A))", 1000) # Back

# # Modal Laws for 'typ'
# countermodel_search("typ A", 1000, premises=["A"]) # Nec
# countermodel_search("(typ A) -> A", 1000) # T
# countermodel_search("(typ A) -> (typ typ A)", 1000) # 4

#--------------------------------------------------------------------
# Random things I'd like to check
#--------------------------------------------------------------------

# STATUS:   Countermodel found!
countermodel_search("((not (know B)) -> (typ A)) -> ((typ (A and B)) <-> (typ A))", 20, max_elements=2)

# STATUS:   No countermodel found. (Searched 1000 randomly-generated models.)
countermodel_search("((not (know B)) -> (typ A)) -> ((typ (A and B)) -> (typ A))", 1000)

# STATUS:   No counterexample found. (Searched 1000 randomly-generated models.)
countermodel_search("((typ A) -> B) <-> ((typ (A or (know↓ B))) -> B)", 1000)


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
