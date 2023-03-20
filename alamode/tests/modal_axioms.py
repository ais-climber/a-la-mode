# We check axioms for K, T, and P+ to see if
# we can find any countermodels via a random search.
# 
# We should hope that no countermodels are found
# (since otherwise there is an error in our proofs!)

from alamode.countermodel_search import countermodel_search

#--------------------------------------------------------------------
# Axioms for propositional logic
#--------------------------------------------------------------------

countermodel_search("A -> A", 1000)
countermodel_search("A -> (B -> A)", 1000)
countermodel_search("(A -> (B -> C)) -> ((A -> B) -> (A -> C))", 1000)
countermodel_search("((not A) -> (not B)) -> (B -> A)", 1000)

#--------------------------------------------------------------------
# Axioms for graph-reachability and forward propagation
#--------------------------------------------------------------------

# Modal Laws for 'know'
countermodel_search("know A", 1000, premises=["A"]) # Nec (Operator from Set->Set)
countermodel_search("(know (A and B)) <-> (know A and know B)", 1000) # K (Monotonic)
countermodel_search("(know A) -> A", 1000) # T (Inclusive)
countermodel_search("(know A) -> (know know A)", 1000) # 4 (Idempotent)
countermodel_search("(know ((know (A -> (know A))) -> A)) -> A", 1000) # Grz (Acyclic)

# Modal Laws for 'know↓'
countermodel_search("know↓ A", 1000, premises=["A"]) # Nec (Operator from Set->Set)
countermodel_search("(know↓ (A and B)) <-> (know↓ A and know↓ B)", 1000) # K (Monotonic)
countermodel_search("A -> (know (<know↓> A))", 1000) # (Back)
countermodel_search("A -> (know↓ (<know> A))", 1000) # (Forth)

# Modal Laws for 'typ'
countermodel_search("typ A", 1000, premises=["A"]) # Nec (Operator from Set->Set)
countermodel_search("(typ A) -> A", 1000) # T (Inclusive)
countermodel_search("(typ A) -> (typ typ A)", 1000) # 4 (Idempotent)

countermodel_search("(typ A) -> (know A)", 1000, max_elements=5)

# Minimal Cause / Skeleton
countermodel_search("(<know↓> B) -> ((typ A) <-> (typ ((<know↓> B) -> (typ A))))", 1000)

# Cumulative (KLM Conditional Property)
countermodel_search("(((typ A) -> B) and (B -> A)) -> ((typ A) <-> (typ B))", 1000)

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
