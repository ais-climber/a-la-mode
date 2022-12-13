------------------------------------------------------------------------
-- Nets.BinaryFeedforward
-- 
-- A binary, feed-forward neural network (BFNN)
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --rewriting #-}

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Float using (Float)
open import Data.Vec using (Vec)

open import Data.Fin using (Fin)
open import Data.Graph.Acyclic using (Graph)

open import Functions-Base using (indegree)
open import Functions-Properties using (Zero-at-Zero; Nondecreasing)

------------------------------------------------------------------------
-- Definition of a BFNN
-- A BFNN consists of:
--   graph - a (float)-weighted, directed acyclic graph 
--           with ℕ node labels
--   activation - the activation function for each node
--   output - the output function for each node
record BFNN {n : ℕ} : Set where
    field 
        graph : Graph ℕ Float n

        activation : {i : ℕ}
            → Fin n → Vec Float i → Vec Float i → Float
        
        output : {i : ℕ}
            → Fin n → Float → Bool

        -- Properties of a BFNN
        -- Note that the graph is binary and acyclic by construction. 
        zero-at-zero : ∀ (node : Fin n)
            → let i = indegree node graph
              in  Zero-at-Zero {n} {graph} {node} activation (output {i})
            
        nondecreasing : ∀ (node : Fin n)
            → let i = indegree node graph
              in  Nondecreasing {n} {graph} {node} activation (output {i})


-- -- Function to make a BFNN from an ordinary neural network
-- -- TODO: From, e.g., Pytorch.
-- make-net : {!   !} → BFNN
-- make-net pytorchModel = record { 
--     graph = {!   !} ; 
--     activation = {!   !} ; 
--     output = {!   !} ; 
--     zeroAtZero = {!   !} ; 
--     monotIncreasing = {!   !}}