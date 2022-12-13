------------------------------------------------------------------------
-- Example
-- 
-- An example of how to use the library to make a neural
-- network and verify facts about it.
------------------------------------------------------------------------
{-# OPTIONS --rewriting #-}

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Float using (Float)
open import Data.Vec using (Vec)
open import Data.List using (List; []; _∷_)

open import Data.Fin using (Fin; #_)
open import Data.Graph.Acyclic using (Graph; context; _&_; ∅)

open import Data.Product using (_,_)

open import Functions-Base
open import Functions-Properties

open import Nets-BinaryFeedforward using (BFNN)

n : ℕ
n = 3

exampleGraph : Graph ℕ Float n
exampleGraph = 
    context 2 ((1.0 , # 0) ∷ []) & 
    context 1 (( -1.0 , # 0 ) ∷ []) & 
    context 0 [] &
    ∅

exampleBFNN : BFNN
exampleBFNN = record {
    graph = exampleGraph ; 
    activation = make-activation weighted-sum ; 
    output = make-output binary-step ; 
    zero-at-zero = step-is-zero-at-zero ; 
    nondecreasing = step-is-nondecreasing }
