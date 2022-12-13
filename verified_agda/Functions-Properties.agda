------------------------------------------------------------------------
-- Functions.Properties
-- 
-- Properties of the activation, output, and other helper
-- functions.  e.g. facts such as:
--   - ReLU is monotonically increasing
--   - binary-step(zeros) = zero
--   etc.
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --rewriting #-}

open import Data.Bool using (Bool; true; false; T; _≤_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Float using (Float; _*_; _+_; _≤ᵇ_; _<ᵇ_)
open import Data.Vec using (Vec; []; _∷_; foldr; zipWith)

open import Data.Fin using (Fin)
open import Data.Graph.Acyclic using (Graph; preds)

-- Reasoning about predicates
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contraposition)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)

-- Establishing rewrite rules
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

-- Helper functions for reasoning about predicates and inequalities.
open import ProofHelp using (_iff_; proof-by-cases; bool-excluded-middle; *zero; zero+zero; ≤ᵇ<ᵇtrans; ¬-elim; ×-to-∧; ∧-to-×; xy≤ᵇxz; ≤ᵇsum)

open import Functions-Base

------------------------------------------------------------------------
-- Some small lemmas about helper functions

-- The 'zeros' vector zeros out any other vector
*zeros : ∀ (n : ℕ) → (vec : Vec Float n)
    → zipWith _*_ (zeros n) vec ≡ (zeros n)

*zeros zero [] = refl
*zeros (suc n) (v ∷ vs) = 
    let IH = *zeros n vs 
    in  trans (cong (λ expr → 0.0 * v ∷ expr) IH) 
              (cong (λ expr → expr ∷ zeros n) (*zero {v}))


-- The 'zeros' vector is an additive identity
+zeros : ∀ (n : ℕ)
    → foldr _ _+_ 0.0 (zeros n) ≡ 0.0

+zeros zero = refl
+zeros (suc n) = 
    let IH = +zeros n 
    in  trans (cong (λ expr → 0.0 + expr) IH) 
              (cong (λ expr → 0.0) zero+zero)


-- These rewrite rules allow us to automatically reduce the
-- result of the activation function.
{-# REWRITE *zeros +zeros #-}


zipWith-is-nondecreasing : ∀ (n : ℕ) (x v1 v2 : Vec Float n)
    → T (v1 ≤ⱽ v2) → T ((zipWith _*_ x v1) ≤ⱽ (zipWith _*_ x v2))

zipWith-is-nondecreasing zero [] [] [] = λ _ → tt
zipWith-is-nondecreasing (suc n) (x ∷ xs) (y ∷ ys) (z ∷ zs) hypothesis = 
    let IH = zipWith-is-nondecreasing n xs ys zs
        y≤z = proj₁ (∧-to-× hypothesis)
        ys≤zs = proj₂ (∧-to-× hypothesis)
    in  ×-to-∧ (xy≤ᵇxz {x} {y} {z} y≤z {!   !} , (IH ys≤zs))


foldr-is-nondecreasing : ∀ (n : ℕ) (v1 v2 : Vec Float n)
    → T (v1 ≤ⱽ v2) → T ((foldr _ _+_ 0.0 v1) ≤ᵇ (foldr _ _+_ 0.0 v2))

foldr-is-nondecreasing zero [] [] = λ _ → tt
foldr-is-nondecreasing (suc n) (y ∷ ys) (z ∷ zs) hypothesis = 
    let IH = foldr-is-nondecreasing n ys zs
        y≤z = proj₁ (∧-to-× hypothesis)
        ys≤zs = proj₂ (∧-to-× hypothesis)
    in  ≤ᵇsum {y} y≤z (IH ys≤zs)
    

threshold-is-nondecreasing : ∀ (x1 x2 : Float)
    → T (x1 ≤ᵇ x2) → ((0.0 <ᵇ x1) ≤ (0.0 <ᵇ x2))

threshold-is-nondecreasing x1 x2 = 
    -- Syntactic substitutions we plan on making
    let left = λ e → e ≤ (0.0 <ᵇ x2)
        right-true = λ e → true ≤ e
        right-false = λ e → false ≤ e
    in  
        -- We just consider every possible case for 0 < x1 and 0 < x2
        λ hypothesis → 
            proof-by-cases (bool-excluded-middle (0.0 <ᵇ x1)) 
                (λ 0<x1 → proof-by-cases (bool-excluded-middle (0.0 <ᵇ x2)) 
                    (λ 0<x2 → subst left 0<x1 
                        (subst right-true 0<x2 _≤_.b≤b))

                    -- This case is impossible (i.e. we show '⊥')
                    λ 0≮x2 → ⊥-elim 
                        let T0<x1 = (subst (λ e → T e) 0<x1 tt)
                            T0<x2 = (≤ᵇ<ᵇtrans 0.0 x1 x2) T0<x1 hypothesis
                            ¬T0<x2 = (subst (λ e → ¬ T e) 0≮x2 (λ x → x))
                        in ¬-elim T0<x2 ¬T0<x2)
                        
                λ 0≮x1 → proof-by-cases (bool-excluded-middle (0.0 <ᵇ x2)) 
                    (λ 0<x2 → subst left 0≮x1 
                        (subst right-false 0<x2 _≤_.f≤t))
                    λ 0≮x2 → subst left 0≮x1 
                        (subst right-false 0≮x2 _≤_.b≤b)


------------------------------------------------------------------------
-- First, we state the major properties generically, i.e.
-- for any possible combination of output and activation
-- functions 'out' and 'act'.

Zero-at-Zero : ∀ {n : ℕ} {graph : Graph ℕ Float n} {node : Fin n}
    → let i = indegree node graph
      in
      (act : Fin n → Vec Float i → Vec Float i → Float)
    → (out : Fin n → Float → Bool)
    → Set
    
Zero-at-Zero {n} {graph} {node} act out =
      let i = indegree node graph
      in
      ∀ (weights : Vec Float i) 
    → out node (act node (zeros i) weights) ≡ false


Nondecreasing : ∀ {n : ℕ} {graph : Graph ℕ Float n} {node : Fin n}
    → let i = indegree node graph
      in
      (act : Fin n → Vec Float i → Vec Float i → Float)
    → (out : Fin n → Float → Bool)
    → Set

Nondecreasing {n} {graph} {node} act out =
      let i = indegree node graph
      in 
      ∀ (x : Vec Float i)
    → ∀ (w1 w2 : Vec Float i)
    → T (w1 ≤ⱽ w2)
    → (out node (act node x w1) 
      Data.Bool.≤
      out node (act node x w2))

------------------------------------------------------------------------
-- Weighted sum with binary step output is Zero at Zero

step-is-zero-at-zero : ∀ {n : ℕ} {graph : Graph ℕ Float n} 
    → ∀ (node : Fin n)
    → Zero-at-Zero {n} {graph} {node}
        (make-activation weighted-sum)
        (make-output binary-step) 

step-is-zero-at-zero {n} {graph} node weights = refl

------------------------------------------------------------------------
-- Weighted sum with binary step output is Nondecreasing

step-is-nondecreasing : ∀ {n : ℕ} {graph : Graph ℕ Float n} 
    → ∀ (node : Fin n) 
    → Nondecreasing {n} {graph} {node}
        (make-activation weighted-sum)
        (make-output binary-step)
        
step-is-nondecreasing {n} {graph} node x w1 w2 =
    let i = indegree node graph
        zipped1 = zipWith _*_ x w1
        zipped2 = zipWith _*_ x w2
        activ1 = weighted-sum x w1
        activ2 = weighted-sum x w2
    in
        λ w1≤w2 → 
            (threshold-is-nondecreasing activ1 activ2) 
                ((foldr-is-nondecreasing i zipped1 zipped2) 
                    ((zipWith-is-nondecreasing i x w1 w2) 
                        w1≤w2))
         