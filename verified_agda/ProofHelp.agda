------------------------------------------------------------------------
-- ProofHelp
-- 
-- Functions to help make doing proofs in Agda easier.
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --rewriting #-}

-- TODO: Clean up imports and make sure everything type-checks!

-- Equational proofs
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- Establishing rewrite rules
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Unit using (tt)

-- Existentials and negations in proofs
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)

-- numbers, strings, lists, vectors, decidability
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
-- open import Agda.Builtin.Float
open import Data.Float using (Float; _+_; _*_; _≡ᵇ_; _<ᵇ_; _≤ᵇ_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Bool using (Bool; true; false; if_then_else_; T; _∧_)
open import Data.List using (List; _∷_; [])
open import Data.Vec using (Vec; []; _∷_; foldl)

postulate
    *zero : ∀ {x : Float} → 0.0 * x ≡ 0.0
    zero+zero : 0.0 + 0.0 ≡ 0.0
    
≤ᵇ<ᵇtrans : ∀ (x y z : Float) → 
    T (x <ᵇ y) → T (y ≤ᵇ z) → T (x <ᵇ z)
≤ᵇ<ᵇtrans x y z x<y y≤z = {!   !}

xy≤ᵇxz : ∀ {x y z : Float} →
    T (y ≤ᵇ z) → T (0.0 ≤ᵇ x) → T (x * y ≤ᵇ x * z)
xy≤ᵇxz {x} {y} {z} = {!   !}

≤ᵇsum : ∀ {w x y z : Float} →
    T (w ≤ᵇ x) → T (y ≤ᵇ z) → T (w + y ≤ᵇ x + z)
≤ᵇsum = {!   !}

-- plfa natural deduction proof rules
-- Credit: Phil Wadler
-- →-elim from plfa
→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M

-- ¬-elim from plfa
¬-elim : ∀ {A : Set}
  → A
  → ¬ A
    ---
  → ⊥
¬-elim x ¬x = ¬x x

-- contraposition from plfa
contraposition₁ : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition₁ f ¬y x = ¬y (f x)

-- contraposition₂ : ∀ {A B : Set}
--   → ((¬ B) → (¬ A))
--     -----------
--   → (A → B)
-- contraposition₂ ¬A→¬B B = {!   !}


-- Proof by cases, or case-⊎ in plfa.
proof-by-cases : ∀ {A B C : Set}
  → A ⊎ B
  → (A → C)
  → (B → C)
    -----------
  → C
proof-by-cases (inj₁ x) f g = f x
proof-by-cases (inj₂ y) f g = g y

-- Universal elimination
∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M

-- Existential elimination
∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y


-- -- ¬ ∀ ¬ conversion
-- ¬∀¬≡∃ : ∀ {A : Set} {B : A → Set}
--   → ¬ (∀ x → ¬ B x) → (∃[ x ] B x)
-- ¬∀¬≡∃ = {!   !}

-- -- ∃ ¬ conversion
-- ∃¬≡¬∀ : ∀ {A : Set} {B : A → Set}
--   → (∃[ x ] (¬ B x)) → ¬ (∀ x → B x)
-- ∃¬≡¬∀ = {!   !}

-- -- Negation of an existential
-- ¬∃∃ : ∀ {A B : Set} {B : A → B → Set}
--   → (∀ x → ∀ y → ¬ B x y) → (¬ (∃[ x ] ∃[ y ] B x y))
-- ¬∃∃ = {!   !}

-- -- Negation of a universal
-- ¬∀∀ : ∀ {A B : Set} {B : A → B → Set}
--   → ∃[ x ] ∃[ y ] (¬ B x y) → ¬ (∀ x → ∀ y → B x y)
-- ¬∀∀ = {!   !}

-- demorgan : ∀ {A B : Set}
--   → ¬ (¬ A × ¬ B)
--     -----------------
--   → (A ⊎ B)
-- demorgan = {!   !}

-- Double negation
-- double-negation : ∀ {A : Set}
--   → ¬ ¬ A
--   → A
-- double-negation {A} = 
--   {!   !} --λ ¬¬A → ⊥-elim (¬-elim ¬¬A λ A → ¬-elim {!   !} {!   !})

-- (Classical) excluded middle for boolean types.
-- Not provable, so we have to postulate it.
postulate
  bool-excluded-middle : ∀ (A : Bool) →
    (true ≡ A) ⊎ (false ≡ A)


-- Helper function for decidables:
-- If A is inhabited,
-- then ⌊ yes A ⌋ must be true
-- (and we can convert this to an equational proof)
-- dec-eqn : ∀ {A : Set}
--   → A
--   → true ≡ ⌊ yes A ⌋
-- dec-eqn A = 
--   begin
--     true ≡⟨ {!   !} ⟩ 
--     ⌊ yes A ⌋
--   ∎

-- true≡false : true ≡ ⌊ yes false ⌋
-- true≡false = dec-eqn false

-- <→<? : ∀ {a b} →
--   Data.Bool.T (a Data.Float.<ᵇ b) → true ≡ ⌊ a Data.Float.<? b ⌋
-- <→<? = {!   !}

-- <?→< : ∀ {a b} →
--   true ≡ ⌊ a Data.Float.<? b ⌋ → a Data.Float.< b
-- <?→< = {!   !}

-- true ≡ ⌊ proj₂ M Data.Float.<? vsm.dot-prod ⟦ w ⟧ⱽ ⟦ x ⟧ⱽ ⌋

-------------------------
-- Isomorphisms
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

-------------------------
-- Min and max
-- min-running : List Float → Float → Float
-- min-running [] curr = curr
-- min-running (x ∷ xs) curr = 
--   if ⌊ x Data.Float.<? curr ⌋
--   then min-running xs x
--   else min-running xs curr

-- max-running : List Float → Float → Float
-- max-running [] curr = curr
-- max-running (x ∷ xs) curr = 
--   if ⌊ curr Data.Float.<? x ⌋
--   then max-running xs x
--   else max-running xs curr

-- min : List Float → Float
-- min lst = min-running lst 1000000.0

-- max : List Float → Float
-- max lst = max-running lst -1000000.0

-- ∃! (there exists a unique)
--infix 4 ∃![_]_
--∃![_]_ : Set
--∃![ x ] A = ∃[ x ] A × 
--infix 4 ∃!_
--∃!_ : Set → Set
--∃! A = ∃[ x ] (A × (∀ y → ))

-- My own personal 'iff' operator
-- Author: Caleb Kisby
-- Based on the agda2 equational begin_≡⟨_⟩_..._∎ pattern
-- infix 1 _iff⟨_⟩_

-- An 'iff' operator, for convenience.
infix 4 _iff_

_iff_ : Set → Set → Set
A iff B = (A → B) × (B → A)

{-
T
      ((x * y ≤ᵇ x * z) Data.Bool.∧
       (zipWith _*_ xs ys ≤ⱽ zipWith _*_ xs zs))
-}
×-to-∧ : ∀ {b1 b2 : Bool} →
    T b1 × T b2 → T (b1 ∧ b2)
×-to-∧ {false} {b2} = proj₁
×-to-∧ {true} {b2} = proj₂

∧-to-× : ∀ {b1 b2 : Bool} →
    T (b1 ∧ b2) → T b1 × T b2
∧-to-× {false} {b2} = λ ()
∧-to-× {true} {b2} = ⟨_,_⟩ tt

{-
begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin x≡y  =  x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y  =  x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z  =  trans x≡y y≡z

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎  =  refl
-}