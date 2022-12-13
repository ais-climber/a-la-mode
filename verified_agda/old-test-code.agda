open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
open import Data.Fin
open import Data.String
open import Data.Float
-- TODO remove List in favor of Vec
open import Data.List
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Vec
open import Data.Bool renaming (not to bool-not)
open import Data.Fin.Subset renaming (_∈_ to memberOf)

-- Reasoning about equality
open import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

-- Reasoning about propositions
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contraposition)

-- Reasoning about quantifiers
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

-- Reasoning about graphs
open import Level using (_⊔_)
open import Data.Graph.Acyclic

private
  variable
    Node : Set

{-╔═════════════════════════════════════════════╗
  ║  ║
  ╚═════════════════════════════════════════════╝-}

{-╔═════════════════════════════════════════════╗
  ║ Helper Functions                            ║
  ╚═════════════════════════════════════════════╝-}
-- TODO: Move to a seperate library

-- Function to give the predecessors of node 'tgt'
-- in a convenient unpacked list.
-- predList : (graph : Graph ℕ Float graphSize) (tgt : Fin graphSize) 
--     → List (Fin graphSize)
--     -- List (Fin′ tgt)
-- predList graph tgt = {!   !}
    -- proj₁ (Data.List.unzip (preds graph tgt))

-- Function to give a list of n 0's/falses
listOfZeros : (n : ℕ) → Vec Bool n
listOfZeros zero = []
listOfZeros (suc m) = false ∷ listOfZeros m

-- Function to convert Bools to Floats
fromBool : Bool → Float
fromBool true = 1.0
fromBool false = 0.0

-- Function to convert Floats back to Bools
-- ANY NON-BOOL VALUES GET CONVERTED TO 'false'
toBool : Float → Bool
toBool = λ (float : Float) → 
    if float ≡ᵇ 1.0 then 
        true 
    else 
        false

-- Function to convert Vecs of Bools to Vecs of Floats
fromVecBool : {n : ℕ} → Vec Bool n → Vec Float n
fromVecBool [] = []
fromVecBool (x ∷ xs) = fromBool x ∷ fromVecBool xs

-- fromVecBool [] = []
-- fromVecBool (x ∷ xs) = fromBool x ∷ fromVecBool xs

weightedSum : ∀ {n : ℕ} → Vec Float n → Vec Float n → Float
weightedSum v1 v2 = 
    Data.Vec.foldr _ Data.Float._+_ 0.0 
        (Data.Vec.zipWith Data.Float._*_ v1 v2)

-- Pointwise less than for Vectors of Floats.
infix 4 _<ⱽ_
_<ⱽ_ : ∀ {n : ℕ} → Vec Float n → Vec Float n → Set
_<ⱽ_ {zero} [] [] = Data.Unit.⊤
_<ⱽ_ {suc n} (x1 ∷ v1) (x2 ∷ v2) = 
    T (x1 Data.Float.<ᵇ x2) × (v1 <ⱽ v2)

-- Try to find these in the standard library!
postulate
   threeChoices : ∀ (a b : Float) → T (a <ᵇ b) ⊎ T (b <ᵇ a) ⊎ (a ≡ b)
   
-- Our actual goal:
-- T
    --   ((if threshold <ᵇ weightedSum (fromVecBool x) w1 then 1 else 0)
    --    <ᵇ
    --    (if threshold <ᵇ weightedSum (fromVecBool x) w2 then 1 else 0))
-- We should do a proof by cases!

-- ifEquality : ∀ x {y z} 
--     → ¬ T x 
--     → (if x then y else z) ≡ z
-- ifEquality false = λ ¬⊥ → refl
-- ifEquality true = λ ¬⊤ → {!   !} -- use prinicple of explosion, obviously

{-╔═════════════════════════════════════════════╗
  ║ BFNN                                        ║
  ╚═════════════════════════════════════════════╝-}
{------------------------------------------------
 -- BFNN
 -- A BFNN is a binary, feed-forward neural network.
 -- It consists of:
 --   graph - a (float)-weighted, directed acyclic graph 
 --           with ℕ node labels
 --   activation - the activation function for each node
 --   output - the output function for each node
 -- 
 -- TODO:
 --   At the moment, we just trust the user to
 --   give 'activation' a List of same length as
 --   the arity of node 'n'.  We should instead
 --   constrain the List to have this length.
 ------------------------------------------------}
record BFNN {graphSize : ℕ} : Set where
    field 
        graph : Graph ℕ Float graphSize

        activation : (n : Fin graphSize) → 
            let indegree = Data.List.length (preds graph n) 
            in  (Vec Bool indegree → Vec Float indegree → Float)
        
        output : (n : Fin graphSize) → Float → Bool

        -- Properties of a BFNN
        -- Note that the graph is binary and acyclic by construction.

        -- TODO:
        -- We use length of weights, implicitly relying on the
        -- fact that the weights are the same length as the predecessors
        -- of n.  This should be made explicit.
        zeroAtZero : ∀ (n : Fin graphSize) →
            let indegree = Data.List.length (preds graph n)
                zeros = listOfZeros indegree
            in  
                -- "The output of the activation at [0...0] is 0."
                (weights : Vec Float indegree)
                -----------------------------------------
              → output n (activation n zeros weights) ≡ false
            
        monotIncreasing : ∀ (n : Fin graphSize) → 
            let indegree = Data.List.length (preds graph n)
            in
                -- "If w1 < w2, then the output(activ(w1)) < output(activ(w2))."
                (x : Vec Bool indegree) (w1 w2 : Vec Float indegree) 
              → w1 <ⱽ w2 
                -----------------------------------------
              → output n (activation n x w1) Data.Bool.< 
                    output n (activation n x w2)

-- -- Function to make a BFNN from an ordinary neural network
-- -- TODO: From, e.g., Pytorch.
-- make-net : {!   !} → BFNN
-- make-net pytorchModel = record { 
--     graph = {!   !} ; 
--     activation = {!   !} ; 
--     output = {!   !} ; 
--     zeroAtZero = {!   !} ; 
--     monotIncreasing = {!   !}}

{-╔═════════════════════════════════════════════╗
  ║ An example neural network                   ║
  ╚═════════════════════════════════════════════╝-}
{------------------------------------------------
 - Note about graph representation:
 - 'Graph ℕ Float 3'
 -    means graph has nodes in ℕ, edges in Float,
 -    and has 3 total nodes.
 - 
 - We use the Edge label to denote the weight of
 - the edge (convenient!)
 - 
 - Graphs are entered in 'reverse', i.e. node
 - n can only point to nodes smaller than it.
 - 
 ------------------------------------------------}

exampleGraph : Graph ℕ Float 3
exampleGraph = 
    context 0 [] & 
    context 1 (( 1.0 , # 0 ) ∷ []) & 
    context 2 (( -1.0 , # 0 ) ∷ []) &
    ∅

threshold : Float
threshold = 0.0

exampleBFNN : BFNN
exampleBFNN = record {
    -- First, we provide the graph, activation, and output 
    graph = exampleGraph ;

    -- Activation value is just a weighted sum.
    activation = λ n prevOutputs weights →
        weightedSum (fromVecBool prevOutputs) weights ;
            
    -- Output is just a threshold function.
    output = λ n activation → 
        threshold <ᵇ activation ;
        
    -- Then we check that this is actually a BFNN.
    -- 
    -- TODO: I should make a library with all the standard
    --       functions used in machine learning (e.g. weighted
    --       sum, RELU, etc. in both binary and fuzzy forms,
    --       and have all the relevant checks along with them.
    --       Otherwise, I'm unfairly expecting the user to
    --       figure it out on their own.)
    zeroAtZero = 
        λ n weights → 
        -- We want to show that threshold ≮ weightedSum(0...0),
        -- and therefore the net outputs 0.0
        -- NOTE: Cleaner if we reduce the if-statement on the left-hand
        --       side using 'cong' or 'subst'
            -- ifEquality (threshold <ᵇ weightedSum (fromVecBool (listOfZeros 
            --         (Data.List.length (preds exampleGraph n)))) weights) 
            --         λ contradHypothesis → 
            --             {!   !} ;
            {!   !} ;

    monotIncreasing = 
        λ n x w1 w2 w1<ⱽw2 →
            -- If threshold <ᵇ weightedSum for w1,
            --    then obviously this holds for w2 as well,
            -- otherwise if the output for w1 is 0.0,
            --    the output for w2 can only be bigger (either 0.0 or 1.0)
            {!   !} }
            {-
            case-⊎ 
            
                -- Case 1: threshold < weighted sum for w1
                (λ thres<ᵇw1Sum → 
                    {!   !}) 
                
                (λ twoChoices → 
                case-⊎ 

                    -- Case 2: weighted sum for w1 < threshold
                    (λ w1Sum<ᵇthres → 
                        {!   !}) 

                    -- Case 3: weighted sum for w1 ≡ threshold
                    (λ thres≡w1Sum → 
                        {!   !}) 
                        
                    twoChoices) 
                (threeChoices threshold (weightedSum (fromVecBool x) w1)) }
            -}
            
{-╔═════════════════════════════════════════════╗
  ║ Reach and Prop                              ║
  ╚═════════════════════════════════════════════╝-}
{------------------------------------------------
 - These functions are the heart of the program.
 - TODO: Unhelpful, say more
 ------------------------------------------------}



-- Attempt to define Reach
-- recursively on the structure of the *graph*

{-
data Reach {size} {Net : BFNN {size}} (signal : Subset size) (node : Fin size) : Set where
    inSignal : memberOf node signal
        → Reach signal node

    reachedBy : ∀ (m : Fin {!   !})
        → {!   !}
        -- TRICK: Perform some operation on 'signal' that reduces
        -- it to be the right size.
        -- Somehow do induction on a topological sort of the graph,
        -- up to (but not including) 'node'.
        → Reach {{!   !}} {{!   !}} {!   !} m
        ---------------------
        → Reach {size} {Net} signal node
-}

-- data Reach {size} {Net : BFNN {size}} (signal : (Fin size) → Set) (node : Fin size) : Set where
--     inSignal : signal node 
--         → Reach {size} {Net} signal node

--     reachedBy : {!   !} 
--         → Reach {{!   !}} {{!   !}} signal node

-- data Reach {size} {Net : BFNN {size}} (signal : List (Fin {!   !})) (node : Fin {!   !}) : Set where
--     inSignal : node ∈ signal
--         → Reach signal node

        -- for Subsets:
        -- -- memberOf node signal

    -- reachedBy : ∃[ x ] (Reach signal node)
    --     → node ∈ proj₂ (Data.List.unzip (sucs (BFNN.graph Net) m))
    --     -- proj₁ (Data.List.unzip (preds {!  !} {! m  !}))
    --     -- proj₂ (Data.List.unzip (sucs {!   !} m))
    --     → Reach signal m
    --     -----------------------
    --     → Reach signal node


-- Reach : {Net : BFNN} (signal : Subset graphSize) → Subset graphSize
-- Reach signal = {!   !}

{-╔═════════════════════════════════════════════╗
  ║ Properties of Reach and Prop                ║
  ╚═════════════════════════════════════════════╝-}
-- propInclusion : ∀ S → S ⊆ Reach S
-- propInclusion S x∈S = {!   !}

-- TODO:
--   Figure out how to recursively define Reaches
--   so that Agda knows it terminates.
--   (we're doing recursion on the index of the node we
--    are considering!!!)

-- TODO:
-- Define logical language and propositional
-- mappings

-- record Model : Set where
--     field
--         net : BFNN
--         proposition_map : {!   !} → {!   !}

-- -- Function to build a BFNN from a neural network
-- -- and an interpretation
-- make-model : {!   !} → {!   !} → Model
-- make-model = {!   !} 

{-╔═════════════════════════════════════════════╗
  ║ Interface Syntax                            ║
  ╚═════════════════════════════════════════════╝-}

Id : Set
Id = String

infix 10 `_
infix 9 knows_ typ_ [_]_ [_]∗_
infix 7 _and_ _or_
infix 6 _⇒_ -- Be careful!  This looks a lot like '→' !!!

data Term : Set where
    -- Base propositions
    `_       : Id → Term

    -- Connectives
    top      : Term
    bot      : Term
    not      : Term → Term
    _and_    : Term → Term → Term
    _or_     : Term → Term → Term
    _⇒_      : Term → Term → Term

    -- Modal update operators
    knows_  : Term → Term
    typ_    : Term → Term
    [_]_    : Term → Term → Term
    [_]∗_   : Term → Term → Term

Environment : Set
Environment = List Term

-- 
infix 6 ⟦_⟧
infix 5 _,_⊨_
infix 5 ⊨_

-- A Model is just a BFNN paired with an interpretation of
-- propositions.
Model : {n : ℕ} → Set
Model {n} = BFNN {n} × (Id → Subset n)

-- ~~~The Interpretation~~~
-- The real engine of the neuro-symbolic interface
⟦_⟧ : {i : ℕ} → Term → Subset i
⟦ t ⟧ = {!  !}


