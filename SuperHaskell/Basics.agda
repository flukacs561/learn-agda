-- title: Notes to the talk 'Super Haskell'
-- date: 2025-01-02

module SuperHaskell.Basics where

open import Data.Nat
open import Data.Bool

-- Sum types
data Three : Set where
  one : Three
  two : Three
  three : Three

valueOfThree : Three
valueOfThree = one

-- This is Haskell's Either implemented in Agda
data Either (A : Set) (B : Set) : Set where
  left : A → Either A B
  right : B → Either A B

valueOfEither : {A : Set} → Either ℕ A
valueOfEither = left 10

-- Product types
record Six : Set where
  constructor myconst
  field
    oneOf3 : Three
    oneOf2 : Bool

valueOfSix : Six
valueOfSix = myconst three false

-- This is Haskell's `Pair` type
record Pair (A : Set) (B : Set) : Set where
  constructor pair
  field
    proj₁ : A
    proj₂ : B

valueOfPair : Pair ℕ Bool
valueOfPair = pair 10 false

-- Pattern Matching
addThreeToNat : ℕ → Three → ℕ
addThreeToNat n one = n + 1 
addThreeToNat n two = n + 2
addThreeToNat n three = n + 3

-- Syntactic considerations
add_to_butOnlyIf_and_otherwisePickOne : ℕ → ℕ → Bool → Bool → ℕ
add n to m butOnlyIf cond1 and cond2 otherwisePickOne = let
  cond1-and-cond2 = cond1 ∧ cond2
  in if cond1-and-cond2
    then n + m
    else chosen cond1 cond2
   where chosen : Bool → Bool → ℕ
         chosen c1 c2 with c1 ∨ c2
         ... | true = n
         ... | false = m

fifteen : ℕ
fifteen = add 10 to 5 butOnlyIf true and (5 <ᵇ 10) otherwisePickOne
