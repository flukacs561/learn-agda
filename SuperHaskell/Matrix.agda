module SuperHaskell.Matrix where

open import Data.Bool
open import Data.Nat as Nat hiding (_+_ ; _*_ ; zero ; _≤ᵇ_)
open import Data.Float as Float hiding (_+_ ; _*_ ; _≤ᵇ_) renaming (Float to ℝ)
open import Data.Bool hiding (_≤_ ; _<_)
open import SuperHaskell.Basics hiding (one)
open import SuperHaskell.PropositionsAsTypes
open import Function

record Num (C : Set) : Set where
  field
    _+_ : C → C → C
    _*_ : C → C → C

    one : C
    zero : C

    _≤ᵇ_ : C → C → Bool

  infixl 19 _≤ᵇ_
  infixl 20 _+_
  infixl 21 _*_

open Num {{...}}

numℕ : Num ℕ
Num._+_ numℕ = Nat._+_
Num._*_ numℕ = Nat._*_
Num.zero numℕ = 0
Num.one numℕ = 1
Num._≤ᵇ_ numℕ = Nat._≤ᵇ_

numℝ : Num ℝ
Num._+_ numℝ = Float._+_
Num._*_ numℝ = Float._*_
Num.zero numℝ = 0.0
Num.one numℝ = 1.0
Num._≤ᵇ_ numℝ = Float._≤ᵇ_

instance
  numℝInstance : Num ℝ
  numℝInstance = numℝ

instance
  numℕInstance : Num ℕ
  numℕInstance = numℕ

record Matrix (A : Set) (rows cols : ℕ) : Set where
  constructor 𝕄
  field
    values : Vec (Vec A cols) rows

open Matrix

_+ᴹ_ : ∀ {A r c} {{numA : Num A}} → Matrix A r c → Matrix A r c → Matrix A r c
_+ᴹ_ (𝕄 m₁) (𝕄 m₂) = 𝕄 (zipWith (zipWith _+_) m₁ m₂)

infixl 29 _+ᴹ_

_*ᴹ_ : ∀ {A r c p} {{numA : Num A}} → Matrix A r c → Matrix A c p → Matrix A r p
_*ᴹ_ (𝕄 m₁) (𝕄 m₂) = 𝕄 (map (λ row → map (λ col → sum (zipWith _*_ row col)) (transpose m₂)) m₁)
  where
    sum : ∀ {A n} {{numA : Num A}} → Vec A n → A
    sum [] = zero
    sum (x :: xs) = x + sum xs

infixl 30 _*ᴹ_

vecToColMatrix : ∀ {A n} → Vec A n → Matrix A n 1
vecToColMatrix v = 𝕄 (map (λ a → [ a ]) v)

vecToRowMatrix : ∀ {A n} → Vec A n → Matrix A 1 n
vecToRowMatrix v = 𝕄 [ v ]

_ᵀ : ∀ {A r c} → Matrix A r c → Matrix A c r
(𝕄 m) ᵀ = 𝕄 (transpose m)

infixl 45 _ᵀ
