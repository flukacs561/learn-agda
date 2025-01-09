module PLFA.Naturals where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl)
open Eq.≡-Reasoning using (begin_ ; step-≡-∣ ; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩
    suc ((suc zero) + (suc (suc (suc (zero)))))
  ≡⟨⟩
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩
    5
  ∎

_ : 2 + 3 ≡ 5
_ = begin 2 + 3
    ≡⟨⟩ suc (1 + 3)
    ≡⟨⟩ suc (suc (0 + 3))
    ≡⟨⟩ suc (suc 3)
    ≡⟨⟩ 5 ∎

_ : 2 + 3 ≡ 5
_ = refl

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + (m * n)

_ : 2 * 3 ≡ 6
_ = begin 2 * 3
    ≡⟨⟩ 3 + (1 * 3)
    ≡⟨⟩ 3 + (3 + (0 * 3))
    ≡⟨⟩ 3 + (3 + 0)
    ≡⟨⟩ 3 + 3
    ≡⟨⟩ 6 ∎
    
_^_ : ℕ → ℕ → ℕ
a ^ zero = 1
a ^ suc n = a * (a ^ n)

_ : 3 ^ 2 ≡ 9
_ = begin 3 ^ 2
    ≡⟨⟩ 3 * (3 ^ 1)
    ≡⟨⟩ 3 * (3 * (3 ^ 0))
    ≡⟨⟩ 3 * (3 * 1)
    ≡⟨⟩ 3 * 3
    ≡⟨⟩ 9 ∎

_∸_ : ℕ → ℕ → ℕ
m ∸ zero = 0
zero ∸ n = n
suc m ∸ suc n = m ∸ n

infixl 6 _+_ _∸_
infixl 7 _*_

_! : ℕ → ℕ
zero ! = 1
suc n ! = suc n * n !

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

_ : Bin
_ = ⟨⟩ I O I I

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = (inc x) O

_ : (inc (⟨⟩ I O I I)) ≡ ⟨⟩ I I O O
_ = refl

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = from b * 2
from (b I) = from b * 2 + 1

_ : from (⟨⟩ I O I I) ≡ 11
_ = refl

_ : to 11 ≡ ⟨⟩ I O I I
_ = refl
