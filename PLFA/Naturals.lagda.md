# Part I: Naturals
```agda
module PLFA.Naturals where
```

```agda
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
```

## Exercise `seven`
```agda
seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))
```

## Imports
```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl)
open Eq.≡-Reasoning using (begin_ ; step-≡-∣ ; _∎)
```

## Operations on natural numbers

We define addition recursively.
```agda
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)
```

Our first proof: 2 + 3 = 5
```agda
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
```

And with the usual notation for naturals. (This is where the pragma from earlier comes into the picture.)
```agda
_ : 2 + 3 ≡ 5
_ = begin 2 + 3
    ≡⟨⟩ suc (1 + 3)
    ≡⟨⟩ suc (suc (0 + 3))
    ≡⟨⟩ suc (suc 3)
    ≡⟨⟩ 5 ∎
```

In fact, Agda is smart enough to figure this out by herself.
```agda
_ : 2 + 3 ≡ 5
_ = refl
```

## Multiplication
```agda
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
```

## Exercixe `_^_`
```agda
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
```

## Monus
```agda
_∸_ : ℕ → ℕ → ℕ
m ∸ zero = 0
zero ∸ n = n
suc m ∸ suc n = m ∸ n
```

## Precedence
```agda
infixl 6 _+_ _∸_
infixl 7 _*_
```

This is just for fun.
```agda
_! : ℕ → ℕ
zero ! = 1
suc n ! = suc n * n !
```

## Exercise `Bin`
```agda
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
```
