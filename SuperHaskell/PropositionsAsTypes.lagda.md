--
title: Super Haskell Talk: Propositions as Types -- Notes
author: Ferenc Lukács
date: 2025-01-02
--

```agda
module SuperHaskell.PropositionsAsTypes where

open import SuperHaskell.Basics
open import Data.Nat hiding (_≤_ ; _<_)
open import Data.Bool hiding (_≤_ ; _<_)

```

## The equality type

This kind of says that A is an inhabited type.
`refl` is the only inhabitant of the type x ≡ x, which corresponds to the proposition 'x equals x'.
```agda
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

11+4≡fifteen : (11 + 4) ≡ fifteen
11+4≡fifteen = refl
```

This sould obviously be impossible to prove as it is equivalent to the type/proposition 14≡15.

```pseudo-code
11+3≡fifteen : (11 + 3) ≡ fifteen
11+3≡fifteen = tt
```

The following types represent the propositions 'True' and 'False'. A type (proposition) is 'true' (can be proved <=> there exists a proof proving it) if and only if it is inhabited (the inhabitant _is_ the proof proving it).
```agda
data ⊥ : Set where
data ⊤ : Set where
  tt : ⊤

_≤_ : ℕ → ℕ → Set
zero ≤ n = ⊤
suc m ≤ zero = ⊥
suc m ≤ suc n = m ≤ n

zeroIsLEQTo100 : 0 ≤ 100
zeroIsLEQTo100 = tt
```

Strict inequality
```agda
_<_ : ℕ → ℕ → Set
zero < zero = ⊥
suc m < zero = ⊥
zero < suc n = ⊤
suc m < suc n = m < n
```

## Type-sace subtraction

Observe that Agda knows that this is already a complete function: we don't need to define the case `zero - suc n` as no proof for `zero ≤ suc n` can ever be given.

```agda
_-_ : (m : ℕ) → (n : ℕ) → {p : n ≤ m} → ℕ
(m - zero) {tt} = m
(suc m - suc n) {p} = (m - n) {p}

infixr 50 _-_

5minus3equals2 : (5 - 2) {tt} ≡ 3
5minus3equals2 = refl
```

## Prototypical example: Vectors of a given size

```agda
data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _::_ : {n : ℕ} → (a : A) → Vec A n → Vec A (suc n)

infixr 5 _::_
```

For this to be type-safe, you need to supply a proof that the length of the vector is at least as big as the number of elements you want to take from it. Observe that when pattern matchin on `n` in in the last case, Agda knows automatically that a proof of `(suc n) ≤ length of (a :: v)` is equivalent to a proof of `n ≤ length of v`.
```agda
take : ∀ {A length} → (n : ℕ) → {p : n ≤ length} → Vec A length → Vec A n
take zero [] = []
take zero _ = []
take (suc n) {p} (a :: v) = a :: take n {p} v
```

Here is the implementation of some standard methods for Vectors.
```agda
concat : ∀ {A m n} → Vec A m → Vec A n → Vec A (m + n)
concat [] v = v
concat (a :: u) v = a :: concat u v

lookup : ∀ {A : Set} {length : ℕ} → Vec A length → (n : ℕ) → {p : n < length} → A
lookup (a :: v) zero {p} = a
lookup (_ :: v) (suc n) {p} = lookup v n {p}

[_] : ∀ {A : Set} → A → Vec A 1
[ a ] = a :: []
```

We can construct a proof showing that in the vector `v = [4, 5, 6, 7]` the element at index 2 is 6.
```agda
correctIndex : let
  v : Vec ℕ 4
  v = 4 :: 5 :: 6 :: 7 :: []
  in lookup v 2 {tt} ≡ 6
correctIndex = refl
```

Some higher-order functions:
```agda
map : ∀ {A B : Set} {n : ℕ} → (A → B) → Vec A n → Vec B n
map f [] = []
map f (a :: v) = f a :: map f v

pwise : ∀ {A B : Set} {n : ℕ} → Vec (A → B) n → Vec A n → Vec B n
pwise [] [] = []
pwise (f :: fs) (a :: as) = f a :: pwise fs as

replicate' : ∀ {A : Set} {n : ℕ} → A → Vec A n
replicate' {n = zero} a = []
replicate' {n = suc m} a = a :: replicate' {n = m} a
```

We wan easily make `n` an explicit argument here:
```agda
replicate : ∀ {A : Set} (n : ℕ) → A → Vec A n
replicate zero a = []
replicate (suc m) a = a :: replicate m a
```

### Transposing a 2-dimensional vector
1. The usage of `replicate'` is quite interesting here. Putting simply `[]` would result in an error: `zero != n of type ℕ`. That is, we can have an empty vector of non-empty vectors, or, to put it differently: `[] : Vec (Vec A n) 0 != [] : Vec (Vec A m) 0` if n != m. We have to make sure that we have the correct empty vector.

In our current situation, on the left hand side we have `[] : Vec (Vec A n) 0`, so on the right we need `[] : Vec (Vec A 0) n`.

2. Next we have the non-empty case
```pseudo-code
as : Vec A n
ass : Vec (Vec A n) (m - 1)
transpose ass : Vec (Vec A (m - 1)) n
_::_ : A → Vec A n → Vec A (suc n)
replicate' _::_ : Vec (A → Vec A n → Vec A (suc n)) m
pwise (replicate' _::_) as : Vec (Vec A n → Vec A (suc n)) m
```
In actual Agda code:
```agda
transpose : ∀ {A m n} → Vec (Vec A n) m → Vec (Vec A m) n
transpose [] = replicate' []
transpose (as :: ass) = pwise (pwise (replicate' _::_) as) (transpose ass)
```

This is a bit inovlved, so let us prove that in the case of 3 by 3 matrices, it really does work.
```agda
transposeWorks3x3 : ∀ {A : Set} {one two thr : A} → transpose
  (
    (one :: one :: one :: []) ::
    (two :: two :: two :: []) ::
    (thr :: thr :: thr :: []) :: []
  ) ≡
  (
    (one :: two :: thr :: []) ::
    (one :: two :: thr :: []) ::
    (one :: two :: thr :: []) :: []
  )
transposeWorks3x3 = refl
```
This must be black megic...

```agda
zipWith : ∀ {A B C n} → (A → B → C) → Vec A n → Vec B n → Vec C n
zipWith _ [] [] = []
zipWith f (a :: u) (b :: v) = f a b :: zipWith f u v
```

## Dependent product and sum
```agda
record Σ (A : Set) (B : (a : A) → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

NatIfTrue,ListOfTopsIfFalse : ∀ {n} → Bool → Set
NatIfTrue,ListOfTopsIfFalse false = ℕ
NatIfTrue,ListOfTopsIfFalse {n} true = Vec ⊤ n

dependentProd : ∀ {n} → Σ Bool (NatIfTrue,ListOfTopsIfFalse {n})
dependentProd = false , 3

dependentProd' : ∀ {n} → Σ Bool (NatIfTrue,ListOfTopsIfFalse {n})
dependentProd' = true , replicate' tt
```
Observe that in `dependentProd'` Agda can infer that the list of `tt`s should have 3 elements.

We can even define the type of natural numbers greater than 5
```agda
GreaterThan5 : Set
GreaterThan5 = Σ ℕ (λ n → 5 < n)

seven : GreaterThan5
seven = 7 , tt
```

Or generalise even further:
```agda
GreaterThan : ℕ → Set
GreaterThan m = Σ ℕ (λ n → m < n)

nine : GreaterThan 7
nine = 9 , tt
```
