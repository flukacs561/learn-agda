# Part I Chapter 4: Equality
```agda
module PLFA.Equality where
```

## Defining equality

Two things are equal if they are the same thing.
```agda
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_
```

Equality is symmetric, transitive and obviously reflexive, hence an equivalence relation. It is also a congruence with respect to function application and satisfies substitution in predicates.
```agda
sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

reflexive : ∀ {A : Set} {x : A} → x ≡ x
reflexive = refl

trans : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong-app : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀ {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl px = px
```

## ≡-Reasoning

### A nested module

The contents of nested modules need to be indented appropriately.
```agda
module ≡-Reasoning {A : Set} where

  infix 1 begin_
  infixr 2 step-≡-∣ step-≡-⟩
  infix 3 _∎

  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin x≡y = x≡y

  step-≡-∣ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
  step-≡-∣ x x≡y = x≡y

  step-≡-⟩ : ∀ (x : A) {y z  : A} → y ≡ z → x ≡ y → x ≡ z
  step-≡-⟩ x y≡z x≡y = trans x≡y y≡z

  syntax step-≡-∣ x x≡y = x ≡⟨⟩ x≡y
  syntax step-≡-⟩ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

  _∎ : ∀ (x : A) → x ≡ x
  x ∎ = refl
```

Once we defined a nested module, it needs to be opened for it to be available in the rest of the file.
```agda
open ≡-Reasoning
```

### A simple example, explained

```agda
trans' : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans' {A} {x} {y} {z} x≡y y≡z = begin x ≡⟨ x≡y ⟩ y ≡⟨ y≡z ⟩ z ∎
```

Let us analyse how `trans` is evaluated.
1. `begin` can be safely discarded as it is purely cosmetic: it simply returns its argument.
1. Since everything associates to the right, we begin with `z ∎`.
1. Observe that `(trans y≡z refl)` is just the proof that `y≡z`.
1. From here on it is just trivial subsitution/simplification.

```pseudo-code
x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ (z ∎))
x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ refl)
x ≡⟨ x≡y ⟩ (trans x≡y y≡z)
trans x≡y (trans y≡z refl)
trans x≡y y≡z
x ≡ z
```

### A slightly more involved, but familiar example

Declaring an identifier with a signature, but not providing a definition is called a postulate.
```agda
data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
Z + n = n
S m + n = S (m + n)

+-identity : ∀ (m : ℕ) → m + Z ≡ m
+-suc : ∀ (m n : ℕ) → m + S n ≡ S (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m Z = begin m + Z ≡⟨ +-identity m ⟩ m ≡⟨⟩ Z + m ∎
+-comm m (S n) = begin m + S n ≡⟨ +-suc m n ⟩ S (m + n) ≡⟨ cong S (+-comm m n) ⟩ S (n + m) ≡⟨⟩ S n + m ∎
```

The explanation is quite similar to the previous one:
```pseudo-code
m + S n ≡⟨ +-suc m n ⟩ (S (m + n) (≡⟨ cong S (+-comm m n) ⟩ (S (n + m) ≡⟨⟩ (S n + m ∎))))
m + S n ≡⟨ +-suc m n ⟩ (trans (cong S (+-comm m n)) refl)
trans (+-suc m n) (trans (cong S (+-comm m n)) refl)
```

### Exercise ≤-Reasoning

First, the required definitions.
```agda
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → Z ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → S m ≤ S n

infix 4 _≤_

≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)
```

Then the definition of the new syntax
```agda
module ≤-Reasoning where

  infix 1 begin-≤_
  infixr 2 step-≤-∣ step-≤-⟩ _≡'⟨_⟩_
  infix 3 _∎'

  begin-≤_ : ∀ {x y : ℕ} → x ≤ y → x ≤ y
  begin-≤ x≤y = x≤y

  step-≤-∣ : ∀ (x : ℕ) {y : ℕ} → x ≤ y → x ≤ y
  step-≤-∣ x x≤y = x≤y

  step-≤-⟩ : ∀ (x : ℕ) {y z : ℕ} → y ≤ z → x ≤ y → x ≤ z
  step-≤-⟩ x y≤z x≤y = ≤-trans x≤y y≤z

  syntax step-≤-∣ x x≤y = x ≤⟨⟩ x≤y
  syntax step-≤-⟩ x y≤z x≤y = x ≤⟨ x≤y ⟩ y≤z

  _≡'⟨_⟩_ : ∀ (m : ℕ) {n p : ℕ} → m ≡ n → n ≤ p → m ≤ p
  m ≡'⟨ refl ⟩ n≤p = n≤p

  _∎' : ∀ (n : ℕ) → n ≤ n
  Z ∎' = z≤n
  S n ∎' = s≤s (n ∎')

open ≤-Reasoning
```

And finally the more readable proofs.
```agda
+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ Z p q p≤q = begin-≤ Z + p ≡'⟨ refl ⟩ p ≤⟨ p≤q ⟩ q ≡'⟨ refl ⟩ Z + q ∎'
+-monoʳ-≤ (S n) p q p≤q = begin-≤ S n + p ≡'⟨ refl ⟩ S (n + p) ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩ S (n + q) ≡'⟨ refl ⟩ S n + q ∎'

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n = begin-≤ m + p ≡'⟨ +-comm m p ⟩ p + m ≤⟨ +-monoʳ-≤ p m n m≤n ⟩ p + n ≡'⟨ +-comm p n ⟩ n + p ∎'

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = begin-≤ m + p ≤⟨ +-monoˡ-≤ m n p m≤n ⟩ n + p ≤⟨ +-monoʳ-≤ n p q p≤q ⟩ n + q ∎'
```

## Rewriting

Some preparations.
```agda
data even : ℕ → Set
data odd : ℕ → Set

data even where
  even-Z : even Z
  even-S : ∀ {n : ℕ} → odd n → even (S n)

data odd where
  odd-S : ∀ {n : ℕ} → even n → odd (S n)

{-# BUILTIN EQUALITY _≡_ #-}
```

Since we have proven `+-comm` and `even m → even n → even (m + n)`, we sould be able to prove `even (n + m)`. This is when rewrite comes into the picture.
```agda
even-comm : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm m n ev rewrite +-comm m n = ev
```

`rewrite` is just syntactic sugar for the following usage of a `with`-clause.
```agda
even-comm' : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm' m n ev with   m + n  | +-comm m n
...                  | .(n + m) | refl       = ev
```

I sill can't quite understand this `with`-clause thing in Agda.

```agda
even-comm'' : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm'' m n = subst even (+-comm m n)
```

This might be worth unpacking quickly. The function `subst` takes a predicate `P` and a proof that `x` and `y` are equivalent (equal) and produces a proof that whenever `x` satisfies `P`, so does `y`. In our case this translates to the following. `subst` takes the predicate that a natural number is `even`, and a proof that `m + n ≡ n + m` (that is `+-comm m n`).

```pseudo-code
+-comm m n : m + n ≡ n m
even : ℕ → Set
subst : {A : Set} {x y  : A} → (P : A → Set) → x ≡ y → P x → P y
```

## Leibniz's definition of equality

> Identity of the indiscernibles: two objects are equal if and only if they satisfy the same properties.

```agda
_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

refl-≐ : ∀ {A : Set} {x : A} → x ≐ x
refl-≐ P Px = Px

trans-≐ : ∀ {A : Set} {x y z : A} → x ≐ y → y ≐ z → x ≐ z
trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)
```

Symmetry is a bit more involved, so let's unpack it.
1. `Q z` is the predicate that asserts that whenever `z` satisfies `P`, so does `x`.
1. Hence, `Q x` is the tautology asserting that whenever `x` satisfies `P`, so does `x`. Clear so far.
1. Now a term of type `Q y` is proof that whenever `y` satisfies `P`, so does `x`. _Id est_, this is what we want to prove.
1. Take look at `x≐y Q`. This is a function that produces a proof of `Q y` whenever it is given a proof of `Q x`. But we do have such a proof, namely `Qx`.

```agda
sym-≐ : ∀ {A : Set} {x y : A} → x ≐ y → y ≐ x
sym-≐ {A} {x} {y} x≐y P = Qy
  where
    Q : A → Set
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx
```

Next we show that Martin-Löf equality is equivalent to Leibniz equality.

```agda
≡-implies-≐ : ∀ {A : Set} {x y : A} → x ≡ y → x ≐ y
≡-implies-≐ x≡y P = subst P x≡y

≐-implies-≡ : ∀ {A : Set} {x y : A} → x ≐ y → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y = x≐y (x ≡_) refl
```

## Universe Polymorphism

being aware to the hierarchiy of universes `set`, `set₁`, `set₂`, etc. the question might arise, what if we want to compare values from different universes (or levels)? Note that levels are isomorphic to natural numbers, hence the similar name of the constructors.

```agda
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

data _≡'_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl' : x ≡' x

sym' : ∀ {ℓ : Level} {A : Set ℓ} {x y : A} → x ≡' y → y ≡' x
sym' refl' = refl'

_≐'_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐'_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P y → P y

_∘_ : ∀ {ℓ : Level} {A B C : Set ℓ} → (A → B) → (B → C) → (A → C)
(f ∘ g) c = g (f c)
```
