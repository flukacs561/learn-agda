module PLFA.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm)

open import PLFA.Bin

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

+-identityʳ' : ∀ {m : ℕ} → m + zero ≡ m
+-identityʳ' = +-identityʳ _

infix 4 _≤_

-- This is crazy stuff...
inv-s≤s : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n = forward (s≤s m≤n)
...                        | flipped n≤m = flipped (s≤s n≤m)

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = (+-monoʳ-≤ p m n m≤n)

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-mono-r-≤ : ∀ (n p q : ℕ) → p ≤ q → n * p ≤ n * q
*-mono-r-≤ zero p q p≤q = z≤n
*-mono-r-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-mono-r-≤ n p q p≤q)

*-mono-l-≤ : ∀ (m n p : ℕ) → m ≤ n → m * p ≤ n * p
*-mono-l-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-mono-r-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-mono-l-≤ m n p m≤n) (*-mono-r-≤ n p q p≤q)

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

<-trans : ∀ (m n p : ℕ) → m < n → n < p → m < p
<-trans zero (suc n) (suc p) z<s n<p = z<s
<-trans (suc m) (suc n) (suc p) (s<s m<n) (s<s n<p) = s<s (<-trans m n p m<n n<p)

-- data _>_ : ℕ → ℕ → Set where
--   _>'_ : ∀ (m n : ℕ) → n < m → m > n

-- data Tricho (m n : ℕ) : Set where
--   fwd : m < n → Tricho m n
--   bwd : n < m → Tricho m n
--   eql : m ≣ n → Tricho m n

≤→< : ∀ (m n : ℕ) → suc m ≤ n → m < n
≤→< zero (suc n) sm≤n = z<s
≤→< (suc m) (suc n) (s≤s sm≤n) = s<s (≤→< m n sm≤n)

<→≤ : ∀ (m n : ℕ) → m < n → suc m ≤ n
<→≤ zero (suc n) m<n = s≤s z≤n
<→≤ (suc m) (suc n) (s<s m<n) = s≤s (<→≤ m n m<n)

data even : ℕ → Set
data odd : ℕ → Set

data even where
  zero : even zero
  suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  suc : ∀ {n : ℕ} → even n → odd (suc n)

-- mutually recursive functions
e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
o+e≡o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)

e+e≡e zero n = n
e+e≡e (suc m) n = suc (o+e≡o m n)

o+e≡o (suc m) n = suc (e+e≡e m n)

e+o≡o : ∀ {m n : ℕ} → even m → odd n → odd (m + n)
e+o≡o {m} {n} em on rewrite +-comm m n = o+e≡o on em

o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e (suc em) on = suc (e+o≡o em on)

data One : Bin → Set where
  one : One (⟨⟩ I)
  app-zero : ∀ (b : Bin) → One b → One (b O)
  app-one : ∀ (b : Bin) → One b → One (b I)

data Can : Bin → Set where
  can-zero : Can ⟨⟩
  one-is-can : ∀ (b : Bin) → One b → Can b

one-inc : ∀ (b : Bin) → One b → One (inc b)
one-inc (b O) (app-zero b one-b) = app-one b one-b
one-inc (b I) one = app-zero (inc ⟨⟩) one
one-inc (b I) (app-one b one-b) = app-zero (inc b) (one-inc b one-b)

can-inc : ∀ (b : Bin) → Can b → Can (inc b)
can-inc ⟨⟩ _ = one-is-can (inc ⟨⟩) one
can-inc (b O) (one-is-can (b O) (app-zero b one-b)) = one-is-can (inc (b O)) (app-one b one-b)
can-inc (b I) (one-is-can (⟨⟩ I) one) = one-is-can (inc (b I)) (app-zero (inc b) one)
can-inc (b I) (one-is-can (b I) (app-one b one-b)) = one-is-can (inc (b I)) (app-zero (inc b) (one-inc b one-b))

can-to : ∀ (n : ℕ) → Can (to n)
can-to zero = can-zero
can-to (suc n) = can-inc (to n) (can-to n)

can-from-id : ∀ (b : Bin) → Can b → to (from b) ≡ b
can-from-id ⟨⟩ can-zero = refl
can-from-id (b O) (one-is-can (b O) (app-zero b one-b)) = {!!}
-- can-from-id b (one-is-can b one-b) : to (from b) ≡ b
can-from-id (b I) (one-is-can (⟨⟩ I) one) = refl
can-from-id (b I) (one-is-can (b I) (app-one b one-b)) = {!!}
