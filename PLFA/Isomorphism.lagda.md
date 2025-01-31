# Part I: Isomorphism

```agda
module PLFA.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
```

An example of pattern-matched λ-expression.
```agda
data Bool : Set where
  true : Bool
  false : Bool

valami : ℕ → Bool
valami = λ{zero → true; (suc n) → false}
```

*Extensionality* means that two functions are equal if they agree on every point. We postulate extensionality, which is fine as it is known to be consistent with the theory Agda is based on.

```agda
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g

_+'_ : ℕ → ℕ → ℕ
m +' zero = m
m +' suc n = suc (m +' n)

same-app : ∀ (m n : ℕ) → m +' n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
    helper : ∀ (m n : ℕ) → m +' n ≡ n + m
    helper m zero = refl
    helper m (suc n) = cong suc (helper m n)

same : _+'_ ≡ _+_
same = extensionality (λ m → extensionality (λ n → same-app m n))
```

Let's take a closer look at this last expression. What this does is first assert that ∀ n : ℕ we have _+ n ≡ _+' n, and then, via extensionality we get _+_ ≡ _+'_.

