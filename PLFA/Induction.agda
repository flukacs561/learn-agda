module PLFA.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = begin (zero + n) + p
                   ≡⟨⟩ n + p
                   ≡⟨⟩ zero + (n + p) ∎
+-assoc (suc m) n p = begin (suc m + n) + p
                      ≡⟨⟩ suc (m + n) + p
                      ≡⟨⟩ suc ((m + n) + p)
                      ≡⟨ cong suc (+-assoc m n p) ⟩ suc (m + (n + p))
                      ≡⟨⟩ suc m + (n + p) ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = begin zero + zero ≡⟨⟩ zero ∎
+-identityʳ (suc m) = begin suc m + zero ≡⟨⟩ suc (m + zero) ≡⟨ cong suc (+-identityʳ m) ⟩ suc m ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = begin zero + suc n ≡⟨⟩ suc n ≡⟨⟩ suc (zero + n) ∎
+-suc (suc m) n = begin suc m + suc n
                  ≡⟨⟩ suc (m + suc n)
                  ≡⟨ cong suc (+-suc m n) ⟩ suc (suc (m + n))
                  ≡⟨⟩ suc (suc m + n) ∎

+-identityˡ : ∀ (m : ℕ) → zero + m ≡ m
+-identityˡ zero = begin zero + zero ≡⟨⟩ zero ∎
+-identityˡ (suc m) = begin zero + suc m ≡⟨⟩ suc (zero + m) ≡⟨ cong suc (+-identityˡ m) ⟩ suc m ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = begin m + zero ≡⟨ +-identityʳ m ⟩ m ≡⟨⟩ zero + m ∎
+-comm m (suc n) = begin m + suc n ≡⟨ +-suc m n ⟩ suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩ suc (n + m) ≡⟨⟩ suc n + m ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q = begin (m + n) + (p + q)
                      ≡⟨ sym (+-assoc (m + n) p q) ⟩ ((m + n) + p) + q
                      ≡⟨ cong (_+ q) (+-assoc m n p) ⟩ (m + (n + p)) + q ∎

+-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc' zero n p = refl
+-assoc' (suc m) n p rewrite +-assoc' m n p = refl

+-identity' : ∀ (m : ℕ) → m + zero ≡ m
+-identity' zero = refl
+-identity' (suc m) rewrite +-identity' m = refl

+-suc' : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc' zero n = refl
+-suc' (suc m) n rewrite +-suc' m n = refl

+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' m zero rewrite +-identity' m = refl
+-comm' m (suc n) rewrite +-suc' m n | +-comm' m n = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite sym (+-assoc' m n p) | +-comm' m n | +-assoc' n m  p = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ (m * p) + (n * p)
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | sym (+-assoc' p (m * p) (n * p)) = refl

-- *-distrib-+ (suc m) n p = begin (suc m + n) * p
--                           ≡⟨⟩
--                             suc (m + n) * p ≡⟨⟩ p + ((m + n) * p)
--                           ≡⟨ cong (p +_) (*-distrib-+ m n p) ⟩
--                             p + ((m * p) + (n * p))
--                           ≡⟨ sym (+-assoc' p (m * p) (n * p)) ⟩
--                             (p + (m * p)) + (n * p)
--                           ≡⟨⟩
--                             (suc m * p) + (n * p) ∎

*-suc : ∀ (m n : ℕ) → m + m * n ≡ m * suc n
*-suc zero n = refl
*-suc (suc m) n rewrite sym (+-assoc' m n (m * n)) | +-comm' m n | +-assoc' n m (m * n) | *-suc m n = refl

n*0≡0 : ∀ (n : ℕ) → n * zero ≡ zero
n*0≡0 zero = refl
n*0≡0 (suc n) rewrite n*0≡0 n = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n = begin zero ≡⟨ sym (n*0≡0 n) ⟩ n * zero ∎
*-comm (suc m) n rewrite *-comm m n | *-suc n m = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | sym (*-assoc m n p) = refl

*-identityˡ : ∀ (n : ℕ) → n * 1 ≡ n
*-identityˡ zero = refl
*-identityˡ (suc n) rewrite *-identityˡ n = refl

^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m n zero rewrite +-identityʳ n | *-identityˡ (m ^ n) = refl
^-distribˡ-+-* m n (suc p) rewrite +-suc n p | ^-distribˡ-+-* m n p | sym (*-assoc m (m ^ n) (m ^ p)) | *-comm m (m ^ n) | *-assoc (m ^ n) m (m ^ p) = refl

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero rewrite n*0≡0 n = refl
^-*-assoc m n (suc p) rewrite sym (*-suc n p) | ^-*-assoc m n p | sym (^-distribˡ-+-* m n (n * p))= refl

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p) rewrite ^-distribʳ-* m n p | sym (*-assoc (m * n) (m ^ p) (n ^ p)) | *-comm m n | *-assoc n m (m ^ p) | *-comm n (m * m ^ p) | *-assoc (m * m ^ p) n (n ^ p) = refl

open import PLFA.Bin

n+1≡sucn : ∀ (n : ℕ) → n + 1 ≡ suc n
n+1≡sucn zero = refl
n+1≡sucn (suc n) rewrite n+1≡sucn n = refl

law1 : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
law1 ⟨⟩ = refl
law1 (b O) = begin from b * 2 + 1 ≡⟨ n+1≡sucn (from b * 2) ⟩ suc (from b * 2) ∎
law1 (b I) rewrite law1 b = begin suc (suc (from b * 2)) ≡⟨ sym (n+1≡sucn (suc (from b * 2))) ⟩ suc (from b * 2) + 1 ∎

law2CounterExample : to (from (⟨⟩ O O I)) ≡ ⟨⟩ I
law2CounterExample = refl

law3 : ∀ (n : ℕ) → from (to n) ≡ n
law3 zero = refl
law3 (suc n) rewrite law1 (to n) | law3 n = refl
