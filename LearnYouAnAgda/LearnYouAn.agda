module LearnYouAnAgda.LearnYouAn where

open import Agda.Builtin.Bool

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + m = m
suc n + m = suc (n + m)

-- We are going to construct the logical judgement _even_

data _even : ℕ → Set where
  ZERO : zero even
  STEP : ∀ { n } → n even → (suc (suc n)) even

-- Prove that 4 is even
proof₁ : suc (suc (suc (suc zero))) even
proof₁ = STEP { suc (suc zero) } (STEP { zero } ZERO)

proof₂ : suc (suc (suc (suc zero))) even
proof₂ = STEP (STEP ZERO)

-- This corresponds to the implication: "if a natural number exists, it exists".
proof₃ : ℕ → ℕ
proof₃ ν = ν

-- This is the generalisation of the previous fact to any proposition.
proof₃' : (A : Set) → A → A
proof₃' _ x = x

proof₃'' : ℕ → ℕ
proof₃'' = proof₃' ℕ
