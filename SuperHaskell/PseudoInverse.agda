module SuperHaskell.PseudoInverse where

import Data.List as L
import Data.Maybe as M

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe

open import Data.Nat as Nat hiding (_+_ ; _*_ ; zero ; _≤ᵇ_)
open import Data.Float as Float hiding (_+_ ; _*_ ; _≤ᵇ_) renaming (Float to ℝ)
open import Data.Bool hiding (_≤_ ; _<_)

open import SuperHaskell.Basics
open import SuperHaskell.PropositionsAsTypes hiding (_≡_)
open import SuperHaskell.Matrix
open import Function

-- Foreign pragme: Insert this Haskell code in the compiled Agda module
{-# FOREIGN GHC
import HsMatrix
#-}

-- Compile pragma: Whenever you see this Agda postulate, generate this Haskell code.
postulate
  invertMatrixAsListTrusted : L.List (L.List ℝ) → L.List (L.List ℝ)
{-# COMPILE GHC invertMatrixAsListTrusted = invertMatrixAsList #-}

-- Turns out, this requires some stuff to happen in the background which I am not interested in figuring out.
