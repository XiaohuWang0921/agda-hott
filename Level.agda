{-# OPTIONS --without-K --safe #-}

module Level where

open import Agda.Primitive public renaming
  ( lzero to 0ℓ
  ; lsuc  to ℓsuc
  )
open import Data.Nat.Core
open import Agda.Builtin.FromNat
open import Agda.Builtin.Unit
open import Algebra.Core

infixl 6 _ℕ+_
_ℕ+_ : ℕ → Op₁ Level
zero  ℕ+ ℓ = ℓ
suc n ℕ+ ℓ = ℓsuc (n ℕ+ ℓ)

Levelℕ : Number Level
Levelℕ = record
  { Constraint = λ _ → ⊤
  ; fromNat = λ n → n ℕ+ 0ℓ
  }
