{-# OPTIONS --without-K --safe #-}

module Algebra.Core where

open import Agda.Primitive
open import Data.Nat.Core

private
  variable
    a : Level

Hop : ℕ → Set a → Set a → Set a
Hop zero _ B = B
Hop (suc n) A B = A → Hop n A B

Op : ℕ → Hop 1 (Set a) (Set a)
Op zero    A = A
Op (suc n) A = A → Op n A

Hop₁ : Op 2 (Set a)
Hop₁ = Hop 1

Hop₂ : Op 2 (Set a)
Hop₂ = Hop 1

Op₁ : Op 1 (Set a)
Op₁ = Op 1

Op₂ : Op 1 (Set a)
Op₂ = Op 2
