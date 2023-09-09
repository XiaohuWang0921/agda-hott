{-# OPTIONS --without-K --safe #-}

module Relation.Core where

open import Level

Rel : ∀ {a} (A : Set a) → ∀ ℓ → Set (a ⊔ ℓsuc ℓ)
Rel A ℓ = A → A → Set ℓ
