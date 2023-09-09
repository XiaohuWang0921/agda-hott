{-# OPTIONS --without-K --safe #-}

module Data.Nat.Base where

open import Level
open import Data.Nat.Core public
open import Relation.Core

infix 4 _≤_
data _≤_ : Rel ℕ 0ℓ where
  z≤n : ∀ {n} → 0 ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n
