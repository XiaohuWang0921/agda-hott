{-# OPTIONS --without-K --safe #-}

module Data.Nat.Base where

open import Level
open import Data.Nat.Core public
open import Relation.Core
open import Data.Bool.Base hiding (_≤?_; _≤_)
open import Universe.Set

infix 4 _≤?_ _≤_ _<_

_≤?_ : ℕ → ℕ → Bool
zero ≤? _ = true
suc _ ≤? zero = false
suc m ≤? suc n = m ≤? n

data _≤_ : Rel ℕ 0ℓ where
  0≤n : ∀ {n} → 0 ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

_<_ : Rel ℕ 0ℓ
_<_ = _≤_ ∘ suc
