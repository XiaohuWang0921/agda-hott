{-# OPTIONS --without-K --safe #-}

module Data.Bool.Base where

open import Data.Bool.Core public
open import Level
open import Relation.Core
open import Data.Unit.Core
open import Data.Empty.Base
open import Algebra.Core
open import Universe.Set

infixr 5 _∨_
infixr 6 _∧_

if_then_else_ : ∀ {ℓ} {A : Set ℓ} → Bool → A → A → A
if false then _ else f = f
if true then t else _ = t

_∨_ : Op₂ Bool
false ∨ b = b
true ∨ _ = true

_∧_ : Op₂ Bool
false ∧ _ = false
true ∧ b = b

not : Op₁ Bool
not false = true
not true = false

_Reflects_ : ∀ {ℓ} → Bool → Set ℓ → Set ℓ
false Reflects P = P → ⊥
true Reflects P = P

_Deflects_ : ∀ {ℓ} → Bool → Set ℓ → Set ℓ
_Deflects_ = _Reflects_ ∘ not

T : Bool → Set
T false = ⊥
T true = ⊤

infix 4 _≤?_ _≟_ _≤_

_≤?_ : Op₂ Bool
false ≤? _ = true
true ≤? b = b

_≟_ : Op₂ Bool
false ≟ false = true
true ≟ true = true
_ ≟ _ = false

data _≤_ : Rel Bool 0ℓ where
  b≤b : ∀ {b} → b ≤ b
  f≤t : false ≤ true
