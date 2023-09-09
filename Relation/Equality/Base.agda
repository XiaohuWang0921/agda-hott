{-# OPTIONS --without-K --safe #-}

module Relation.Equality.Base where

open import Relation.Equality.Core public

open import Level
open import Universe.Setoid.Base

private
  variable
    a : Level
    A : Set a

sym : {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl p = p

setoid : (A : Set a) → Setoid a a
setoid A = record
  { Carrier = A
  ; _≈_ = _≡_
  ; refl = refl
  ; sym = sym
  ; trans = trans
  }
