{-# OPTIONS --without-K --safe #-}

module Universe.Presheaf.Fillable where

open import Level
open import Data.Nat.Base
open import Universe.Presheaf.Base hiding (id; _∘_)
open import Universe.Presheaf.Cycle
open import Universe.Setoid

record Fillable {a r} (P : Presheaf a r) (n : ℕ) : Set (a ⊔ r) where
  field
    fill : setoid P n ⟶ Presheaf.Space P (2 + n)
    isSection : (open Setoid (setoid P n ⇒ setoid P n)) → boundary P n ∘ fill ≈ id
