{-# OPTIONS --without-K --safe #-}

module Data.Vec.Properties where

open import Data.Vec.Base
open import Universe.Set
open import Relation.Equality.Base
open import Level
open import Data.Nat.Base
private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c
    n : ℕ

zipWith-cong : (f : A → B → C) {t u : Vec A n} {v w : Vec B n} → t ≗ u → v ≗ w → zipWith f t v ≗ zipWith f u w
zipWith-cong f t≗u v≗w i = cong₂ f (t≗u i) (v≗w i)
