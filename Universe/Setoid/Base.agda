{-# OPTIONS --without-K --safe #-}

module Universe.Setoid.Base where

open import Level
open import Relation.Core
open import Relation.Equality.Core as Eq using (_≡_)

record Setoid a r : Set (ℓsuc (a ⊔ r)) where
  infix 4 _≈_
  field
    Carrier : Set a
    _≈_ : Rel Carrier r
    refl : ∀ {x} → x ≈ x
    trig : ∀ {x y z} → y ≈ x → y ≈ z → x ≈ z

  reflexive : ∀ {x y} → x ≡ y → x ≈ y
  reflexive Eq.refl = refl

  sym : ∀ {x y} → x ≈ y → y ≈ x
  sym x≈y = trig x≈y refl

  trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
  trans x≈y y≈z = trig (sym x≈y) y≈z
