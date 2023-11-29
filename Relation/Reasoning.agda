{-# OPTIONS --without-K --safe #-}

open import Relation.Core

module Relation.Reasoning {a r} {A : Set a} (_≈_ : Rel A r) where

open import Relation.Equality.Core as Eq

infixr 2 step-≡ step-≡˘ _≡⟨⟩_

step-≡ : ∀ x {y z} → y ≈ z → x ≡ y → x ≈ z
step-≡ _ yRz Eq.refl = yRz

step-≡˘ : ∀ x {y z} → y ≈ z → y ≡ x → x ≈ z
step-≡˘ _ xRz Eq.refl = xRz

_≡⟨⟩_ : ∀ x {y} → x ≈ y → x ≈ y
_ ≡⟨⟩ xRy = xRy

syntax step-≡ x y≈z x≡y = x ≡⟨ x≡y ⟩ y≈z
syntax step-≡˘ x y≈z y≡x = x ≡˘⟨ y≡x ⟩ y≈z

module Refl (refl : ∀ {x} → x ≈ x) where

  infix 3 _∎

  _∎ : ∀ x → x ≈ x
  _ ∎ = refl

module Trig (trig : ∀ {x y z} → y ≈ x → y ≈ z → x ≈ z) where

  infixr 2 step-≈˘

  step-≈˘ : ∀ x {y z} → y ≈ z → y ≈ x → x ≈ z
  step-≈˘ _ y≈z y≈x = trig y≈x y≈z

  syntax step-≈˘ x y≈z y≈x = x ≈˘⟨ y≈x ⟩ y≈z

module Equiv (refl : ∀ {x} → x ≈ x) (trig : ∀ {x y z} → y ≈ x → y ≈ z → x ≈ z) where
  open Refl refl public
  open Trig trig public

  infixr 2 step-≈

  step-≈ : ∀ x {y z} → y ≈ z → x ≈ y → x ≈ z
  step-≈ _ y≈z x≈y = trig (trig x≈y refl) y≈z

  syntax step-≈ x y≈z x≈y = x ≈⟨ x≈y ⟩ y≈z
