{-# OPTIONS --without-K --safe #-}

module HoTT.Presheaf where

open import Level
open import Relation.Binary.Core
open import Relation.Binary.Bundles
open import Relation.Binary.Structures
open import HoTT.EqNotation hiding (isEquivalence; cong)
open import HoTT.Setoid.Morphism as Mor using (_⟶_; _⟨$⟩_; cong; _⊖_)
open import Data.Nat.Base hiding (_⊔_; suc)
open import HoTT.OFF
open import Function.Base hiding (id; _∘_)

private
  variable
    l m n : ℕ

record Presheaf a ℓ : Set (suc (a ⊔ ℓ)) where
  field
    Space : ℕ → Setoid a ℓ
    morph : OFF m n → Space n ⟶ Space m
    morph-id : morph (id {n}) ⊖ Mor.id
    morph-∘ : (f : OFF m n) (g : OFF l m) → morph (f ∘ g) ⊖ morph g Mor.∘ morph f

  Simplex : ℕ → Set a
  Simplex n = Space n .Setoid.Carrier

  _≈_ : Rel (Simplex n) ℓ
  _≈_ = Space _ .Setoid._≈_

  fmap : OFF m n → Simplex n → Simplex m
  fmap f = morph f ⟨$⟩_

  isEquivalence : IsEquivalence (_≈_ {n})
  isEquivalence = Space _ .Setoid.isEquivalence

  fmap-cong : (f : OFF m n) → fmap f Preserves _≈_ ⟶ _≈_
  fmap-cong f = morph f .cong

Hom : ℕ → Presheaf 0ℓ 0ℓ
Hom m = record
  { Space = λ n → setoid (OFF n m)
  ; morph = λ f → record
    { _⟨$⟩_ = _∘ f
    ; cong = icong
    }
  ; morph-id = ∘-identityʳ $-
  ; morph-∘ = λ f g {h} → ∘-assoc h f g ⋆
  }
