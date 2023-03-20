{-# OPTIONS --without-K --safe #-}

module HoTT.Presheaf where

open import Level
open import Relation.Binary.Core
open import Relation.Binary.Bundles
open import Relation.Binary.Structures
open import HoTT.EqNotation hiding (isEquivalence; cong)
open import Function.Bundles
open import Data.Nat.Base hiding (_⊔_; suc)
open import HoTT.OFF
open import HoTT.OFF.Properties

private
  variable
    l m n : ℕ

record Presheaf a ℓ : Set (suc (a ⊔ ℓ)) where
  field
    Space : ℕ → Setoid a ℓ
    morph : OFF m n → Func (Space n) (Space m)

  Simplex : ℕ → Set a
  Simplex n = Space n .Setoid.Carrier

  _≈_ : Rel (Simplex n) ℓ
  _≈_ = Space _ .Setoid._≈_

  fmap : OFF m n → Simplex n → Simplex m
  fmap f = morph f .Func.f

  field
    fmap-id : (s : Simplex n) → fmap id s ≈ s
    fmap-∘ : ∀ (f : OFF m n) (g : OFF l m) s → fmap (f ∘ g) s ≈ fmap g (fmap f s)

  isEquivalence : IsEquivalence (_≈_ {n})
  isEquivalence = Space _ .Setoid.isEquivalence

  cong : (f : OFF m n) → fmap f Preserves _≈_ ⟶ _≈_
  cong f = morph f .Func.cong

homPresheaf : ℕ → Presheaf 0ℓ 0ℓ
homPresheaf m = record
  { Space = λ n → setoid (OFF n m)
  ; morph = λ f → record
    { f = _∘ f
    ; cong = icong
    }
  ; fmap-id = ∘-identityʳ
  ; fmap-∘ = λ f g s → ∘-assoc s f g ⋆
  }
