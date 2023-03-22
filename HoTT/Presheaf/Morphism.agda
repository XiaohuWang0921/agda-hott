{-# OPTIONS --without-K --safe #-}

module HoTT.Presheaf.Morphism where

open import Level
open import HoTT.Presheaf
open import HoTT.OFF hiding (id; _∘_)
open import Data.Nat.Base hiding (_⊔_)
open import Function.Bundles
open import Relation.Binary.Core
open import Relation.Binary.Structures
open import Function.Base as Fun hiding (id; _∘_)

private
  variable
    a b c r s t : Level
    m n : ℕ

record _⇉_ (From : Presheaf a r) (To : Presheaf b s) : Set (a ⊔ b ⊔ r ⊔ s) where
  open Presheaf From using () renaming (Space to S; _≈_ to _≈ˢ_; fmap to ϕ)
  open Presheaf To using () renaming (Space to T; _≈_ to _≈ᵗ_ ; fmap to ψ)

  field
    transform : Func (S n) (T n)

  apply : ∀ {n} → _
  apply {n} = transform {n} .Func.f

  field
    isNatural : ∀ (f : OFF m n) s → apply (ϕ f s) ≈ᵗ ψ f (apply s)

  cong : apply {n} Preserves _≈ˢ_ ⟶ _≈ᵗ_
  cong = transform .Func.cong

id : {A : Presheaf a r} → A ⇉ A
id ._⇉_.transform = record
  { f = Fun.id
  ; cong = Fun.id
  }
id {A = A} ._⇉_.isNatural _ _ = refl
  where open Presheaf A
        open IsEquivalence isEquivalence

infixr 9 _∘_
_∘_ : {A : Presheaf a r} {B : Presheaf b s} {C : Presheaf c t} →
      B ⇉ C → A ⇉ B → A ⇉ C
(F ∘ G) ._⇉_.transform = record
  { f = ε ∘′ η
  ; cong = ε-cong ∘′ η-cong
  }
  where open _⇉_ F renaming (apply to ε; cong to ε-cong)
        open _⇉_ G renaming (apply to η; cong to η-cong)
_∘_ {A = A} {B = B} {C = C} F G ._⇉_.isNatural {m} h p = begin
  ε (η (φ h p)) ≈⟨ ε-cong (η-natural h p) ⟩
  ε (ψ h (η p)) ≈⟨ ε-natural h (η p) ⟩
  χ h (ε (η p)) ∎
  where open Presheaf A using ()renaming (fmap to φ)
        open Presheaf B using () renaming (fmap to ψ)
        open Presheaf C renaming (fmap to χ)
        open _⇉_ F renaming (apply to ε; cong to ε-cong; isNatural to ε-natural)
        open _⇉_ G renaming (apply to η; isNatural to η-natural)
        open import Relation.Binary.Reasoning.Setoid (Space m)

infix 4 _⊜_
_⊜_ : {A : Presheaf a r} {B : Presheaf b s} → Rel (A ⇉ B) (a ⊔ s)
_⊜_ {B = B} F G = ∀ {n} s → ε {n} s ≈ η s
  where open Presheaf B using (_≈_)
        open _⇉_ F renaming (apply to ε)
        open _⇉_ G renaming (apply to η)
