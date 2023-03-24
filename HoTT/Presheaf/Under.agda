{-# OPTIONS --without-K --safe #-}

open import HoTT.Presheaf

module HoTT.Presheaf.Under {a ℓ} (P : Presheaf a ℓ) where

open import Level
open import Data.Nat.Base hiding (_⊔_)
open import HoTT.OFF
open import HoTT.OFF.Properties
open import Relation.Binary.Core
open import Relation.Binary.Bundles
open import Relation.Binary.Structures
open import Function.Base hiding (id; _∘_)
open import Function.Bundles
open import Relation.Binary.PropositionalEquality.Core as P hiding (refl; sym; trans; cong)
import Relation.Binary.Reasoning.Setoid

open Presheaf P

private
  variable
    l m n : ℕ
    tip : Simplex l

record UnderSimplex (tip : Simplex l) (n : ℕ) : Set (a ⊔ ℓ) where
  field
    solid : Simplex (l + n)
    fromTip : fmap (first l) solid ≈ tip

open UnderSimplex

infix 4 _≈↓_
_≈↓_ : Rel (UnderSimplex tip n) ℓ
_≈↓_ = _≈_ on solid

≈↓-isEquivalence : IsEquivalence (_≈↓_ {l} {tip} {n})
≈↓-isEquivalence {l} {_} {n} = record
  { refl = refl
  ; sym = sym
  ; trans = trans
  }
  where open IsEquivalence (isEquivalence {l + n})

UnderSpace : Simplex l → ℕ → Setoid (a ⊔ ℓ) ℓ
UnderSpace tip n = record
  { Carrier = UnderSimplex tip n
  ; _≈_ = _≈↓_
  ; isEquivalence = ≈↓-isEquivalence
  }

morph↓ : OFF m n → Func (UnderSpace tip n) (UnderSpace tip m)
morph↓ {m} {n} {l} {tip} f .Func.f u = record
  { solid = fmap (shiftˡ l f) (u .solid)
  ; fromTip = begin
    fmap (first l) (fmap (shiftˡ l f) (u .solid)) ≡⟨⟩
    fmap (first l) (fmap (stack id f) (u .solid)) ≈˘⟨ fmap-∘ _ _ _ ⟩
    fmap (stack id f ∘ first l) (u .solid) ≈˘⟨ reflexive (P.cong (flip fmap _) (first-∘ id f)) ⟩
    fmap (first l ∘ id) (u .solid) ≈⟨ reflexive (P.cong (flip fmap _) (∘-identityʳ (first l))) ⟩
    fmap (first l) (u .solid) ≈⟨ u .fromTip ⟩
    tip ∎
  }
  where open Relation.Binary.Reasoning.Setoid (Space l)
        open IsEquivalence (isEquivalence {l})
morph↓ {m} {n} {l} {tip} f .Func.cong {u} {v} = cong _

under : Simplex l → Presheaf (a ⊔ ℓ) ℓ
under tip .Space = UnderSpace tip
under tip .morph = morph↓
under {l} tip .fmap-id {n} u = begin
  morph↓ id .Func.f u .solid ≡⟨⟩
  fmap (shiftˡ l id) (u .solid) ≡⟨⟩
  fmap (stack {l} {l} {n} id id) (u .solid) ≈⟨ reflexive (P.cong (flip fmap _) (stack-id {l} {n})) ⟩
  fmap id (u .solid) ≈⟨ fmap-id _ ⟩
  u .solid ∎
  where open Relation.Binary.Reasoning.Setoid (Space (l + n))
        open IsEquivalence (isEquivalence {l + n})
under {l} tip .fmap-∘ {l = k} f g u = begin
  morph↓ (f ∘ g) .Func.f u .solid ≡⟨⟩
  fmap (shiftˡ l (f ∘ g)) (u .solid) ≈⟨ reflexive (P.cong (flip fmap _) (shiftˡ-∘ l f g)) ⟩
  fmap (shiftˡ l f ∘ shiftˡ l g) (u .solid) ≈⟨ fmap-∘ (shiftˡ l f) _ _ ⟩
  fmap (shiftˡ l g) (fmap (shiftˡ l f) (u .solid)) ≡⟨⟩
  morph↓ g .Func.f (morph↓ f .Func.f u) .solid ∎
  where open Relation.Binary.Reasoning.Setoid (Space (l + k))
        open IsEquivalence (isEquivalence {l + k})

base : Func (UnderSpace tip n) (Space n)
base {n = n} .Func.f u = fmap (shiftʳ n empty) (u .solid)
base {n = n} .Func.cong {u} {v} u≈v = cong _ u≈v
