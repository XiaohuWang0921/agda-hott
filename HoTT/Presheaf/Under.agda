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
open import Function.Base as Fun hiding (id; _∘_)
open import HoTT.Setoid.Morphism as Mor hiding (id; _∘_)
open import Relation.Binary.PropositionalEquality.Core as P hiding (refl; sym; trans; cong)
import Relation.Binary.Reasoning.Setoid

open Presheaf P

private
  variable
    l m n : ℕ

record UnderSimplex (tip : Simplex l) (n : ℕ) : Set (a ⊔ ℓ) where
  field
    solid : Simplex (l + n)
    fromTip : fmap (first l) solid ≈ tip

open UnderSimplex public

infix 4 _≈↓_
_≈↓_ : {tip : Simplex l} → Rel (UnderSimplex tip n) ℓ
_≈↓_ = _≈_ on solid

≈↓-isEquivalence : {tip : Simplex l} → IsEquivalence (_≈↓_ {l} {n} {tip})
≈↓-isEquivalence {l} {n} = record
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

sink : (F : Space (l + m) ⟶ Space (l + n)) → morph (first l) Mor.∘ F ⊖ morph (first l) → {tip : Simplex l} → UnderSpace tip m ⟶ UnderSpace tip n
sink {l = l} F F-first = record
  { _⟨$⟩_ = λ u → record
    { solid = F ⟨$⟩ u .solid
    ; fromTip = trans F-first (u .fromTip)
    }
  ; cong = F .cong
  }
  where open Setoid (Space l)

base : {tip : Simplex l} → UnderSpace tip n ⟶ Space (l + n)
base = record
  { _⟨$⟩_ = solid
  ; cong = Fun.id
  }

morph↓ : {tip : Simplex l} → OFF m n → UnderSpace tip n ⟶ UnderSpace tip m
morph↓ {l} {m} {n} f = sink (morph (shiftˡ l f)) (begin
  morph (first l) Mor.∘ morph (shiftˡ l f) ≈˘⟨ morph-∘ _ _ ⟩
  morph (shiftˡ l f ∘ first l) ≡⟨⟩
  morph (stack id f ∘ first l) ≈˘⟨ reflexive (P.cong morph (first-∘ id f)) ⟩
  morph (first l ∘ id) ≈⟨ reflexive (P.cong morph (∘-identityʳ _)) ⟩
  morph (first l) ∎)
  where open Relation.Binary.Reasoning.Setoid (Space (l + n) ⇨ Space l)
        open IsEquivalence (⊖-isEquivalence {From = Space (l + n)} {To = Space l})
{-
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
-}
