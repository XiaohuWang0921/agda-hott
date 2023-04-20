{-# OPTIONS --without-K --safe #-}

open import HoTT.Presheaf

module HoTT.Presheaf.Cycle {a ℓ} (P : Presheaf a ℓ) where

open import Data.Nat.Base hiding (_⊔_)
open import Data.Fin.Base hiding (_+_; lift)
open import HoTT.OFF
open import HoTT.OFF.Properties
open import Data.Product
open import Data.Unit.Base
open import Level
open import Relation.Binary.Core
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality.Core as P
open import Function.Base hiding (id; _∘_)

open Presheaf P

private
  variable
    n : ℕ

module _ (faces : Fin (2 + n) → Simplex (1 + n)) where

  common : Fin (2 + n) → Fin (1 + n) → Simplex n
  common i j = fmap (skip j) (faces i)

  Compatible1+ : Set ℓ
  Compatible1+ =
    ∀ i (j : Fin′ i) →
    let j = inject! j
        j′ , i′ = switch i j
    in common i j ≈ common j′ i′

Compatible : (Fin (1 + n) → Simplex n) → Set ℓ
Compatible {zero} _ = Lift _ ⊤
Compatible {suc _} = Compatible1+

record Cycle (n : ℕ) : Set (a ⊔ ℓ) where
  field
    faces : Fin (1 + n) → Simplex n
    compatible : Compatible faces

open Cycle public

infix 4 _≈ᶜ_
_≈ᶜ_ : Rel (Cycle n) ℓ
c ≈ᶜ d = ∀ i → c .faces i ≈ d .faces i

boundary : Simplex (1 + n) → Cycle n
boundary s .faces i = fmap (skip i) s
boundary {zero} s .compatible = lift tt
boundary {suc n} s .compatible i j =
  let j = inject! j
      j′ , i′ = switch i j
  in begin
     common (boundary s .faces) i j ≡⟨⟩
     fmap (skip j) (boundary s .faces i) ≡⟨⟩
     fmap (skip j) (fmap (skip i) s) ≈˘⟨ morph-∘ (skip i) (skip j) ⟩
     fmap (skip i ∘ skip j) s ≈⟨ reflexive (P.cong (flip fmap s) (skip-switch i j)) ⟩
     fmap (skip j′ ∘ skip i′) s ≈⟨ morph-∘ (skip j′) (skip i′) ⟩
     fmap (skip i′) (fmap (skip j′) s) ≡⟨⟩
     fmap (skip i′) (boundary s .faces j′) ≡⟨⟩
     common (boundary s .faces) j′ i′ ∎
  where open import Relation.Binary.Reasoning.Setoid (Space n)
        open IsEquivalence (isEquivalence {n})
