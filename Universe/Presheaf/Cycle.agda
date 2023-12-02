{-# OPTIONS --without-K --safe #-}

module Universe.Presheaf.Cycle where

open import Level
open import Universe.Presheaf.Base hiding (_∘_)
open import Data.Nat.Base
open import Data.Fin.Base
open import Data.Fin.Properties
open import Universe.Setoid hiding (_∘_)
open import Data.Unit.Core
open import Relation.Core
open import Category.Base
import Relation.Reasoning
open import Relation.Equality.Base using (_≡_)
open import Category.Functor hiding (_∘_)
open import Data.Product.Base hiding (map)
open import Universe.Set hiding (_⇒_)
-- open import Universe.Setoid.Categorical
-- open import Universe.Set.Categorical

record Cycle {a r} (P : Presheaf a r) (n : ℕ) : Set (a ⊔ r) where
  module P = Presheaf P
  field
    face : Fin (2 + n) → P.Tope (1 + n)
    compatible : ∀ i j → P.proj (punchIn i) (face j) P.≃ P.proj (punchIn (pinch i j)) (face (punchIn j i))

open Cycle public hiding (module P)

CycStd : ∀ {a r} (P : Presheaf a r) (n : ℕ) → Setoid (a ⊔ r) r
CycStd P n .Carrier = Cycle P n
CycStd P _ ._≈_ c d = ∀ i → face c i P.≃ face d i
  where module P = Presheaf P
CycStd P n .refl _ = Space P (suc n) .refl
CycStd P n .trig d≈c d≈e i = Space P (suc n) .trig (d≈c i) (d≈e i)

mapCyc : ∀ {a r} {P Q : Presheaf a r} n →
        (P ⇛ Q) ⟶ CycStd P n ⇒ CycStd Q n
mapCyc n .func η .func c .face i = (η <&> suc n) ⟨$⟩ c .face i
mapCyc {a} {r} {P} {Q} n .func η .func c .compatible i j =
  (Q -$- punchIn i) ⟨$⟩ ((η <&> suc n) ⟨$⟩ face c j) ≈⟨ η .isNatural _ _ ⟩
  (η <&> n) ⟨$⟩ ((P -$- punchIn i) ⟨$⟩ face c j) ≈⟨ (η <&> n) ~$~ c .compatible i j ⟩
  (η <&> n) ⟨$⟩ ((P -$- punchIn (pinch i j)) ⟨$⟩ face c (punchIn j i)) ≈˘⟨ η .isNatural _ _ ⟩
  (Q -$- punchIn (pinch i j)) ⟨$⟩ ((η <&> suc n) ⟨$⟩ face c (punchIn j i)) ∎
  where open Relation.Reasoning (_≃_ Q)
        open Equiv (Space Q n .refl) (Space Q n .trig)
mapCyc n .func η .cong c≈d i = (η <&> suc n) ~$~ c≈d i
mapCyc n .cong η≈ε c i = η≈ε (suc n) (face c i)

boundary : ∀ {a r} (P : Presheaf a r) n → Space P (2 + n) ⟶ CycStd P n
boundary P n .func t .face i = map P (punchIn i) ⟨$⟩ t
boundary P n .func t .compatible i j =
  map P (punchIn i) ⟨$⟩ (map P (punchIn j) ⟨$⟩ t) ≈˘⟨ map-∘ P _ _ _ ⟩
  map P (punchIn j ∘ punchIn i) ⟨$⟩ t ≈⟨ map-cong P (punchIn∘punchIn j i) t ⟩
  map P (punchIn (punchIn j i) ∘ punchIn (pinch i j)) ⟨$⟩ t ≈⟨ map-∘ P _ _ _ ⟩
  map P (punchIn (pinch i j)) ⟨$⟩ (map P (punchIn (punchIn j i)) ⟨$⟩ t) ∎
  where open Relation.Reasoning (_≃_ P)
        open Equiv (Space P n .refl) (Space P n .trig)
boundary P n .cong t≃u i = map P (punchIn i) ~$~ t≃u
