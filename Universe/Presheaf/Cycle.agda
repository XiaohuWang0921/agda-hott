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
open import Relation.Equality.Base hiding (setoid)
open import Category.Functor hiding (_∘_)
open import Data.Product.Base hiding (map)
open import Universe.Set hiding (_⇒_)
-- open import Universe.Setoid.Categorical
-- open import Universe.Set.Categorical

record Cycle {a r} (P : Presheaf a r) (n : ℕ) : Set (a ⊔ r) where
  open Presheaf P
  field
    face : Fin (2 + n) → Tope (1 + n)
    compatible : ∀ i j → proj (punchIn i) (face j) ≃ proj (punchIn (pinch i j)) (face (punchIn j i))

open Cycle public

setoid : ∀ {a r} (P : Presheaf a r) (n : ℕ) → Setoid (a ⊔ r) r
setoid P n = record
  { Carrier = Cycle P n
  ; _≈_ = λ c d → ∀ i → face c i ≃ face d i
  ; refl = λ _ → Setoid.refl (Space (suc n))
  ; trig = λ d≈c d≈e i → Setoid.trig (Space (suc n)) (d≈c i) (d≈e i)
  }
  where open Presheaf P

map : ∀ {a r} {P Q : Presheaf a r} n →
        (P ⇛ Q) ⟶ setoid P n ⇒ setoid Q n
map {a} {r} {P} {Q} n = record
  { func = λ η → record
    { func = λ c → record
      { face = λ i → (η <&> suc n) ⟨$⟩ face c i
      ; compatible = λ i j →
        (Q -$- punchIn i) ⟨$⟩ ((η <&> suc n) ⟨$⟩ face c j) ≈˘⟨ isNatural η _ _ ⟩
        (η <&> n) ⟨$⟩ ((P -$- punchIn i) ⟨$⟩ face c j) ≈⟨ (η <&> n) ~$~ compatible c i j ⟩
        (η <&> n) ⟨$⟩ ((P -$- punchIn (pinch i j)) ⟨$⟩ face c (punchIn j i)) ≈⟨ isNatural η _ _ ⟩
        (Q -$- punchIn (pinch i j)) ⟨$⟩ ((η <&> suc n) ⟨$⟩ face c (punchIn j i)) ∎
      }
    ; cong = λ c≈d i → (η <&> suc n) ~$~ c≈d i
    }
  ; cong = λ η≈ε c i → η≈ε (suc n) (face c i)
  }
  where
    open Relation.Reasoning (Presheaf._≃_ Q)
    open Equiv (Setoid.refl (Presheaf.Space Q n))
               (Setoid.trig (Presheaf.Space Q n))

boundary : ∀ {a r} (P : Presheaf a r) n (open Presheaf P) → Space (2 + n) ⟶ setoid P n
boundary P n = record
  { func = λ t → record
    { face = λ i → m (punchIn i) ⟨$⟩ t
    ; compatible = λ i j →
      m (punchIn i) ⟨$⟩ (m (punchIn j) ⟨$⟩ t) ≈˘⟨ map-∘ _ _ _ ⟩
      m (punchIn j ∘ punchIn i) ⟨$⟩ t ≈⟨ map-cong (punchIn∘punchIn j i) t ⟩
      m (punchIn (punchIn j i) ∘ punchIn (pinch i j)) ⟨$⟩ t ≈⟨ map-∘ _ _ _ ⟩
      m (punchIn (pinch i j)) ⟨$⟩ (m (punchIn (punchIn j i)) ⟨$⟩ t) ∎
    }
  ; cong = λ t≃u i → m (punchIn i) ~$~ t≃u
  }
  where
    open Presheaf P renaming (map to m)
    open Relation.Reasoning _≃_
    open Equiv (Setoid.refl (Space n))
               (Setoid.trig (Space n))
