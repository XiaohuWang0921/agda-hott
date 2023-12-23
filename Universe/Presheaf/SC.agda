{-# OPTIONS --without-K --safe #-}

open import Universe.Presheaf.Base

module Universe.Presheaf.SC {a r} (P : Presheaf a r) where
-- SC stands for Simplicial Complex
open import Data.ASC.Base
open import Data.ASC.Properties
open import Data.Fin.Base
open import Data.Nat.Base
open import Data.Fin.Subset.Base
open import Data.Fin.Subset.Properties
open import Level
open import Universe.Presheaf.Fillable

module P = Presheaf P

record SC {n} (asc : ASC n) : Set (a ⊔ r) where
  field
    for : ∀ {s} → s ∈ asc → Tope P ∣ s ∣
    compat : ∀ {s t} t∈asc (s⊆t : s ⊆ t) → for (Has-⊆ asc s⊆t t∈asc) P.≃ P.proj (embed s⊆t) (for t∈asc)

module Fill (fillable : ∀ n → Fillable P n) where
