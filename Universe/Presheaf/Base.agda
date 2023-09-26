{-# OPTIONS --without-K --safe #-}

module Universe.Presheaf.Base where

open import Level
open import Category
open import Universe.Set.Categorical as Set
open import Universe.Setoid.Categorical as Setoid
open import Universe.Setoid
open import Category.Functor
open import Data.Fin.Base
open import Data.Nat.Base
open import Category.Natural public

Presheaf : ∀ a r → Set (ℓsuc (a ⊔ r))
Presheaf a r = Functor (FullSub Set.category Fin) (Op (Setoid.category {a} {r}))

module Presheaf {a r} (P : Presheaf a r) where

  Space : ℕ → Setoid a r
  Space = P <$>_

  proj : ∀ {m n} → (Fin m → Fin n) → (Space n ⟶ Space m)
  proj = P -$-_

  proj-cong : ∀ {m n} {f g : Fin m → Fin n} → f ≈ g → proj f ≈ proj g
  proj-cong = P #$#_

  open Functor P public renaming
    ( mor-id to proj-id
    ; mor-∘  to proj-∘
    )
