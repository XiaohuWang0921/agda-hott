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
open import Relation.Core

Presheaf : ∀ a r → Set (ℓsuc (a ⊔ r))
Presheaf a r = Functor (Op FinCat) (Setoid.category {a} {r})

module Presheaf {a r} (P : Presheaf a r) where

  Space : ℕ → Setoid a r
  Space = P <$>_

  Tope : ℕ → Set a
  Tope n = Setoid.Carrier (Space n)

  _≃_ : ∀ {n} → Rel (Tope n) r
  _≃_ {n} = Setoid._≈_ (Space n)

  map : ∀ {m n} → (Fin m → Fin n) → (Space n ⟶ Space m)
  map = P -$-_

  map-cong : ∀ {m n} {f g : Fin m → Fin n} → f ≈ g → map f ≈ map g
  map-cong = P #$#_

  proj : ∀ {m n} → (Fin m → Fin n) → (Tope n → Tope m)
  proj f = map f ⟨$⟩_

  open Functor P public renaming
    ( mor-id to map-id
    ; mor-∘  to map-∘
    )

  Component : Setoid a r
  Component = Space 0

  Point : Setoid a r
  Point = Space 1

  Path : Setoid a r
  Path = Space 2
