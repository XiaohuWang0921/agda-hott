{-# OPTIONS --without-K --safe #-}

module Universe.Presheaf.Base where

open import Level
open import Category.Base
open import Universe.Set.Categorical
open import Universe.Setoid.Categorical
open import Universe.Setoid
open import Category.Functor
open import Data.Fin.Base
open import Data.Nat.Base
open import Category.Natural renaming (_⇉_ to _⇇_; _⇛_ to _⇚_) public
open import Relation.Core

-- I have decided to take the opposite category of setoids
-- because we will compose presheaves more often with functors
-- on FinCat and there seem to be some weird performance issues
-- in agda with Category.Functor.Opposite
Presheaf : ∀ a r → Set (ℓsuc (a ⊔ r))
Presheaf a r = Functor FinCat (Op (SetoidCat a r))

infixr 0 _⇉_
_⇉_ : ∀ {a r} → Rel (Presheaf a r) (a ⊔ r)
P ⇉ Q = Q ⇇ P

infixr 0 _⇛_
_⇛_ : ∀ {a r} → Presheaf a r → Presheaf a r → Setoid (a ⊔ r) (a ⊔ r)
P ⇛ Q = Q ⇚ P

module Presheaf {a r} (P : Presheaf a r) where

  Space : ℕ → Setoid a r
  Space = P <$>_

  Tope : ℕ → Set a
  Tope n = Carrier (Space n)

  _≃_ : ∀ {n} → Rel (Tope n) r
  _≃_ {n} = _≈_ (Space n)

  map : ∀ {m n} → (Fin m → Fin n) → (Space n ⟶ Space m)
  map = P -$-_

  module F = Category FinCat
  module S = Category (SetoidCat a r)

  map-cong : ∀ {m n} {f g : Fin m → Fin n} → f F.≈ g → map f S.≈ map g
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

open Presheaf public
