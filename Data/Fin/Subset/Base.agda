{-# OPTIONS --without-K --safe #-}

module Data.Fin.Subset.Base where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base
open import Data.Vec.Base
open import Data.Bool.Base hiding (_≟_)
open import Relation.Core
open import Level
open import Universe.Set
open import Algebra.Core

private
  variable
    m n : ℕ

Subset : ℕ → Set
Subset = Vec Bool

infix 4 _⊆_ _⊆?_
_⊆_ : ∀ {n} → Rel (Subset n) 0ℓ
_⊆_ = Pointwise _≤_

_⊆?_ : ∀ {n} → Subset n → Subset n → Bool
_⊆?_ {zero} _ _ = true
_⊆?_ {suc _} s t = (head s ≤? head t) ∧ (tail s ⊆? tail t)

∣_∣ : ∀ {n} → Subset n → ℕ
∣_∣ {zero} _ = 0
∣_∣ {suc n} s = (if s zero then suc else id) ∣ tail s ∣

full : ∀ n → Subset n
full _ = const true

empty : ∀ n → Subset n
empty _ = const false

∁ : Op₁ (Subset n)
∁ = map not

infixr 7 _∩_
infixr 6 _∪_

_∩_ : Op₂ (Subset n)
_∩_ = zipWith _∧_

_∪_ : Op₂ (Subset n)
_∪_ = zipWith _∨_

infixr 0 _↝_
_↝_ : ∀ {m n} → Subset m → Subset n → Set
s ↝ t = Fin ∣ s ∣ → Fin ∣ t ∣

embed : ∀ {n} {s t : Subset n} → s ⊆ t → s ↝ t
embed {zero} _ ()
embed {suc n} {s} {t} s⊆t with s zero | t zero | s⊆t zero
... | false | false | _ = embed (λ i → s⊆t (suc i))
... | false | true | _ = suc ∘ embed (λ i → s⊆t (suc i))
... | true | true | _ = id ∣ embed (λ i → s⊆t (suc i))

singleton : ∀ {n} → Fin n → Subset n
singleton = _≟_

preimage : ∀ {m n} → (Fin m → Fin n) → Subset n → Subset m
preimage = flip _∘_

image : ∀ {m n} → (Fin m → Fin n) → Subset m → Subset n
image {zero} = const (const (const false))
image {suc _} f s = singleton (f zero) ∪ image (f ∘ suc) (s ∘ suc)
