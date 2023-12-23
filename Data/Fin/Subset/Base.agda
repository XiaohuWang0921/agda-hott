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
open import Data.Product.Base using (_,_)

private
  variable
    m n : ℕ

Subset : ℕ → Set
Subset = Vec Bool

infix 4 _⊆_ _⊆?_
_⊆_ : ∀ {n} → Rel (Subset n) 0ℓ
_⊆_ = Pointwise _≤_

_⊆?_ : ∀ {n} → Subset n → Subset n → Bool
_⊆?_ [] [] = true
_⊆?_ (b ∷ s) (c ∷ t) = (b ≤? c) ∧ (s ⊆? t)

∣_∣ : ∀ {n} → Subset n → ℕ
∣ [] ∣ = 0
∣ false ∷ s ∣ = ∣ s ∣
∣ true ∷ s ∣ = suc ∣ s ∣

full : ∀ n → Subset n
full n = repeat n true

empty : ∀ n → Subset n
empty n = repeat n false

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
embed [] ()
embed (b≤b {false} ∷ s⊆t) = embed s⊆t
embed (b≤b {true} ∷ s⊆t) = id ∣ embed s⊆t
embed (f≤t ∷ s⊆t) = suc ∘ embed s⊆t

single : ∀ {n} → Fin n → Subset n
single zero = true ∷ empty _
single (suc i) = false ∷ single i

antisingle : ∀ {n} → Fin n → Subset n
antisingle zero = false ∷ full _
antisingle (suc i) = true ∷ antisingle i

preimage : ∀ {m n} → (Fin m → Fin n) → Subset n → Subset m
preimage f s = tabulate (lookup s ∘ f)

image : ∀ {m n} → (Fin m → Fin n) → Subset m → Subset n
image _ [] = empty _
image f (b ∷ s) = repeat _ b ∩ single (f zero) ∪ image (f ∘ suc) s

subSub : (s : Subset n) → Subset ∣ s ∣ → Subset n
subSub [] _ = []
subSub (false ∷ s) t = false ∷ subSub s t
subSub (true ∷ s) (b ∷ t) = b ∷ subSub s t

except : (s : Subset n) → Fin ∣ s ∣ → Subset n
except s i = subSub s (antisingle i)
