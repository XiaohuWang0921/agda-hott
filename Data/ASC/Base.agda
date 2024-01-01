{-# OPTIONS --without-K --safe #-}

module Data.ASC.Base where
-- ASC stands for abstract simplicial complex
open import Data.Bool.Base hiding (_≤?_)
open import Data.Fin.Base
open import Data.Fin.Subset.Base
open import Data.Fin.Subset.Properties
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; _+_; _≤?_)
open import Data.Bool.Properties hiding (≤?-functorˡ)
open import Category.Base
open import Category.Functor
open import Universe.Setoid using (func)
open import Data.Nat.Properties using (≤?-functorˡ; <?-functorˡ)
open import Relation.Equality.Base
open import Data.Unit.Core
open import Universe.Set using (_≗_; flip)
open import Category.FunCat
open import Data.Vec.Base
open import Relation.Core
open import Level

record ASC (n : ℕ) : Set where
  field
    revMap : Functor (Op (⊆-Cat n)) ≤-Cat

  has : Subset n → Bool
  has = Functor.obj revMap

  Has : Subset n → Set
  Has s = T (has s)

  has-⊆ : ∀ {s t} → s ⊆ t → has t ≤ has s
  has-⊆ = Functor.hom revMap .func

  Has-⊆ : ∀ {s t} → s ⊆ t → Has t → Has s
  Has-⊆ s⊆t = T-≤ (has-⊆ s⊆t)

  field
    hasAllPoints : ∀ i → Has (single i)

open ASC public

infix 0 _∈_
_∈_ : ∀ {n} → Subset n → ASC n → Set
_∈_ = flip Has

points : ∀ n → ASC n
points _ .revMap = ≤?-functorˡ 1 ∘ Opposite ∣∣-functor
points _ .hasAllPoints i = resp (λ m → T (m ≤? 1)) (sym (∣∣∘single i)) tt

all : ∀ n → ASC n
all _ .revMap = Const <$> true
all _ .hasAllPoints _ = tt

cycle : ∀ n → ASC (2 + n)
cycle n .revMap = ≤?-functorˡ (1 + n) ∘ Opposite ∣∣-functor
cycle n .hasAllPoints i = resp (λ m → T (m ≤? 1 + n)) (sym (∣∣∘single i)) tt

preimages : ∀ {m n} → (Fin m → Fin n) → ASC n → ASC m
preimages f asc .revMap = asc .revMap ∘ Opposite (image-functor f)
preimages f asc .hasAllPoints i = Has-⊆ asc (≡⇒⊆ (image-single f i)) (asc .hasAllPoints (f i))

add : ∀ {n} → Subset n → ASC n → ASC n
add s asc .revMap = ∨-functor ∘ asc .revMap ˢ ⊆?-functorˡ s
add _ asc .hasAllPoints i = T-≤ a≤a∨b (asc .hasAllPoints i)

addAll : ∀ {m n} → (Fin m → Subset n) → ASC n → ASC n
addAll {zero} _ asc = asc
addAll {suc _} ss asc = addAll (λ i → ss (suc i)) (add (ss zero) asc)

infix 4 _⊑_
_⊑_ : ∀ {n} → Rel (ASC n) 0ℓ
a ⊑ b = ∀ s → has a s ≤ has b s

infix 4 _≅_
_≅_ : ∀ {n} → Rel (ASC n) 0ℓ
a ≅ b = has a ≗ has b
