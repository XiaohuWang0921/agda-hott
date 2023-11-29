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
open import Universe.Setoid hiding (_∘_)
open import Data.Nat.Properties using (≤?-functorˡ; <?-functorˡ)
open import Relation.Equality.Base
open import Data.Unit.Core
open import Relation.Equality.Base
open import Universe.Set using (_≗_)

record ASC (n : ℕ) : Set where
  field
    revMap : Functor (⊆-Cat n) (Op ≤-Cat)

  has : Subset n → Bool
  has = Functor.obj revMap

  Has : Subset n → Set
  Has s = T (has s)

  has-⊆ : ∀ {s t} → s ⊆ t → has t ≤ has s
  has-⊆ = _⟶_.func (Functor.hom revMap)

  has-cong : ∀ {s t} → s ≗ t → has s ≡ has t
  has-cong s≗t = ≤-antisym (has-⊆ (λ i → ≡⇒≤ (sym (s≗t i))))
                           (has-⊆ (λ i → ≡⇒≤ (s≗t i)))

  Has-⊆ : ∀ {s t} → s ⊆ t → Has t → Has s
  Has-⊆ s⊆t = T-≤ (has-⊆ s⊆t)

  field
    hasAllPoints : ∀ i → Has (singleton i)

points : ∀ n → ASC n
points n = record
  { revMap = ≤?-functorˡ 1 ∘ ∣∣-functor
  ; hasAllPoints = λ i → resp (λ m → T (m ≤? 1)) (sym (∣∣∘singleton i)) tt
  }

all : ∀ n → ASC n
all n = record
  { revMap = Const true
  ; hasAllPoints = λ _ → tt
  }

cycle : ∀ n → ASC (2 + n)
cycle n = record
  { revMap = ≤?-functorˡ (1 + n) ∘ ∣∣-functor
  ; hasAllPoints = λ i → resp (λ m → T (m ≤? 1 + n)) (sym (∣∣∘singleton i)) tt
  }

preimages : ∀ {m n} → (Fin m → Fin n) → ASC n → ASC m
preimages f asc = record
  { revMap = revMap ∘ image-functor f
  ; hasAllPoints = λ i → Has-⊆ (≗⇒⊆ (image-singleton f i)) (hasAllPoints (f i))
  }
  where open ASC asc
