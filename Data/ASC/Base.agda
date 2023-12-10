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
open import Relation.Equality.Base
open import Universe.Set using (_≗_)
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

  has-cong : ∀ {s t} → s ≗ t → has s ≡ has t
  has-cong s≗t = ≤-antisym (has-⊆ (λ i → ≡⇒≤ (sym (s≗t i))))
                           (has-⊆ (λ i → ≡⇒≤ (s≗t i)))

  Has-⊆ : ∀ {s t} → s ⊆ t → Has t → Has s
  Has-⊆ s⊆t = T-≤ (has-⊆ s⊆t)

  field
    hasAllPoints : ∀ i → Has (singleton i)

open ASC public

points : ∀ n → ASC n
points _ .revMap = ≤?-functorˡ 1 ∘ Opposite ∣∣-functor
points _ .hasAllPoints i = resp (λ m → T (m ≤? 1)) (sym (∣∣∘singleton i)) tt

all : ∀ n → ASC n
all _ .revMap = Const <$> true
all _ .hasAllPoints _ = tt

cycle : ∀ n → ASC (2 + n)
cycle n .revMap = ≤?-functorˡ (1 + n) ∘ Opposite ∣∣-functor
cycle n .hasAllPoints i = resp (λ m → T (m ≤? 1 + n)) (sym (∣∣∘singleton i)) tt

preimages : ∀ {m n} → (Fin m → Fin n) → ASC n → ASC m
preimages f asc .revMap = asc .revMap ∘ Opposite (image-functor f)
preimages f asc .hasAllPoints i = Has-⊆ asc (≗⇒⊆ (image-singleton f i)) (asc .hasAllPoints (f i))

add : ∀ {n} → ASC n → Subset n → ASC n
add asc s .revMap = ∨-functor ∘ asc .revMap ˢ ⊆?-functorˡ s
add asc _ .hasAllPoints i = T-≤ a≤a∨b (asc .hasAllPoints i)

addAll : ∀ {m n} → Vec (Subset n) m → ASC n → ASC n
addAll = foldl add

infix 4 _⊑_
_⊑_ : ∀ {n} → Rel (ASC n) 0ℓ
a ⊑ b = ∀ s → has a s ≤ has b s

infix 4 _≅_
_≅_ : ∀ {n} → Rel (ASC n) 0ℓ
a ≅ b = has a ≗ has b
