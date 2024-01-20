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
open import Data.Product.Base

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
    hasAllPoints : ∀ s → Has (1 , s)

open ASC public

infix 0 _∈_ _∉_
_∈_ : ∀ {k l} → CSet k l → ASC k → Set
s ∈ asc = Has asc (_ , s)

_∉_ : ∀ {k l} → CSet k l → ASC k → Set
s ∉ asc = F (has asc (_ , s))

points : ∀ n → ASC n
points _ .revMap = ≤?-functorˡ 1 ∘ Opposite proj₁-functor
points _ .hasAllPoints _ = tt

all : ∀ n → ASC n
all _ .revMap = Const <$> true
all _ .hasAllPoints _ = tt

cycle : ∀ n → ASC (2 + n)
cycle n .revMap = ≤?-functorˡ (1 + n) ∘ Opposite proj₁-functor
cycle n .hasAllPoints _ = tt

preimages : ∀ {m n} → (Fin m → Fin n) → ASC n → ASC m
preimages f asc .revMap = asc .revMap ∘ Opposite (image-functor f)
preimages f asc .hasAllPoints s rewrite l≡1 s refl .proj₂ rewrite image-single f (l≡1 s refl .proj₁) = asc .hasAllPoints _

add : ∀ {k l} → CSet k l → ASC k → ASC k
add s asc .revMap = ∨-functor ∘ asc .revMap ˢ ⊆?-functorˡ (_ , s)
add _ asc .hasAllPoints s = T-≤ a≤a∨b (asc .hasAllPoints s)

addAll : ∀ {m k l} → (Fin m → CSet k l) → ASC k → ASC k
addAll {zero} _ asc = asc
addAll {suc _} ss asc = addAll (λ i → ss (suc i)) (add (ss zero) asc)

infix 4 _⊑_
_⊑_ : ∀ {n} → Rel (ASC n) 0ℓ
a ⊑ b = ∀ {l} s → has a (l , s) ≤ has b (l , s)

infix 4 _≅_
_≅_ : ∀ {n} → Rel (ASC n) 0ℓ
a ≅ b = ∀ {l} s → has a (l , s) ≡ has b (l , s)
