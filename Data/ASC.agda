{-# OPTIONS --without-K --safe #-}

module Data.ASC where
-- ASC stands for abstract simplicial complex
open import Data.Bool.Base hiding (_≤?_)
open import Data.Fin.Base
open import Data.Fin.Subset.Base
open import Data.Fin.Subset.Properties
open import Data.Nat.Base as ℕ hiding (_≤_)
open import Data.Bool.Properties hiding (≤?-functorˡ)
open import Category.Base
open import Category.Functor
open import Universe.Setoid using (func)
open import Data.Nat.Properties using (≤?-functorˡ; <?-functorˡ)
open import Relation.Equality.Base
open import Data.Unit.Core
open import Universe.Set using (_≗_; flip; IsMonic; _|>_)
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

private
  variable
    k l m n : ℕ

infix 0 _∈_ _∉_
_∈_ : CSet k l → ASC k → Set
s ∈ asc = Has asc (_ , s)

_∉_ : CSet k l → ASC k → Set
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

preimages : (Fin m → Fin n) → ASC n → ASC m
preimages f asc .revMap = asc .revMap ∘ Opposite (image-functor f)
preimages f asc .hasAllPoints s rewrite l≡1 s refl .proj₂ rewrite image-single f (l≡1 s refl .proj₁) = asc .hasAllPoints _

empty∈asc : (asc : ASC (suc n)) → empty _ ∈ asc
empty∈asc asc = Has-⊆ asc empty⊂s (asc .hasAllPoints (single zero))

l≤1⇒s∈asc : (s : CSet (suc n) l) (asc : ASC (suc n)) → l ℕ.≤ 1 → s ∈ asc
l≤1⇒s∈asc s asc 0≤n rewrite l≡0 s refl = empty∈asc asc
l≤1⇒s∈asc s asc (s≤s 0≤n) = asc .hasAllPoints s

egamis : ∀ {m n} (f : Fin (suc m) → Fin n) → IsMonic f → ASC (suc m) → ASC n
egamis f _ asc .revMap = asc .revMap ∘ Opposite (preimage-functor f)
egamis f f-monic asc .hasAllPoints s =
  l≤1⇒s∈asc (preimage f s .proj₂) asc (pser (λ t → preimage f t .proj₁ ℕ.≤ 1) (l≡1 s refl .proj₂) (preimage-monic-single (l≡1 s refl .proj₁) f-monic))

infix 4 _⊑_
_⊑_ : ∀ {n} → Rel (ASC n) 0ℓ
a ⊑ b = ∀ {l} s → has a (l , s) ≤ has b (l , s)

infix 4 _≅_
_≅_ : ∀ {n} → Rel (ASC n) 0ℓ
a ≅ b = ∀ {l} s → has a (l , s) ≡ has b (l , s)

⊑-refl : {a : ASC n} → a ⊑ a
⊑-refl _ = ≤-refl

⊑-antisym : {a b : ASC n} → a ⊑ b → b ⊑ a → a ≅ b
⊑-antisym a⊑b b⊑a s = ≤-antisym (a⊑b s) (b⊑a s)

⊑-trans : {a b c : ASC n} → a ⊑ b → b ⊑ c → a ⊑ c
⊑-trans a⊑b b⊑c s = ≤-trans (a⊑b s) (b⊑c s)

⊑-∈ : ∀ {a b} (s : CSet k l) → a ⊑ b → s ∈ a → s ∈ b
⊑-∈ s a⊑b = T-≤ (a⊑b s)

l≡0⇒s∈asc : (s : CSet (suc n) 0) (asc : ASC (suc n)) → s ∈ asc
l≡0⇒s∈asc s asc = l≤1⇒s∈asc s asc 0≤n
