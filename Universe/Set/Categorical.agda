{-# OPTIONS --without-K --safe #-}

module Universe.Set.Categorical where

open import Level
open import Category.Base
open import Universe.Set
open import Relation.Equality.Base hiding (cong)
open import Universe.Setoid using (func; cong)
open import Category.Functor

open Category hiding (id; refl)

SetCat : ∀ a → Category (ℓsuc a) a a
SetCat a .Obj = Set a
SetCat _ ._⊸_ = _⇒_
SetCat _ .compose .func f .func g x = f (g x)
SetCat _ .compose .func f .cong g≈h x = f =$= g≈h x
SetCat _ .compose .cong f≈g h x = f≈g (h x)
SetCat _ .Category.id = id
SetCat _ .assoc _ _ _ _ = refl
SetCat _ .identityˡ _ _ = refl
SetCat _ .identityʳ _ _ = refl

LiftFunctor : ∀ {a} ℓ → Functor (SetCat a) (SetCat (a ⊔ ℓ))
LiftFunctor ℓ .obj A = Lift ℓ A
LiftFunctor _ .hom .func f (lift x) = lift (f x)
LiftFunctor _ .hom .cong f≈g (lift x) = lift =$= f≈g x
LiftFunctor _ .mor-∘ _ _ _ = refl
LiftFunctor _ .mor-id _ = refl
