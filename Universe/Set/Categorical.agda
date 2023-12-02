{-# OPTIONS --without-K --safe #-}

module Universe.Set.Categorical where

open import Level
open import Category.Base
open import Universe.Set
open import Relation.Equality.Base hiding (cong)
open import Universe.Setoid using (func; cong)

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
