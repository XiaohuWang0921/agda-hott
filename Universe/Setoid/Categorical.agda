{-# OPTIONS --without-K --safe #-}

module Universe.Setoid.Categorical where

open import Level
open import Category.Base
open import Universe.Setoid

open Category hiding (compose; id)

SetoidCat : ∀ a r → Category (ℓsuc (a ⊔ r)) (a ⊔ r) (a ⊔ r)
SetoidCat a r .Obj = Setoid a r
SetoidCat _ _ ._⊸_ = _⇒_
SetoidCat _ _ .Category.compose = compose
SetoidCat _ _ .Category.id = id
SetoidCat _ _ .assoc {Z = Z} _ _ _ _ = Setoid.refl Z
SetoidCat _ _ .identityˡ {Y = Y} _ _ = Setoid.refl Y
SetoidCat _ _ .identityʳ {Y = Y} _ _ = Setoid.refl Y
