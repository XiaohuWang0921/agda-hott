{-# OPTIONS --without-K --safe #-}

module Universe.Setoid.Categorical where

open import Level
open import Category.Base
open import Universe.Setoid

open Category hiding (compose; id)

category : ∀ a r → Category (ℓsuc (a ⊔ r)) (a ⊔ r) (a ⊔ r)
category a r .Obj = Setoid a r
category _ _ .[_,_] = _⇒_
category _ _ .Category.compose = compose
category _ _ .Category.id = id
category _ _ .assoc {Z = Z} _ _ _ _ = Setoid.refl Z
category _ _ .identityˡ {Y = Y} _ _ = Setoid.refl Y
category _ _ .identityʳ {Y = Y} _ _ = Setoid.refl Y
