{-# OPTIONS --without-K --safe #-}

module Universe.Setoid.Categorical where

open import Level
open import Category.Base
open import Universe.Setoid

instance
  isCategory : ∀ {a r} → IsCategory (Setoid a r) (λ X Y → X ⇒ Y)
  isCategory = record
    { compose = compose
    ; id = id
    ; assoc = λ {Z = Z} f g h x →
      let open Setoid Z in refl
    ; identityˡ = λ {Y = Y} f x →
      let open Setoid Y in refl
    ; identityʳ = λ {Y = Y} f x →
      let open Setoid Y in refl
    }

  category : ∀ {a r} → Category (ℓsuc (a ⊔ r)) (a ⊔ r) (a ⊔ r)
  category {a} {r} = record
    { Obj = Setoid a r
    ; [_,_] = _⇒_
    ; isCategory = isCategory
    }
