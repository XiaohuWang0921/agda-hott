{-# OPTIONS --without-K --safe #-}

module Universe.Set.Categorical where

open import Level
open import Category.Base
open import Universe.Set
open import Relation.Equality.Base

instance
  isCategory : ∀ {a} → IsCategory (Set a) (λ X Y → X ⇒ Y)
  isCategory = record
    { compose = record
      { func = λ f → record
        { func = λ g x → f (g x)
        ; cong = λ g≈h x → f =$= g≈h x
        }
      ; cong = λ f≈g h x → f≈g (h x)
      }
    ; id = id
    ; assoc = λ _ _ _ _ → refl
    ; identityˡ = λ _ _ → refl
    ; identityʳ = λ _ _ → refl
    }

  category : ∀ {a} → Category (ℓsuc a) a a
  category = record
    { [_,_] = λ X Y → X ⇒ Y
    ; isCategory = isCategory
    }
