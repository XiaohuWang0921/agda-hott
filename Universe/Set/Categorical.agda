{-# OPTIONS --without-K --safe #-}

module Universe.Set.Categorical where

open import Level
open import Category.Base
open import Universe.Set
open import Relation.Equality.Base hiding (cong)
open import Universe.Setoid using (func; cong)

-- instance
--   isCategory : ∀ {a} → IsCategory (Set a) (λ X Y → X ⇒ Y)
--   isCategory = record
--     { compose = record
--       { func = λ f → record
--         { func = λ g x → f (g x)
--         ; cong = λ g≈h x → f =$= g≈h x
--         }
--       ; cong = λ f≈g h x → f≈g (h x)
--       }
--     ; id = id
--     ; assoc = λ _ _ _ _ → refl
--     ; identityˡ = λ _ _ → refl
--     ; identityʳ = λ _ _ → refl
--     }

open Category hiding (id; refl)

category : ∀ a → Category (ℓsuc a) a a
category a .Obj = Set a
category _ .[_,_] = _⇒_
category _ .compose .func f .func g x = f (g x)
category _ .compose .func f .cong g≈h x = f =$= g≈h x
category _ .compose .cong f≈g h x = f≈g (h x)
category _ .Category.id = id
category _ .assoc _ _ _ _ = refl
category _ .identityˡ _ _ = refl
category _ .identityʳ _ _ = refl
