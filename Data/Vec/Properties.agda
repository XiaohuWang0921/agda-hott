{-# OPTIONS --without-K --safe #-}

module Data.Vec.Properties where

open import Data.Vec.Base
open import Universe.Set
open import Relation.Equality.Base
open import Level
open import Data.Nat.Base
open import Data.Fin.Base
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c
    n : ℕ

module _ {x y : A} {xs ys : Vec A n} where

  ∷-monic : x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
  ∷-monic refl = refl , refl

  ∷-monicˡ : x ∷ xs ≡ y ∷ ys → x ≡ y
  ∷-monicˡ refl = refl

  ∷-monicʳ : x ∷ xs ≡ y ∷ ys → xs ≡ ys
  ∷-monicʳ refl = refl

tabulate-cong : {f g : Fin n → A} → f ≗ g → tabulate f ≡ tabulate g
tabulate-cong {0} _ = refl
tabulate-cong {suc _} f≗g = cong₂ _∷_ (f≗g zero) (tabulate-cong λ i → f≗g (suc i))

repeatPointwise : ∀ {x y} {_~_ : A → B → Set c} n → x ~ y → Pointwise _~_ (repeat n x) (repeat n y)
repeatPointwise 0 x~y = []
repeatPointwise (suc n) x~y = x~y ∷ (repeatPointwise n x~y)
