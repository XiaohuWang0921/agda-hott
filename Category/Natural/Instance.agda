{-# OPTIONS --without-K --safe #-}

module Category.Natural.Instance where

open import Level
open import Category.Base
open import Category.Functor
open import Category.Natural

private
  variable
    o p m n r s : Level
    C : Category o m r
    D : Category p n s
    
instance
  isCategory : IsCategory (Functor C D) _⇛_
  isCategory {D = D} = record
    { compose = compose
    ; id = id
    ; assoc = λ _ _ _ _ → D.assoc _ _ _
    ; identityˡ = λ _ _ → D.identityˡ _
    ; identityʳ = λ _ _ → D.identityʳ _
    }
    where module D = Category D

  category : {C : Category o m r} {D : Category p n s} → Category _ _ _
  category {C = C} {D = D} = record
    { Obj = Functor C D
    ; [_,_] = _⇛_
    ; isCategory = isCategory
    }
