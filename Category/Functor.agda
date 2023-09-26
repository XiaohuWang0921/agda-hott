{-# OPTIONS --without-K --safe #-}

module Category.Functor where

open import Level
open import Category.Base
open import Universe.Setoid as Setoid hiding (id; _∘_)

private
  variable
    o p q l m n r s t : Level
    C : Category o l r
    D : Category p m s
    E : Category q n t

record Functor (C : Category o m r) (D : Category p n s) : Set (o ⊔ p ⊔ m ⊔ n ⊔ r ⊔ s) where
  open Category {{...}}

  private
    instance
      categoryC = C
      categoryD = D
  
  field
    obj : Category.Obj C → Category.Obj D
    hom : ∀ {X Y} → [ X , Y ] ⟶ [ obj X , obj Y ]

  mor : ∀ {X Y} → Mor X Y → Mor (obj X) (obj Y)
  mor = hom ⟨$⟩_

  mor-cong : {X Y : Category.Obj C} {f g : Mor X Y} → f ≈ g → mor f ≈ mor g
  mor-cong = hom ~$~_

  field
    mor-∘ : {X Y Z : Category.Obj C} (f : Mor Y Z) (g : Mor X Y) → mor (f ∘ g) ≈ mor f ∘ mor g
    mor-id : ∀ {X} → mor (id {X = X}) ≈ id {X = obj X}

infixl 5 _<$>_
_<$>_ = Functor.obj

infixr 4.5 _-$-_
_-$-_ = Functor.mor

infixr 4.25 _#$#_
_#$#_ = Functor.mor-cong

Id : Functor C C
Id {C = C} = record
  { obj = λ O → O
  ; hom = Setoid.id
  ; mor-∘ = λ _ _ → refl
  ; mor-id = refl
  }
  where open Category C

infixr 9 _∘_
_∘_ : Functor D E → Functor C D → Functor C E
_∘_ {E = E} F G = record
  { obj = λ X → obj F (obj G X)
  ; hom = hom F Setoid.∘ hom G
  ; mor-∘ = λ f g → trans (hom F ~$~ mor-∘ G f g) (mor-∘ F _ _)
  ; mor-id = trans (hom F ~$~ mor-id G) (mor-id F)
  }
  where open Functor
        open Category E

Embed : ∀ {a} {A : Set a} (open Category C) (f : A → Obj) → Functor (FullSub C f) C
Embed {C = C} f = record
  { obj = f
  ; hom = Setoid.id
  ; mor-∘ = λ _ _ → refl
  ; mor-id = refl
  }
  where open Category C
