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

  private
    module C = Category C
    module D = Category D
  
  field
    obj : Category.Obj C → Category.Obj D
    hom : ∀ {X Y} → C.[ X , Y ] ⟶ D.[ obj X , obj Y ]

  mor : ∀ {X Y} → C.Mor X Y → D.Mor (obj X) (obj Y)
  mor = hom ⟨$⟩_

  mor-cong : {X Y : Category.Obj C} {f g : C.Mor X Y} → f C.≈ g → mor f D.≈ mor g
  mor-cong = hom ~$~_

  field
    mor-∘ : {X Y Z : Category.Obj C} (f : C.Mor Y Z) (g : C.Mor X Y) → mor (f C.∘ g) D.≈ mor f D.∘ mor g
    mor-id : ∀ {X} → mor (C.id {X = X}) D.≈ D.id
    
infixl 5 _<$>_
_<$>_ = Functor.obj

infixr 4.5 _-$-_
_-$-_ = Functor.mor

infixr 4.25 _#$#_
_#$#_ = Functor.mor-cong

Const : Category.Obj D → Functor C D
Const {D = D} X = record
  { obj = λ _ → X
  ; hom = const ⟨$⟩ id
  ; mor-∘ = λ f g → sym (identityˡ id)
  ; mor-id = refl
  }
  where open Category D

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

Opposite : Functor C D → Functor (Op C) (Op D)
Opposite F = record
  { obj = obj
  ; hom = hom
  ; mor-∘ = λ f g → mor-∘ g f
  ; mor-id = mor-id
  }
  where open Functor F

Embed : ∀ {a} {A : Set a} (open Category C) (f : A → Obj) → Functor (FullSub C f) C
Embed {C = C} f = record
  { obj = f
  ; hom = Setoid.id
  ; mor-∘ = λ _ _ → refl
  ; mor-id = refl
  }
  where open Category C
