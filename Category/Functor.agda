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

open Functor public
    
infixl 5 _<$>_
_<$>_ = obj
{-# DISPLAY obj F X = F <$> X #-}

infixr 4.5 _-$-_
_-$-_ = mor
{-# DISPLAY mor F X = F -$- X #-}
{-# DISPLAY hom F ⟨$⟩ X = F -$- X #-}

infixr 4.25 _#$#_
_#$#_ = mor-cong
{-# DISPLAY mor-cong F X = F #$# X #-}
{-# DISPLAY hom F ~$~ X = F #$# X #-}

Id : Functor C C
Id .obj = λ X → X
Id .hom = Setoid.id
Id {C = C} .mor-∘ _ _ = Category.refl C
Id {C = C} .mor-id = Category.refl C

infixr 9 _∘_
_∘_ : Functor D E → Functor C D → Functor C E
(F ∘ G) .obj X = F <$> (G <$> X)
(F ∘ G) .hom = F .hom Setoid.∘ G .hom
_∘_ {E = E} F G .mor-∘ f g = Category.trans E (hom F ~$~ mor-∘ G f g) (mor-∘ F _ _)
_∘_ {E = E} F G .mor-id = Category.trans E (hom F ~$~ mor-id G) (mor-id F)

Opposite : Functor C D → Functor (Op C) (Op D)
Opposite F .obj = F .obj
Opposite F .hom = F .hom
Opposite F .mor-∘ f g = F .mor-∘ g f
Opposite F .mor-id = F .mor-id

Embed : ∀ {a} {A : Set a} (open Category C) (f : A → Obj) → Functor (FullSub C f) C
Embed f .obj = f
Embed f .hom = Setoid.id
Embed {C = C} f .mor-∘ _ _ = Category.Hom.refl C _ _
Embed {C = C} f .mor-id = Category.Hom.refl C _ _
