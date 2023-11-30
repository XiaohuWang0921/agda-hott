{-# OPTIONS --without-K --safe #-}

module Category.FunCat where

open import Level
open import Category.Base
open import Category.Functor
open import Category.Natural as Natural hiding (compose; id; _∘_)
open import Universe.Setoid as Setoid hiding (id; compose; _∘_; _ˢ_)
import Relation.Reasoning

private
  variable
    o p q l m n r s t : Level
    C : Category o m r
    D : Category p n s
    E : Category q o t

category : Category o m r → Category p n s → Category _ _ _
category C D = categoryCD
  where
    module D = Category D
    open Category

    categoryCD : Category _ _ _
    categoryCD .Obj = Functor C D
    categoryCD .[_,_] F G = F ⇛ G
    categoryCD .compose = Natural.compose
    categoryCD .id = Natural.id
    categoryCD .assoc _ _ _ _ = D.assoc _ _ _
    categoryCD .identityˡ _ _ = D.identityˡ _
    categoryCD .identityʳ _ _ = D.identityʳ _

Const : Functor C (category D C)
Const {C = C} = ConstC
  where
    module C = Category C

    ConstC : Functor C (category D C)
    ConstC .obj X .obj _ = X
    ConstC .obj _ .hom = const ⟨$⟩ C.id
    ConstC .obj _ .mor-∘ _ _ = C.sym (C.identityˡ C.id)
    ConstC .obj _ .mor-id = C.refl
    ConstC .hom .func f .at _ = f
    ConstC .hom .func f .isNatural _ = C.trans (C.identityʳ f) (C.sym (C.identityˡ f))
    ConstC .hom .cong f≈g _ = f≈g
    ConstC .mor-∘ _ _ _ = C.refl
    ConstC .mor-id _ = C.refl

Join : Functor (category C (category C D)) (category C D)
Join .obj F .obj X = F <$> X <$> X
Join {D = D} .obj F .hom {X} {Y} =
  let module D = Category D
  in (D.compose Setoid.∘ ta Y Setoid.∘ F .hom) Setoid.ˢ ((F <$> X) .hom)
Join {C = C} {D = D} .obj F .mor-∘ {X} {Y} {Z} f g =
  let module C = Category C
      module D = Category D
      open Relation.Reasoning D._≈_
      open Equiv D.refl D.trig
  in ((F -$- f C.∘ g) <&> Z) D.∘ (F <$> X -$- f C.∘ g) ≈⟨ (λ→ D.compose - _) ~$~ F .mor-∘ f g Z ⟩
     ((F -$- f) Natural.∘ (F -$- g) <&> Z) D.∘ (F <$> X -$- f C.∘ g) ≡⟨⟩
     (((F -$- f) <&> Z) D.∘ ((F -$- g) <&> Z)) D.∘ (F <$> X -$- f C.∘ g) ≈⟨ D.compose ⟨$⟩ _ ~$~ (F <$> X) .mor-∘ f g ⟩
     (((F -$- f) <&> Z) D.∘ ((F -$- g) <&> Z)) D.∘ (F <$> X -$- f) D.∘ (F <$> X -$- g) ≈⟨ D.assoc _ _ _ ⟩
     ((F -$- f) <&> Z) D.∘ ((F -$- g) <&> Z) D.∘ (F <$> X -$- f) D.∘ (F <$> X -$- g) ≈˘⟨ D.compose ⟨$⟩ _ ~$~ D.assoc _ _ _ ⟩
     ((F -$- f) <&> Z) D.∘ (((F -$- g) <&> Z) D.∘ (F <$> X -$- f)) D.∘ (F <$> X -$- g) ≈⟨ D.compose ⟨$⟩ _ ~$~ (λ→ D.compose - _) ~$~ (F -$- g) .isNatural f ⟩
     ((F -$- f) <&> Z) D.∘ ((F <$> Y -$- f) D.∘ ((F -$- g) <&> Y)) D.∘ (F <$> X -$- g) ≈⟨ D.compose ⟨$⟩ _ ~$~ D.assoc _ _ _ ⟩
     ((F -$- f) <&> Z) D.∘ (F <$> Y -$- f) D.∘ ((F -$- g) <&> Y) D.∘ (F <$> X -$- g) ≈˘⟨ D.assoc _ _ _ ⟩
     (((F -$- f) <&> Z) D.∘ (F <$> Y -$- f)) D.∘ ((F -$- g) <&> Y) D.∘ (F <$> X -$- g) ∎
Join {C = C} {D = D} .obj F .mor-id {X} =
  let module C = Category C
      module D = Category D
      open Relation.Reasoning D._≈_
      open Equiv D.refl D.trig
  in ((F -$- C.id) <&> X) D.∘ (F <$> X -$- C.id) ≈⟨ D.compose ⟨$⟩ _ ~$~ (F <$> X) .mor-id ⟩
     ((F -$- C.id) <&> X) D.∘ D.id ≈⟨ D.identityʳ _ ⟩
     (F -$- C.id) <&> X ≈⟨ F .mor-id X ⟩
     Natural.id {F = F <$> X} <&> X ≡⟨⟩
     D.id ∎
Join .hom .func η .at X = (η <&> X) <&> X
Join {D = D} .hom {F} {G} .func η .isNatural {X} {Y} f =
  let module D = Category D
      open Relation.Reasoning D._≈_
      open Equiv D.refl D.trig
  in ((η <&> Y) <&> Y) D.∘ ((F -$- f) <&> Y) D.∘ (F <$> X -$- f) ≈˘⟨ D.assoc _ _ _ ⟩
     (((η <&> Y) <&> Y) D.∘ ((F -$- f) <&> Y)) D.∘ (F <$> X -$- f) ≡⟨⟩
     ((η <&> Y) Natural.∘ (F -$- f) <&> Y) D.∘ (F <$> X -$- f) ≈⟨ (λ→ D.compose - _) ~$~ η .isNatural f Y ⟩
     ((G -$- f) Natural.∘ (η <&> X) <&> Y) D.∘ (F <$> X -$- f) ≡⟨⟩
     (((G -$- f) <&> Y) D.∘ ((η <&> X) <&> Y)) D.∘ (F <$> X -$- f) ≈⟨ D.assoc _ _ _ ⟩
     ((G -$- f) <&> Y) D.∘ ((η <&> X) <&> Y) D.∘ (F <$> X -$- f) ≈⟨ D.compose ⟨$⟩ _ ~$~ (η <&> X) .isNatural f ⟩
     ((G -$- f) <&> Y) D.∘ (G <$> X -$- f) D.∘ ((η <&> X) <&> X) ≈˘⟨ D.assoc _ _ _ ⟩
     (((G -$- f) <&> Y) D.∘ (G <$> X -$- f)) D.∘ ((η <&> X) <&> X) ∎
Join .hom .cong η≈ε X = η≈ε X X
Join {D = D} .mor-∘ _ _ _ = Category.refl D
Join {D = D} .mor-id _ = Category.refl D

Compose : Functor (category D E) (category (category C D) (category C E))
Compose .obj F .obj G = F ∘ G
Compose .obj F .hom = postCompose F
Compose .obj F .mor-∘ η ε X = F .mor-∘ (η <&> X) (ε <&> X)
Compose .obj F .mor-id _ = F .mor-id
Compose .hom {F} {G} .func η .at H = η ⋊ H
Compose .hom .func η .isNatural ε X = η .isNatural (ε <&> X)
Compose .hom .cong η≈ε H X = η≈ε (H <$> X)
Compose {E = E} .mor-∘ _ _ _ _ = Category.refl E
Compose {E = E} .mor-id _ _ = Category.refl E

infixr -1 Λ_-_
Λ_-_ : Functor C (category D E) → Category.Obj D → Functor C E
(Λ F - X) .obj Y = F <$> Y <$> X
(Λ F - X) .hom = ta X Setoid.∘ F .hom
(Λ F - X) .mor-∘ f g = F .mor-∘ f g X
(Λ F - X) .mor-id = F .mor-id X

Flip : Functor (category C (category D E)) (category D (category C E))
Flip .obj F .obj X = Λ F - X
Flip .obj F .hom .func f .at X = F <$> X -$- f
Flip {E = E} .obj F .hom .func f .isNatural g = Category.sym E ((F -$- g) .isNatural f)
Flip .obj F .hom .cong f≈g X = F <$> X #$# f≈g
Flip .obj F .mor-∘ f g X = (F <$> X) .mor-∘ f g
Flip .obj F .mor-id X = (F <$> X) .mor-id
Flip .hom .func η .at X .at Y = (η <&> Y) <&> X
Flip .hom .func η .at X .isNatural f = η .isNatural f X
Flip .hom .func η .isNatural f Y = (η <&> Y) .isNatural f
Flip .hom .cong η≈ε X Y = η≈ε Y X
Flip {E = E} .mor-∘ _ _ _ _ = Category.refl E
Flip {E = E} .mor-id _ _ = Category.refl E

Ap : Functor (category C (category D E)) (category (category C D) (category C E))
Ap = (Compose <$> Join) ∘ Compose ∘ Flip

infixl 8 _ˢ_
_ˢ_ : Functor C (category D E) → Functor C D → Functor C E
F ˢ G = Ap <$> F <$> G
