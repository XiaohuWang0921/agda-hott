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
    
-- instance
--   isCategory : IsCategory (Functor C D) _⇛_
--   isCategory {D = D} = record
--     { compose = compose
--     ; id = Natural.id
--     ; assoc = λ _ _ _ _ → D.assoc _ _ _
--     ; identityˡ = λ _ _ → D.identityˡ _
--     ; identityʳ = λ _ _ → D.identityʳ _
--     }
--     where module D = Category D

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

infixl 8 _ˢ_
_ˢ_ : Functor C (category D E) → Functor C D → Functor C E
_ˢ_ {C = C} {D = D} {E = E} F G = FˢG
  where
    module C = Category C
    module D = Category D
    module E = Category E

    FˢG : Functor C E
    FˢG .obj X = F <$> X <$> (G <$> X)
    FˢG .hom {X} {Y} = E.compose Setoid.∘ Functor.hom (F <$> Y) Setoid.∘ Functor.hom G Setoid.ˢ ta (G <$> X) Setoid.∘ Functor.hom F
    FˢG .mor-∘ {X} {Y} {Z} f g =
      let open Relation.Reasoning E._≈_
          open Equiv E.refl E.trig
      in
        (F <$> Z -$- G -$- f C.∘ g) E.∘ ((F -$- f C.∘ g) <&> G <$> X) ≈⟨ (λ→ E.compose - _) ~$~ mor-cong (F <$> Z) (mor-∘ G f g) ⟩
        (F <$> Z -$- (G -$- f) D.∘ (G -$- g)) E.∘ ((F -$- f C.∘ g) <&> G <$> X) ≈⟨ (λ→ E.compose - _) ~$~ mor-∘ (F <$> Z) _ _ ⟩
        ((F <$> Z -$- G -$- f) E.∘ (F <$> Z -$- G -$- g)) E.∘ ((F -$- f C.∘ g) <&> G <$> X) ≈⟨ E.compose ⟨$⟩ _ ~$~ mor-∘ F f g (G <$> X) ⟩
        ((F <$> Z -$- G -$- f) E.∘ (F <$> Z -$- G -$- g)) E.∘ (((F -$- f) Natural.∘ (F -$- g)) <&> G <$> X) ≡⟨⟩
        ((F <$> Z -$- G -$- f) E.∘ (F <$> Z -$- G -$- g)) E.∘ ((F -$- f) <&> G <$> X) E.∘ ((F -$- g) <&> G <$> X) ≈⟨ E.assoc _ _ _ ⟩
        (F <$> Z -$- G -$- f) E.∘ (F <$> Z -$- G -$- g) E.∘ ((F -$- f) <&> G <$> X) E.∘ ((F -$- g) <&> G <$> X) ≈˘⟨ E.compose ⟨$⟩ _ ~$~ E.assoc _ _ _ ⟩
        (F <$> Z -$- G -$- f) E.∘ ((F <$> Z -$- G -$- g) E.∘ ((F -$- f) <&> G <$> X)) E.∘ ((F -$- g) <&> G <$> X) ≈˘⟨ E.compose ⟨$⟩ _ ~$~ (λ→ E.compose - _) ~$~ isNatural (F -$- f) _ ⟩
        (F <$> Z -$- G -$- f) E.∘ (((F -$- f) <&> G <$> Y) E.∘ (F <$> Y -$- G -$- g)) E.∘ ((F -$- g) <&> G <$> X) ≈⟨ E.compose ⟨$⟩ _ ~$~ E.assoc _ _ _ ⟩
        (F <$> Z -$- G -$- f) E.∘ ((F -$- f) <&> G <$> Y) E.∘ (F <$> Y -$- G -$- g) E.∘ ((F -$- g) <&> G <$> X) ≈˘⟨ E.assoc _ _ _ ⟩
        ((F <$> Z -$- G -$- f) E.∘ ((F -$- f) <&> G <$> Y)) E.∘ (F <$> Y -$- G -$- g) E.∘ ((F -$- g) <&> G <$> X) ∎
    FˢG .mor-id {X} =
      let open Relation.Reasoning E._≈_
          open Equiv E.refl E.trig
      in
        (F <$> X -$- G -$- C.id) E.∘ ((F -$- C.id) <&> G <$> X) ≈⟨ E.compose ⟨$⟩ _ ~$~ mor-id F _ ⟩
        (F <$> X -$- G -$- C.id) E.∘ (Natural.id {F = F <$> X} <&> G <$> X) ≡⟨⟩
        (F <$> X -$- G -$- C.id) E.∘ E.id ≈⟨ E.identityʳ _ ⟩
        F <$> X -$- G -$- C.id ≈⟨ mor-cong (F <$> X) (mor-id G) ⟩
        F <$> X -$- D.id ≈⟨ mor-id (F <$> X) ⟩
        E.id ∎

ˢ-⇉ˡ : {F G : Functor C (category D E)} (H : Functor C D) → (F ⇛ G) ⟶ F ˢ H ⇛ G ˢ H
ˢ-⇉ˡ {C = C} {D = D} {E = E} {F} {G} H = slH where
  module C = Category C
  module D = Category D
  module E = Category E

  slH : (F ⇛ G) ⟶ F ˢ H ⇛ G ˢ H
  slH .func η .at X = (η <&> X) <&> H <$> X
  slH .func η .isNatural {X} {Y} f =
    let open Relation.Reasoning E._≈_
        open Equiv E.refl E.trig
    in
      ((η <&> Y) <&> H <$> Y) E.∘ (F <$> Y -$- H -$- f) E.∘ ((F -$- f) <&> H <$> X) ≈˘⟨ E.assoc _ _ _ ⟩
      (((η <&> Y) <&> H <$> Y) E.∘ (F <$> Y -$- H -$- f)) E.∘ ((F -$- f) <&> H <$> X) ≈⟨ (λ→ E.compose - _) ~$~ isNatural (η <&> Y) _ ⟩
      ((G <$> Y -$- H -$- f) E.∘ ((η <&> Y) <&> H <$> X)) E.∘ ((F -$- f) <&> H <$> X) ≈⟨ E.assoc _ _ _ ⟩
      (G <$> Y -$- H -$- f) E.∘ ((η <&> Y) <&> H <$> X) E.∘ ((F -$- f) <&> H <$> X) ≡⟨⟩
      (G <$> Y -$- H -$- f) E.∘ ((η <&> Y) Natural.∘ (F -$- f) <&> H <$> X) ≈⟨ E.compose ⟨$⟩ _ ~$~ isNatural η f _ ⟩
      (G <$> Y -$- H -$- f) E.∘ ((G -$- f) Natural.∘ (η <&> X) <&> H <$> X) ≡⟨⟩
      (G <$> Y -$- H -$- f) E.∘ ((G -$- f) <&> H <$> X) E.∘ ((η <&> X) <&> H <$> X) ≈˘⟨ E.assoc _ _ _ ⟩
      ((G <$> Y -$- H -$- f) E.∘ ((G -$- f) <&> H <$> X)) E.∘ ((η <&> X) <&> H <$> X) ∎
  slH .cong η≈ε X = η≈ε X (H <$> X)

ˢ-⇉ʳ : (F : Functor C (category D E)) {G H : Functor C D} → (G ⇛ H) ⟶ F ˢ G ⇛ F ˢ H
ˢ-⇉ʳ F .func η .at X = F <$> X -$- η <&> X
ˢ-⇉ʳ {C = C} {D = D} {E = E} F {G} {H} .func η .isNatural {X} {Y} f =
  let module C = Category C
      module D = Category D
      module E = Category E
      open Relation.Reasoning E._≈_
      open Equiv E.refl E.trig
  in
    (F <$> Y -$- η <&> Y) E.∘ (F <$> Y -$- G -$- f) E.∘ ((F -$- f) <&> G <$> X) ≈˘⟨ E.assoc _ _ _ ⟩
    ((F <$> Y -$- η <&> Y) E.∘ (F <$> Y -$- G -$- f)) E.∘ ((F -$- f) <&> G <$> X) ≈˘⟨ (λ→ E.compose - _) ~$~ mor-∘ (F <$> Y) _ _ ⟩
    (F <$> Y -$- (η <&> Y) D.∘ (G -$- f)) E.∘ ((F -$- f) <&> G <$> X) ≈⟨ (λ→ E.compose - _) ~$~ mor-cong (F <$> Y) (isNatural η f) ⟩
    (F <$> Y -$- (H -$- f) D.∘ (η <&> X)) E.∘ ((F -$- f) <&> G <$> X) ≈⟨ (λ→ E.compose - _) ~$~ mor-∘ (F <$> Y) _ _ ⟩
    ((F <$> Y -$- H -$- f) E.∘ (F <$> Y -$- η <&> X)) E.∘ ((F -$- f) <&> G <$> X) ≈⟨ E.assoc _ _ _ ⟩
    (F <$> Y -$- H -$- f) E.∘ (F <$> Y -$- η <&> X) E.∘ ((F -$- f) <&> G <$> X) ≈˘⟨ E.compose ⟨$⟩ _ ~$~ isNatural (F -$- f) _ ⟩
    (F <$> Y -$- H -$- f) E.∘ ((F -$- f) <&> H <$> X) E.∘ (F <$> X -$- η <&> X) ≈˘⟨ E.assoc _ _ _ ⟩
    ((F <$> Y -$- H -$- f) E.∘ ((F -$- f) <&> H <$> X)) E.∘ (F <$> X -$- η <&> X) ∎
ˢ-⇉ʳ F .cong η≈ε X = mor-cong (F <$> X) (η≈ε X)

Ap : Functor (category C (category D E)) (category (category C D) (category C E))
Ap .obj F .obj G = F ˢ G
Ap .obj F .hom = ˢ-⇉ʳ F
Ap .obj F .mor-∘ η ε X = mor-∘ (F <$> X) (η <&> X) (ε <&> X)
Ap .obj F .mor-id X = mor-id (F <$> X)
Ap .hom .func η .at H = ˢ-⇉ˡ H ⟨$⟩ η
Ap .hom .func η .isNatural {H} {I} ε X = isNatural (η <&> X) (ε <&> X)
Ap .hom .cong η≈ε H X = η≈ε X (H <$> X)
Ap {E = E} .mor-∘ _ _ _ _ = Category.refl E
Ap {E = E} .mor-id _ _ = Category.refl E

Compose : Functor (category D E) (category (category C D) (category C E))
Compose = (Const <$> Ap) ˢ Const

Flip : Functor (category C (category D E)) (category D (category C E))
Flip = (Compose ∘ Ap) ˢ (Const <$> Const)

infixr -1 Λ_-_
Λ_-_ : Functor C (category D E) → Category.Obj D → Functor C E
Λ F - X = Flip <$> F <$> X
