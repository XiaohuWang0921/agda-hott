{-# OPTIONS --without-K --safe #-}

module Category.FunCat where

open import Level
open import Category.Base
open import Category.Functor
open import Category.Natural as Natural
open import Universe.Setoid as Setoid hiding (id; compose)
import Relation.Reasoning

private
  variable
    o p q l m n r s t : Level
    C : Category o m r
    D : Category p n s
    E : Category q o t
    
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

category : Category o m r → Category p n s → Category _ _ _
category C D = record
  { Obj = Functor C D
  ; [_,_] = _⇛_
  ; isCategory = isCategory
  }

Const : Functor C (category D C)
Const {C = C} = record
  { obj = λ X → record
    { obj = λ _ → X
    ; hom = const ⟨$⟩ C.id
    ; mor-∘ = λ f g → C.sym (C.identityˡ C.id)
    ; mor-id = C.refl
    }
  ; hom = record
    { func = λ f → record
      { at = λ _ → f
      ; isNatural = λ g → C.trans (C.identityʳ f) (C.sym (C.identityˡ f))
      }
    ; cong = λ f≈g _ → f≈g
    }
  ; mor-∘ = λ _ _ _ → C.refl
  ; mor-id = λ _ → C.refl
  }
  where module C = Category C

-- Join : Functor (category C (category C D)) (category C D)
-- Join {C = C} {D = D} = record
--   { obj = λ F → record
--     { obj = λ X → F <$> X <$> X
--     ; hom = λ {X Y} → D.compose Setoid.∘ ta Y Setoid.∘ hom F ˢ hom (F <$> X)
-- --     record
-- --       { func = λ f → ((F -$- f) <&> Y) D.∘ (F <$> X -$- f)
-- --       ; cong = λ {f} {g} f≈g → {!!}
-- --       }
--     ; mor-∘ = λ {X Y Z} f g →
--       let
--         open Relation.Reasoning D._≈_
--         open Equiv D.refl D.trig
--       in ((F -$- f C.∘ g) <&> Z) D.∘ (F <$> X -$- f C.∘ g) ≈⟨ {!!} ⟩
--          (((F -$- f) Natural.∘ (F -$- g)) <&> Z) D.∘ (F <$> X -$- f C.∘ g) ≡⟨⟩
--          (((F -$- f) <&> Z) D.∘ ((F -$- g) <&> Z)) D.∘ (F <$> X -$- f C.∘ g) ≈⟨ {!!} ⟩
--          (((F -$- f) <&> Z) D.∘ ((F -$- g) <&> Z)) D.∘ ((F <$> X -$- f) D.∘ (F <$> X -$- g)) ≈⟨ {!!} ⟩
--          {!!}
--     ; mor-id = {!!} } ; hom = {!!} ; mor-∘ = {!!} ; mor-id = {!!} }
--   where
--     module C = Category C
--     module D = Category D

Ap : Functor (category C (category D E)) (category (category C D) (category C E))
Ap {C = C} {D = D} {E = E} = record
  { obj = λ F → record
    { obj = λ G → record
      { obj = λ X → F <$> X <$> (G <$> X)
      ; hom = λ {X Y} → E.compose Setoid.∘ Functor.hom (F <$> Y) Setoid.∘ Functor.hom G ˢ ta (G <$> X) Setoid.∘ Functor.hom F
  --     record
  --       { func = λ f → (F <$> Y -$- G -$- f) E.∘ ((F -$- f) <&> G <$> X)
  --       ; cong = λ f≈g → {!!} }
      ; mor-∘ = λ {X Y Z} f g →
        let
          open Relation.Reasoning E._≈_
          open Equiv E.refl E.trig
        in begin
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
      ; mor-id = λ {X} →
        let
          open Relation.Reasoning E._≈_
          open Equiv E.refl E.trig
        in begin
          (F <$> X -$- G -$- C.id) E.∘ ((F -$- C.id) <&> G <$> X) ≈⟨ E.compose ⟨$⟩ _ ~$~ mor-id F _ ⟩
          (F <$> X -$- G -$- C.id) E.∘ (Natural.id <&> G <$> X) ≡⟨⟩
          {!!} } ; hom = {!!} ; mor-∘ = {!!} ; mor-id = {!!} } ; hom = {!!} ; mor-∘ = {!!} ; mor-id = {!!} }
   where
     module C = Category C
     module D = Category D
     module E = Category E
