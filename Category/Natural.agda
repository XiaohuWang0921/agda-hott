{-# OPTIONS --without-K --safe #-}

module Category.Natural where

open import Level
open import Category.Base
open import Category.Functor as Functor hiding (_∘_)
open import Relation.Core
import Relation.Reasoning
open import Universe.Setoid hiding (id; compose; _∘_)

private
  variable
    o p q l m n r s t : Level
    C : Category o l r
    D : Category p m s
    E : Category q n t

infixr 0 _⇉_
record _⇉_ {C : Category o m r} {D : Category p n s} (F G : Functor C D) : Set (o ⊔ m ⊔ n ⊔ s) where

  private
    module C = Category C
    module D = Category D

  field
    at : ∀ X → D.Mor (F <$> X) (G <$> X)
    isNatural : ∀ {X Y} (f : C.Mor X Y) → at Y D.∘ (F -$- f) D.≈ (G -$- f) D.∘ at X

open _⇉_ public

infixr 4.5 _<&>_
_<&>_ = _⇉_.at
{-# DISPLAY at η X = η <&> X #-}

infixr 0 _⇛_
_⇛_ : Functor C D → Functor C D → Setoid _ _
_⇛_ {D = D} F G = F⇛G
  where
    module D = Category D

    F⇛G : Setoid _ _
    F⇛G .Carrier = F ⇉ G
    F⇛G ._≈_ φ ψ = ∀ X → φ <&> X D.≈ ψ <&> X
    F⇛G .refl _ = D.refl
    F⇛G .trig ψ≈φ ψ≈χ X = D.trig (ψ≈φ X) (ψ≈χ X)

ta : {F G : Functor C D} (open Category D) (X : Category.Obj C) → (F ⇛ G) ⟶ [ F <$> X , G <$> X ]
ta X .func η = η <&> X
ta X .cong η≈ε = η≈ε X

id : {F : Functor C D} → F ⇉ F
id {D = D} {F = F} = idDF
  where
    module D = Category D

    idDF : _ ⇉ _
    idDF .at _ = D.id
    idDF .isNatural f =
      D.trans (D.identityˡ _) (D.sym (D.identityʳ _))
  
infixr 9 _∘_
_∘_ : {F G H : Functor C D} → G ⇉ H → F ⇉ G → F ⇉ H
_∘_ {D = D} {F = F} {G = G} {H = H} ε η = ε∘η
  where
    module D = Category D

    ε∘η : _ ⇉ _
    ε∘η .at X = (ε <&> X) D.∘ (η <&> X)
    ε∘η .isNatural {X} {Y} f =
      let open Relation.Reasoning D._≈_
          open Equiv D.refl D.trig
      in
        ((ε <&> Y) D.∘ (η <&> Y)) D.∘ (F -$- f) ≈⟨ D.assoc _ _ _ ⟩
        (ε <&> Y) D.∘ (η <&> Y) D.∘ (F -$- f)   ≈⟨ D.compose ⟨$⟩ _ ~$~ isNatural η f ⟩
        (ε <&> Y) D.∘ (G -$- f) D.∘ (η <&> X)   ≈˘⟨ D.assoc _ _ _ ⟩
        ((ε <&> Y) D.∘ (G -$- f)) D.∘ (η <&> X) ≈⟨ (D.compose ~$~ isNatural ε f) _ ⟩
        ((H -$- f) D.∘ (ε <&> X)) D.∘ (η <&> X) ≈⟨ D.assoc _ _ _ ⟩
        (H -$- f) D.∘ (ε <&> X) D.∘ (η <&> X)   ∎

compose : {F G H : Functor C D} → (G ⇛ H) ⟶ (F ⇛ G) ⇒ F ⇛ H
compose {D = D} = composeD
  where
    module D = Category D

    composeD : (_ ⇛ _) ⟶ (_ ⇛ _) ⇒ _ ⇛ _
    composeD .func ε .func η = ε ∘ η
    composeD .func ε .cong η≈ι X = D.compose ⟨$⟩ _ ~$~ η≈ι X
    composeD .cong ε≈ι η X = (D.compose ~$~ ε≈ι X) _

op : {C : Category o l r} {D : Category p m s} {F G : Functor C D} → (F ⇛ G) ⟶ Opposite G ⇛ Opposite F
op {D = D} = opD
  where
    module D = Category D

    opD : (_ ⇛ _) ⟶ _ ⇛ _
    opD .func η .at X = η <&> X
    opD .func η .isNatural f = D.sym (η .isNatural f)
    opD .cong η≈ε = η≈ε

infixr 9 _⋉_
_⋉_ : (F : Functor D E) {G H : Functor C D} → G ⇉ H → (F Functor.∘ G) ⇉ (F Functor.∘ H)
(F ⋉ η) .at X = F -$- η <&> X
_⋉_ {D = D} {E = E} F {G = G} {H = H} η .isNatural {X} {Y} f =
  (F -$- η <&> Y) E.∘ (F -$- G -$- f) ≈˘⟨ mor-∘ F _ _ ⟩
  F -$- ((η <&> Y) D.∘ (G -$- f)) ≈⟨ F #$# isNatural η f ⟩
  F -$- ((H -$- f) D.∘ (η <&> X)) ≈⟨ mor-∘ F _ _ ⟩
  (F -$- H -$- f) E.∘ (F -$- η <&> X) ∎
  where module D = Category D
        module E = Category E
        open Relation.Reasoning (E._≈_ )
        open Equiv E.refl E.trig

infixl 9 _⋊_
_⋊_ : {F G : Functor D E} → F ⇉ G → (H : Functor C D) → (F Functor.∘ H) ⇉ (G Functor.∘ H)
(η ⋊ H) .at X = η <&> H <$> X
(η ⋊ H) .isNatural f = isNatural η (H -$- f)

postCompose : (F : Functor D E) {G H : Functor C D} → (G ⇛ H) ⟶ (F Functor.∘ G) ⇛ (F Functor.∘ H)
postCompose F .func = F ⋉_
postCompose F .cong η≈ε X = F #$# η≈ε X

preCompose : {F G : Functor D E} (H : Functor C D) → (F ⇛ G) ⟶ (F Functor.∘ H) ⇛ (G Functor.∘ H)
preCompose H .func = _⋊ H
preCompose H .cong η≈ε X = η≈ε (H <$> X)
