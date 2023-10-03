{-# OPTIONS --without-K --safe #-}

module Category.Natural where

open import Level
open import Category.Base
open import Category.Functor as Functor hiding (_∘_)
open import Relation.Core
open import Relation.Reasoning
open import Universe.Setoid hiding (id; compose; _∘_)

private
  variable
    o p q l m n r s t : Level
    C : Category o l r
    D : Category p m s
    E : Category q n t

infixr 0 _⇉_
record _⇉_ {C : Category o m r} {D : Category p n s} (F G : Functor C D) : Set (o ⊔ m ⊔ n ⊔ s) where
  open Category {{...}}

  private
    instance
      categoryC = C
      categoryD = D

  field
    at : ∀ X → Mor (F <$> X) (G <$> X)
    isNatural : ∀ {X Y} (f : Mor X Y) → at Y ∘ (F -$- f) ≈ (G -$- f) ∘ at X

open _⇉_ public

infixr 4.5 _<&>_
_<&>_ = _⇉_.at

infixr 0 _⇛_
_⇛_ : Functor C D → Functor C D → Setoid _ _
_⇛_ {D = D} F G = record
  { Carrier = F ⇉ G
  ; _≈_ = λ φ ψ → ∀ X → φ <&> X ≈ ψ <&> X
  ; refl = λ _ → refl
  ; trig = λ ψ≈φ ψ≈χ X → trig (ψ≈φ X) (ψ≈χ X)
  }
  where open Category D

id : {F : Functor C D} → F ⇉ F
id {D = D} {F = F} = record
  { at = λ _ → D.id
  ; isNatural = λ f →
    D.trans (D.identityˡ _) (D.sym (D.identityʳ _))
  }
  where module D = Category D

infixr 9 _∘_
_∘_ : {F G H : Functor C D} → G ⇉ H → F ⇉ G → F ⇉ H
_∘_ {D = D} {F = F} {G = G} {H = H} ε η = record
  { at = λ X → (ε <&> X) D.∘ (η <&> X)
  ; isNatural = λ {X} {Y} f →
    let open Equiv (D._≈_ {F <$> X} {H <$> Y}) D.refl D.trig
    in ((ε <&> Y) D.∘ (η <&> Y)) D.∘ (F -$- f) ≈⟨ D.assoc _ _ _ ⟩
       (ε <&> Y) D.∘ (η <&> Y) D.∘ (F -$- f)   ≈⟨ D.compose ⟨$⟩ _ ~$~ isNatural η f ⟩
       (ε <&> Y) D.∘ (G -$- f) D.∘ (η <&> X)   ≈˘⟨ D.assoc _ _ _ ⟩
       ((ε <&> Y) D.∘ (G -$- f)) D.∘ (η <&> X) ≈⟨ (D.compose ~$~ isNatural ε f) _ ⟩
       ((H -$- f) D.∘ (ε <&> X)) D.∘ (η <&> X) ≈⟨ D.assoc _ _ _ ⟩
       (H -$- f) D.∘ (ε <&> X) D.∘ (η <&> X)   ∎
  }
  where
    module D = Category D
    open _⇉_

compose : {F G H : Functor C D} → (G ⇛ H) ⟶ (F ⇛ G) ⇒ F ⇛ H
compose {D = D} = record
  { func = λ ε → record
    { func = λ η → ε ∘ η
    ; cong = λ η≈ι X → D.compose ⟨$⟩ _ ~$~ η≈ι X
    }
  ; cong = λ ε≈ι η X → (D.compose ~$~ ε≈ι X) _
  }
  where module D = Category D

-- infixr 9 _∙_
-- _∙_ : {F G : Functor D E} {I J : Functor C D} → F ⇉ G → I ⇉ J → (F Functor.∘ I) ⇉ (G Functor.∘ J)
-- _∙_ {D = D} {E = E} {F = F} {G = G} {I = I} {J = J} ε η = record
--   { at = λ X → (G -$- η <&> X) E.∘ (ε <&> I <$> X)
--   ; isNatural = λ {X} {Y} f →
--     let open Equiv (E._≈_ {F <$> (I <$> X)} {G <$> (J <$> Y)}) E.refl E.trig
--     in ((G -$- η <&> Y) E.∘ (ε <&> I <$> Y)) E.∘ (F -$- I -$- f) ≈⟨ E.assoc _ _ _ ⟩
--        (G -$- η <&> Y) E.∘ (ε <&> I <$> Y) E.∘ (F -$- I -$- f)   ≈⟨ E.compose ⟨$⟩ _ ~$~ isNatural ε _ ⟩
--        (G -$- η <&> Y) E.∘ (G -$- I -$- f) E.∘ (ε <&> I <$> X)   ≈˘⟨ E.assoc _ _ _ ⟩
--        ((G -$- η <&> Y) E.∘ (G -$- I -$- f)) E.∘ (ε <&> I <$> X) ≈˘⟨ (E.compose ~$~ mor-∘ G _ _) _ ⟩
--        (G -$- ((η <&> Y) D.∘ (I -$- f))) E.∘ (ε <&> I <$> X)     ≈⟨ (E.compose ~$~ hom G ~$~ isNatural η _) _ ⟩
--        (G -$- ((J -$- f) D.∘ (η <&> X))) E.∘ (ε <&> I <$> X)     ≈⟨ (E.compose ~$~ mor-∘ G _ _) _ ⟩
--        ((G -$- J -$- f) E.∘ (G -$- η <&> X)) E.∘ (ε <&> I <$> X) ≈⟨ E.assoc _ _ _ ⟩
--        (G -$- J -$- f) E.∘ (G -$- η <&> X) E.∘ (ε <&> I <$> X)   ∎
--   }
--   where
--     module D = Category D
--     module E = Category E
--     open _⇉_
--     open Functor.Functor

infixr 9 _⋉_
_⋉_ : (F : Functor D E) {G H : Functor C D} → G ⇉ H → (F Functor.∘ G) ⇉ (F Functor.∘ H)
_⋉_ {D = D} {E = E} F {G = G} {H = H} η = record
  { at = λ X → F -$- η <&> X
  ; isNatural = λ {X} {Y} f →
    let open Equiv (E._≈_ {F <$> (G <$> X)} {F <$> (H <$> Y)}) E.refl E.trig
    in (F -$- η <&> Y) E.∘ (F -$- G -$- f) ≈˘⟨ mor-∘ F _ _ ⟩
       F -$- ((η <&> Y) D.∘ (G -$- f)) ≈⟨ mor-cong F (isNatural η f) ⟩
       F -$- ((H -$- f) D.∘ (η <&> X)) ≈⟨ mor-∘ F _ _ ⟩
       (F -$- H -$- f) E.∘ (F -$- η <&> X) ∎
  }
  where
    module D = Category D
    module E = Category E
    open Functor.Functor
    open _⇉_

infixl 9 _⋊_
_⋊_ : {F G : Functor D E} → F ⇉ G → (H : Functor C D) → (F Functor.∘ H) ⇉ (G Functor.∘ H)
_⋊_ {D = D} {E = E} {F = F} {G = G} η H = record
  { at = λ X → η <&> H <$> X
  ; isNatural = λ f →
    isNatural η (H -$- f)
  }
  where open _⇉_
