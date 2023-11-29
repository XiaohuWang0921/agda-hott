{-# OPTIONS --without-K --safe #-}

module Category.Base where

open import Level
open import Relation.Core
open import Universe.Setoid hiding (compose; _≈_;  _∘_; id; refl; reflexive; sym; trans; trig)
open import Relation.Equality.Core hiding (refl)
open import Data.Unit.Core

-- record IsCategory {o m r} (Obj : Set o) ([_,_] : Obj → Obj → Setoid m r) : Set (o ⊔ m ⊔ r) where

--   Mor : Obj → Obj → Set m
--   Mor X Y = Setoid.Carrier [ X , Y ]

--   infix 4 _≈_
--   _≈_ : ∀ {X Y} → Rel (Mor X Y) r
--   _≈_ {X} {Y} = Setoid._≈_ [ X , Y ]

--   refl : ∀ {X Y} {f : Mor X Y} → f ≈ f
--   refl {X} {Y} = Setoid.refl [ X , Y ]

--   reflexive : ∀ {X Y} {f g : Mor X Y} → f ≡ g → f ≈ g
--   reflexive {X} {Y} = Setoid.reflexive [ X , Y ]

--   trig : ∀ {X Y} {f g h : Mor X Y} → g ≈ f → g ≈ h → f ≈ h
--   trig {X} {Y} = Setoid.trig [ X , Y ]

--   sym : ∀ {X Y} {f g : Mor X Y} → f ≈ g → g ≈ f
--   sym {X} {Y} = Setoid.sym [ X , Y ]

--   trans : ∀ {X Y} {f g h : Mor X Y} → f ≈ g → g ≈ h → f ≈ h
--   trans {X} {Y} = Setoid.trans [ X , Y ]

--   field
--     compose : ∀ {X Y Z} → [ Y , Z ] ⟶ [ X , Y ] ⇒ [ X , Z ]
--     id : ∀ {X} → Mor X X
    
--   infixr 9 _∘_
--   _∘_ : ∀ {X Y Z} → Mor Y Z → Mor X Y → Mor X Z
--   f ∘ g = compose ⟨$⟩ f ⟨$⟩ g

--   field
--     assoc : ∀ {W X Y Z} (f : Mor Y Z) (g : Mor X Y) (h : Mor W X) → (f ∘ g) ∘ h ≈ f ∘ g ∘ h
--     identityˡ : ∀ {X Y} (f : Mor X Y) → id ∘ f ≈ f
--     identityʳ : ∀ {X Y} (f : Mor X Y) → f ∘ id ≈ f

-- opposite : ∀ {o m r} {Obj : Set o} {[_,_] : Obj → Obj → Setoid m r} → IsCategory Obj [_,_] → IsCategory Obj (λ X Y → [ Y , X ])
-- opposite {[_,_] = [_,_]} isCategory = record
--   { compose = flip ⟨$⟩ compose
--   ; assoc = λ f g h →
--     sym (assoc h g f)
--   ; identityˡ = identityʳ
--   ; identityʳ = identityˡ
--   }
--   where open IsCategory isCategory

-- fullSubcat : ∀ {a o m r} {A : Set a} {Obj : Set o} {[_,_] : Obj → Obj → Setoid m r} (F : A → Obj) → IsCategory Obj [_,_] → IsCategory A (λ X Y → [ F X , F Y ])
-- fullSubcat F isCategory = record
--   { compose = compose
--   ; assoc = assoc
--   ; identityˡ = identityˡ
--   ; identityʳ = identityʳ
--   }
--   where open IsCategory isCategory

-- preorder : ∀ {a r} {A : Set a} {_≲_ : Rel A r} → (∀ {x} → x ≲ x) → (∀ {x y z} → x ≲ y → y ≲ z → x ≲ z) → IsCategory A (λ x y → Trivial (x ≲ y))
-- preorder refl trans = record
--   { compose = record
--     { func = λ y≲z → record
--       { func = λ x≲y → trans x≲y y≲z
--       ; cong = λ _ → tt
--       }
--     ; cong = λ _ _ → tt
--     }
--   ; id = refl
--   ; assoc = λ _ _ _ → tt
--   ; identityˡ = λ _ → tt
--   ; identityʳ = λ _ → tt
--   }

record Category o m r : Set (ℓsuc (o ⊔ m ⊔ r)) where

  field
    Obj : Set o
    [_,_] : Obj → Obj → Setoid m r

  Mor : Obj → Obj → Set m
  Mor X Y = [ X , Y ] .Carrier

  module Hom X Y = Setoid [ X , Y ]

  infix 4 _≈_
  _≈_ : ∀ {X Y} → Rel (Mor X Y) r
  _≈_ {X} {Y} = Hom._≈_ X Y

  refl : ∀ {X Y} {f : Mor X Y} → f ≈ f
  refl {X} {Y} = Setoid.refl [ X , Y ]

  reflexive : ∀ {X Y} {f g : Mor X Y} → f ≡ g → f ≈ g
  reflexive {X} {Y} = Setoid.reflexive [ X , Y ]

  trig : ∀ {X Y} {f g h : Mor X Y} → g ≈ f → g ≈ h → f ≈ h
  trig {X} {Y} = Setoid.trig [ X , Y ]

  sym : ∀ {X Y} {f g : Mor X Y} → f ≈ g → g ≈ f
  sym {X} {Y} = Setoid.sym [ X , Y ]

  trans : ∀ {X Y} {f g h : Mor X Y} → f ≈ g → g ≈ h → f ≈ h
  trans {X} {Y} = Setoid.trans [ X , Y ]  

  field
    compose : ∀ {X Y Z} → [ Y , Z ] ⟶ [ X , Y ] ⇒ [ X , Z ]
    id : ∀ {X} → Mor X X
    
  infixr 9 _∘_
  _∘_ : ∀ {X Y Z} → Mor Y Z → Mor X Y → Mor X Z
  f ∘ g = compose ⟨$⟩ f ⟨$⟩ g

  field
    assoc : ∀ {W X Y Z} (f : Mor Y Z) (g : Mor X Y) (h : Mor W X) → (f ∘ g) ∘ h ≈ f ∘ g ∘ h
    identityˡ : ∀ {X Y} (f : Mor X Y) → id ∘ f ≈ f
    identityʳ : ∀ {X Y} (f : Mor X Y) → f ∘ id ≈ f

open Category

Op : ∀ {o m r} → Category o m r → Category o m r
Op C .Obj = C .Obj
Op C .[_,_] X Y = C .[_,_] Y X
Op C .compose = flip ⟨$⟩ C .compose
Op C .id = C .id
Op C .assoc f g h = Hom.sym C _ _ (C .assoc h g f)
Op C .identityˡ = C .identityʳ
Op C .identityʳ = C .identityˡ

FullSub : ∀ {a o m r} {A : Set a} (C : Category o m r) → (A → C .Obj) → Category a m r
FullSub {A = A} C F .Obj = A
FullSub C F .[_,_] X Y = C .[_,_] (F X) (F Y)
FullSub C F .compose = C .compose
FullSub C F .id = C .id
FullSub C F .assoc = C .assoc
FullSub C F .identityˡ = C .identityˡ
FullSub C F .identityʳ = C .identityʳ

Preorder : ∀ {a r} {A : Set a} (_≲_ : Rel A r) → (∀ {x} → x ≲ x) → (∀ {x y z} → x ≲ y → y ≲ z → x ≲ z) → Category a r 0ℓ
Preorder {A = A} _≲_ refl trans .Obj = A
Preorder {A = A} _≲_ refl trans .[_,_] x y = Trivial (x ≲ y)
Preorder {A = A} _≲_ refl trans .compose .func y≲z .func x≲y = trans x≲y y≲z
Preorder {A = A} _≲_ refl trans .compose .func y≲z .cong _ = tt
Preorder {A = A} _≲_ refl trans .compose .cong _ _ = tt
Preorder {A = A} _≲_ refl trans .id = refl
Preorder {A = A} _≲_ refl trans .assoc _ _ _ = tt
Preorder {A = A} _≲_ refl trans .identityˡ _ = tt
Preorder {A = A} _≲_ refl trans .identityʳ _ = tt
