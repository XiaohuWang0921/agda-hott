{-# OPTIONS --without-K --safe #-}

module Category.Base where

open import Level
open import Relation.Core
open import Universe.Setoid hiding (compose; _∘_; id)
open import Relation.Equality.Core hiding (refl)

record IsCategory {o m r} (Obj : Set o) ([_,_] : Obj → Obj → Setoid m r) : Set (o ⊔ m ⊔ r) where

  Mor : Obj → Obj → Set m
  Mor X Y = Setoid.Carrier [ X , Y ]

  infix 4 _≈_
  _≈_ : ∀ {X Y} → Rel (Mor X Y) r
  _≈_ {X} {Y} = Setoid._≈_ [ X , Y ]

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

opposite : ∀ {o m r} {Obj : Set o} {[_,_] : Obj → Obj → Setoid m r} → IsCategory Obj [_,_] → IsCategory Obj (λ X Y → [ Y , X ])
opposite {[_,_] = [_,_]} isCategory = record
  { compose = flip ⟨$⟩ compose
  ; assoc = λ f g h →
    sym (assoc h g f)
  ; identityˡ = identityʳ
  ; identityʳ = identityˡ
  }
  where open IsCategory isCategory

fullSubcat : ∀ {a o m r} {A : Set a} {Obj : Set o} {[_,_] : Obj → Obj → Setoid m r} (F : A → Obj) → IsCategory Obj [_,_] → IsCategory A (λ X Y → [ F X , F Y ])
fullSubcat F isCategory = record
  { compose = compose
  ; assoc = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  }
  where open IsCategory isCategory

record Category o m r : Set (ℓsuc (o ⊔ m ⊔ r)) where
  field
    Obj : Set o
    [_,_] : Obj → Obj → Setoid m r
    isCategory : IsCategory Obj [_,_]

  open IsCategory isCategory public

Op : ∀ {o m r} → Category o m r → Category o m r
Op Cat = record
  { isCategory = opposite isCategory
  }
  where open Category Cat

FullSub : ∀ {a o m r} {A : Set a} (Cat : Category o m r) (open Category Cat) → (A → Obj) → Category a m r
FullSub {A = A} Cat F = record
  { isCategory = fullSubcat F isCategory
  }
  where open Category Cat
