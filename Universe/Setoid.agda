{-# OPTIONS --without-K --safe #-}

module Universe.Setoid where

open import Level
open import Universe.Setoid.Base public
open import Universe.Set as Set using ()
import Relation.Reasoning
open import Relation.Equality.Base as Eq using (_≡_)
open import Data.Unit.Core

infixr 0 _⟶_
record _⟶_ {a b r s} (A : Setoid a r) (B : Setoid b s) : Set (a ⊔ b ⊔ r ⊔ s) where

  private
    module A = Setoid A
    module B = Setoid B

  field
    func : Setoid.Carrier A → Setoid.Carrier B
    cong : ∀ {x y} → x A.≈ y → func x B.≈ func y

open _⟶_ public

infixl 5 _⟨$⟩_
_⟨$⟩_ = func
{-# DISPLAY func f x = f ⟨$⟩ x #-}

infixr 4.5 _~$~_
_~$~_ = cong
{-# DISPLAY cong f e = f ~$~ e #-}

Eq : ∀ {ℓ} → Set ℓ → Setoid ℓ ℓ
Eq A .Carrier = A
Eq A ._≈_ = _≡_
Eq A .refl = Eq.refl
Eq A .trig = Eq.trig

Trivial : ∀ {ℓ} → Set ℓ → Setoid ℓ 0ℓ
Trivial A .Carrier = A
Trivial A ._≈_ _ _ = ⊤
Trivial A .refl = tt
Trivial A .trig _ _ = tt

infixr 0 _⇒_
_⇒_ : ∀ {a b r s} (A : Setoid a r) (B : Setoid b s) → Setoid (a ⊔ b ⊔ r ⊔ s) (a ⊔ s)
A ⇒ B = A⇒B
  where
    module B = Setoid B

    A⇒B : Setoid _ _
    A⇒B .Carrier = A ⟶ B
    A⇒B ._≈_ f g = ∀ x → func f x B.≈ func g x
    A⇒B .refl _ = B.refl
    A⇒B .trig g≈f g≈h x = B.trig (g≈f x) (g≈h x)
    
-- Lift : ∀ {a r} b s → Setoid a r → Setoid (a ⊔ b) (r ⊔ s)
-- Lift b s A = record
--   { Carrier = Set.Lift b Carrier
--   ; _≈_ = λ x y → Set.Lift s (Set.lower x ≈ Set.lower y)
--   ; refl = Set.lift refl
--   ; trig = λ y≈x y≈z → Set.lift (trig (Set.lower y≈x) (Set.lower y≈z))
--   }
--   where open Setoid A

private
  variable
    a b c r s t : Level
    A : Setoid a r
    B : Setoid b s
    C : Setoid c t

-- lift : A ⟶ Lift b s A
-- lift = record
--   { func = Set.lift
--   ; cong = Set.lift
--   }

-- lower : Lift b s A ⟶ A
-- lower = record
--   { func = Set.lower
--   ; cong = Set.lower
--   }

const : A ⟶ B ⇒ A
const .func x .func _ = x
const {A = A} .func _ .cong _ = A .refl
const .cong x≈y _ = x≈y

ap : (A ⇒ B ⇒ C) ⟶ (A ⇒ B) ⇒ A ⇒ C
ap .func f .func g .func x = f ⟨$⟩ x ⟨$⟩ (g ⟨$⟩ x)
ap {C = C} .func f .func g .cong {x} {y} x≈y =
  let module C = Setoid C
      open Relation.Reasoning C._≈_
      open Equiv C.refl C.trig
  in f ⟨$⟩ x ⟨$⟩ (g ⟨$⟩ x) ≈⟨ f ⟨$⟩ x ~$~ g ~$~ x≈y ⟩
     f ⟨$⟩ x ⟨$⟩ (g ⟨$⟩ y) ≈⟨ (f ~$~ x≈y) _ ⟩
     f ⟨$⟩ y ⟨$⟩ (g ⟨$⟩ y) ∎
ap .func f .cong g≈h x = f ⟨$⟩ x ~$~ g≈h x
ap .cong f≈g _ x = f≈g x _

infixl 8 _ˢ_
_ˢ_ : (A ⟶ B ⇒ C) → (A ⟶ B) → A ⟶ C
f ˢ g = ap ⟨$⟩ f ⟨$⟩ g

id : A ⟶ A
id .func x = x
id .cong x≈y = x≈y

compose : (B ⇒ C) ⟶ (A ⇒ B) ⇒ A ⇒ C
compose = (const ⟨$⟩ ap) ˢ const

infixr 9 _∘_
_∘_ : (B ⟶ C) → (A ⟶ B) → A ⟶ C
f ∘ g = compose ⟨$⟩ f ⟨$⟩ g

flip : (A ⇒ B ⇒ C) ⟶ B ⇒ A ⇒ C
flip = compose ∘ ap ˢ (const ⟨$⟩ const)

infixr -1 λ→_-_
λ→_-_ : (A ⟶ B ⇒ C) → Setoid.Carrier B → A ⟶ C
λ→ f - y = flip ⟨$⟩ f ⟨$⟩ y
