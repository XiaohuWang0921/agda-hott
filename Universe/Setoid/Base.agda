{-# OPTIONS --without-K --safe #-}

module Universe.Setoid.Base where

open import Level
open import Relation.Core
open import Relation.Equality.Core as Eq using (_≡_)
open import Universe.Type as T using ()
import Relation.Reasoning

record Setoid a r : Set (ℓsuc (a ⊔ r)) where

  field
    Carrier : Set a
    _≈_ : Rel Carrier r
    refl : ∀ {x} → x ≈ x
    trig : ∀ {x y z} → y ≈ x → y ≈ z → x ≈ z

  reflexive : ∀ {x y} → x ≡ y → x ≈ y
  reflexive Eq.refl = refl

  sym : ∀ {x y} → x ≈ y → y ≈ x
  sym x≈y = trig x≈y refl

  trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
  trans x≈y y≈z = trig (sym x≈y) y≈z

infixr 0 _⟶_
record _⟶_ {a b r s} (A : Setoid a r) (B : Setoid b s) : Set (a ⊔ b ⊔ r ⊔ s) where

  private
    instance
      setoidA = A
      setoidB = B
      
    open Setoid {{...}}

  field
    func : Setoid.Carrier A → Setoid.Carrier B
    cong : ∀ {x y} → x ≈ y → func x ≈ func y

infixl 5 _⟨$⟩_
_⟨$⟩_ = _⟶_.func

infixl 5 _~$~_
_~$~_ = _⟶_.cong

infixr 0 _⇒_
_⇒_ : ∀ {a b r s} (A : Setoid a r) (B : Setoid b s) → Setoid (a ⊔ b ⊔ r ⊔ s) (a ⊔ s)
A ⇒ B = record
  { Carrier = A ⟶ B
  ; _≈_ = λ f g → ∀ {x} → func f x ≈ func g x
  ; refl = refl
  ; trig = λ g≈f g≈h → trig g≈f g≈h
  }
  where open _⟶_
        open Setoid B

Lift : ∀ {a r} b s → Setoid a r → Setoid (a ⊔ b) (r ⊔ s)
Lift b s A = record
  { Carrier = T.Lift b Carrier
  ; _≈_ = λ x y → T.Lift s (x .T.lower ≈ y .T.lower)
  ; refl = T.lift refl
  ; trig = λ y≈x y≈z → T.lift (trig (y≈x .T.lower) (y≈z .T.lower))
  }
  where open Setoid A

private
  variable
    a b c r s t : Level
    A : Setoid a r
    B : Setoid b s
    C : Setoid c t

lift : A ⟶ Lift b s A
lift = record
  { func = T.lift
  ; cong = T.lift
  }

lower : Lift b s A ⟶ A
lower = record
  { func = T.lower
  ; cong = T.lower
  }

const : A ⟶ B ⇒ A
const {A = A} = record
  { func = λ x → record
    { func = λ _ → x
    ; cong = λ _ → refl }
  ; cong = λ x≈y → x≈y }
  where open Setoid A

ap : (A ⇒ B ⇒ C) ⟶ (A ⇒ B) ⇒ A ⇒ C
ap {C = C} = record
  { func = λ f → record
    { func = λ g → record
      { func = λ x → f ⟨$⟩ x ⟨$⟩ (g ⟨$⟩ x)
      ; cong = λ {x} {y} x≈y →
        let open Setoid C
            open Relation.Reasoning _≈_
            open Equiv refl trig
        in f ⟨$⟩ x ⟨$⟩ (g ⟨$⟩ x) ≈⟨ f ⟨$⟩ x ~$~ (g ~$~ x≈y) ⟩
           f ⟨$⟩ x ⟨$⟩ (g ⟨$⟩ y) ≈⟨ f ~$~ x≈y ⟩
           f ⟨$⟩ y ⟨$⟩ (g ⟨$⟩ y) ∎ }
    ; cong = λ g≈h {x} → f ⟨$⟩ x ~$~ g≈h
    }
  ; cong = λ f≈g → f≈g
  }

infixl 8 _ˢ_
_ˢ_ : (A ⟶ B ⇒ C) → (A ⟶ B) → A ⟶ C
f ˢ g = ap ⟨$⟩ f ⟨$⟩ g

id : A ⟶ A
id = record
  { func = λ x → x
  ; cong = λ x≈y → x≈y
  }

compose : (B ⇒ C) ⟶ (A ⇒ B) ⇒ A ⇒ C
compose = (const ⟨$⟩ ap) ˢ const

infixr 9 _∘_
_∘_ : (B ⟶ C) → (A ⟶ B) → A ⟶ C
f ∘ g = compose ⟨$⟩ f ⟨$⟩ g

flip : (A ⇒ B ⇒ C) ⟶ B ⇒ A ⇒ C
flip = compose ∘ ap ˢ (const ⟨$⟩ const)
