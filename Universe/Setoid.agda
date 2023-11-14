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

infixl 5 _⟨$⟩_
_⟨$⟩_ = _⟶_.func

infixr 4.5 _~$~_
_~$~_ = _⟶_.cong

Eq : ∀ {ℓ} → Set ℓ → Setoid ℓ ℓ
Eq A = record
  { Carrier = A
  ; _≈_ = _≡_
  ; refl = Eq.refl
  ; trig = Eq.trig
  }

Trivial : ∀ {ℓ} → Set ℓ → Setoid ℓ 0ℓ
Trivial A = record
  { Carrier = A
  ; _≈_ = λ _ _ → ⊤
  ; refl = tt
  ; trig = λ _ _ → tt
  }

infixr 0 _⇒_
_⇒_ : ∀ {a b r s} (A : Setoid a r) (B : Setoid b s) → Setoid (a ⊔ b ⊔ r ⊔ s) (a ⊔ s)
A ⇒ B = record
  { Carrier = A ⟶ B
  ; _≈_ = λ f g → ∀ x → func f x ≈ func g x
  ; refl = λ _ → refl
  ; trig = λ g≈f g≈h x → trig (g≈f x) (g≈h x)
  }
  where open _⟶_
        open Setoid B

Lift : ∀ {a r} b s → Setoid a r → Setoid (a ⊔ b) (r ⊔ s)
Lift b s A = record
  { Carrier = Set.Lift b Carrier
  ; _≈_ = λ x y → Set.Lift s (Set.lower x ≈ Set.lower y)
  ; refl = Set.lift refl
  ; trig = λ y≈x y≈z → Set.lift (trig (Set.lower y≈x) (Set.lower y≈z))
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
  { func = Set.lift
  ; cong = Set.lift
  }

lower : Lift b s A ⟶ A
lower = record
  { func = Set.lower
  ; cong = Set.lower
  }

const : A ⟶ B ⇒ A
const {A = A} = record
  { func = λ x → record
    { func = λ _ → x
    ; cong = λ _ → refl }
  ; cong = λ x≈y _ → x≈y }
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
        in f ⟨$⟩ x ⟨$⟩ (g ⟨$⟩ x) ≈⟨ f ⟨$⟩ x ~$~ g ~$~ x≈y ⟩
           f ⟨$⟩ x ⟨$⟩ (g ⟨$⟩ y) ≈⟨ (f ~$~ x≈y) _ ⟩
           f ⟨$⟩ y ⟨$⟩ (g ⟨$⟩ y) ∎ }
    ; cong = λ g≈h x → f ⟨$⟩ x ~$~ g≈h x
    }
  ; cong = λ f≈g _ x → f≈g x _
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
