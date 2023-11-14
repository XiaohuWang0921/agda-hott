{-# OPTIONS --without-K --safe #-}

module Data.Bool.Properties where

open import Data.Bool.Base
open import Relation.Equality.Base
open import Universe.Set
open import Data.Empty.Base
open import Data.Unit.Core
open import Category.Base
open import Category.Functor hiding (_∘_)
open import Universe.Set.Categorical
open import Level

false≢true : false ≢ true
false≢true ()

id-Reflects-T : ∀ b → b Reflects T b
id-Reflects-T false = id
id-Reflects-T true = tt

≤?-Reflects-≤ : ∀ b c → (b ≤? c) Reflects (b ≤ c)
≤?-Reflects-≤ false false = b≤b
≤?-Reflects-≤ false true = f≤t
≤?-Reflects-≤ true true = b≤b

≟-Reflects-≡ : ∀ b c → (b ≟ c) Reflects (b ≡ c)
≟-Reflects-≡ false false = refl
≟-Reflects-≡ false true = false≢true
≟-Reflects-≡ true false = false≢true ∘ sym
≟-Reflects-≡ true true = refl

Reflects-true : ∀ {ℓ} {P : Set ℓ} b → b Reflects P → P → b ≡ true
Reflects-true false ¬p p = ⊥-elim (¬p p)
Reflects-true true _ _ = refl

Reflects-false : ∀ {ℓ} {P : Set ℓ} b → b Reflects P → (P → ⊥) → b ≡ false
Reflects-false false _ _ = refl
Reflects-false true p ¬p = ⊥-elim (¬p p)

≤-true : ∀ {b} → b ≤ true
≤-true {false} = f≤t
≤-true {true} = b≤b

false-≤ : ∀ {b} → false ≤ b
false-≤ {false} = b≤b
false-≤ {true} = f≤t

not-≤ : ∀ {a b} → a ≤ b → not b ≤ not a
not-≤ b≤b = b≤b
not-≤ f≤t = f≤t

T-≤ : ∀ {a b} → .(a ≤ b) → T a → T b
T-≤ {true} {true} _ _ = tt

≤?-≤ˡ : ∀ {a b c} → a ≤ b → (b ≤? c) ≤ (a ≤? c)
≤?-≤ˡ b≤b = b≤b
≤?-≤ˡ f≤t = ≤-true

≤?-≤ʳ : ∀ {a b c} → b ≤ c → (a ≤? b) ≤ (a ≤? c)
≤?-≤ʳ b≤b = b≤b
≤?-≤ʳ {false} f≤t = b≤b
≤?-≤ʳ {true} f≤t = f≤t

∧-≤ : ∀ {a b c d} → a ≤ b → c ≤ d → a ∧ c ≤ b ∧ d
∧-≤ {false} {false} _ _ = b≤b
∧-≤ {false} {true} _ _ = false-≤
∧-≤ {true} {true} _ = id

≤-refl : ∀ {b} → b ≤ b
≤-refl = b≤b

≡⇒≤ : ∀ {a b} → a ≡ b → a ≤ b
≡⇒≤ refl = ≤-refl

≤-antisym : ∀ {a b} → a ≤ b → b ≤ a → a ≡ b
≤-antisym b≤b _ = refl

≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans b≤b a≤c = a≤c
≤-trans f≤t b≤b = f≤t

≤-Cat : Category 0ℓ 0ℓ 0ℓ
≤-Cat = Preorder _≤_ ≤-refl ≤-trans

T-functor : Functor ≤-Cat (category {0ℓ})
T-functor = record
  { obj = T
  ; hom = record
    { func = λ a≤b → T-≤ a≤b
    ; cong = λ _ _ → refl
    }
  ; mor-∘ = λ where
    {true} {true} {true} _ _ _ → refl
  ; mor-id = λ where
    {true} tt → refl
  }

not-functor : Functor ≤-Cat (Op ≤-Cat)
not-functor = record
  { obj = not
  ; hom = record
    { func = not-≤
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ f g → tt
  ; mor-id = tt
  }

≤?-functorˡ : Bool → Functor ≤-Cat (Op ≤-Cat)
≤?-functorˡ b = record
  { obj = _≤? b
  ; hom = record
    { func = ≤?-≤ˡ
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ _ _ → tt
  ; mor-id = tt
  }

≤?-functorʳ : Bool → Functor ≤-Cat ≤-Cat
≤?-functorʳ b = record
  { obj = b ≤?_
  ; hom = record
    { func = ≤?-≤ʳ
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ _ _ → tt
  ; mor-id = tt
  }

∧-functorˡ : Bool → Functor ≤-Cat ≤-Cat
∧-functorˡ b = record
  { obj = _∧ b
  ; hom = record
    { func = flip ∧-≤ ≤-refl
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ _ _ → tt
  ; mor-id = tt
  }

∧-functorʳ : Bool → Functor ≤-Cat ≤-Cat
∧-functorʳ b = record
  { obj = b ∧_
  ; hom = record
    { func = ∧-≤ ≤-refl
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ _ _ → tt
  ; mor-id = tt
  }
