{-# OPTIONS --without-K --safe #-}

module Data.Sum.Properties where

open import Level
open import Data.Sum.Base
open import Universe.Set
open import Relation.Equality.Base
open import Universe.Set.Categorical
open import Category.Functor hiding (_∘_)
open import Category.Natural hiding (id; _∘_)

private
  variable
    a b c d e f : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e
    F : Set f

<⊹>-cong : {f g : A → C} {h i : B → C} → f ≗ g → h ≗ i → < f ⊹ h > ≗ < g ⊹ i >
<⊹>-cong f≗g _ (inj₁ x) = f≗g x
<⊹>-cong _ h≗i (inj₂ y) = h≗i y

<⊹>-congˡ : {f g : A → C} {h : B → C} → f ≗ g → < f ⊹ h > ≗ < g ⊹ h >
<⊹>-congˡ f≗g = <⊹>-cong f≗g (λ _ → refl)

<⊹>-congʳ : {f : A → C} {h i : B → C} → h ≗ i → < f ⊹ h > ≗ < f ⊹ i >
<⊹>-congʳ h≗i = <⊹>-cong (λ _ → refl) h≗i

<⊹>-∘ : (f : C → D) (g : A → C) (h : B → C) → f ∘ < g ⊹ h > ≗ < f ∘ g ⊹ f ∘ h >
<⊹>-∘ _ _ _ (inj₁ _) = refl
<⊹>-∘ _ _ _ (inj₂ _) = refl

<⊹>-inj₁ : (f : A → C) (g : B → C) → < f ⊹ g > ∘ inj₁ ≡ f
<⊹>-inj₁ _ _ = refl

<⊹>-inj₂ : (f : A → C) (g : B → C) → < f ⊹ g > ∘ inj₂ ≡ g
<⊹>-inj₂ _ _ = refl

map-cong : {f g : A → B} {h i : C → D} → f ≗ g → h ≗ i → map f h ≗ map g i
map-cong f≗g h≗i = <⊹>-cong (λ x → cong inj₁ (f≗g x)) (λ y → cong inj₂ (h≗i y))

map-congˡ : {f g : A → B} {h : C → D} → f ≗ g → map f h ≗ map g h
map-congˡ f≗g = map-cong f≗g (λ _ → refl)

map-congʳ : {f : A → B} {h i : C → D} → h ≗ i → map f h ≗ map f i
map-congʳ h≗i = map-cong (λ _ → refl) h≗i

map-∘ : (f : B → C) (g : A → B) (h : E → F) (i : D → E) → map (f ∘ g) (h ∘ i) ≗ map f h ∘ map g i
map-∘ _ _ _ _ (inj₁ _) = refl
map-∘ _ _ _ _ (inj₂ _) = refl

map-id : map id id ≗ id {A = A ⊎ B}
map-id (inj₁ _) = refl
map-id (inj₂ _) = refl

⊎-functorˡ : ∀ {a b} → Set b → Functor (category {a}) (category {a ⊔ b})
⊎-functorˡ B = record
  { obj = _⊎ B
  ; hom = record
    { func = flip map id
    ; cong = map-congˡ
    }
  ; mor-∘ = λ f g → map-∘ f g id id
  ; mor-id = map-id
  }

⊎-functorʳ : ∀ {a b} → Set a → Functor (category {b}) (category {a ⊔ b})
⊎-functorʳ A = record
  { obj = A ⊎_
  ; hom = record
    { func = map id
    ; cong = map-congʳ
    }
  ; mor-∘ = λ f g → map-∘ id id f g
  ; mor-id = map-id
  }

⊎-naturalˡ : ∀ {a b} {A B : Set b} → (A → B) → ⊎-functorˡ {a} {b} A ⇉ ⊎-functorˡ B
⊎-naturalˡ f = record
  { at = λ _ → map id f
  ; isNatural = λ _ → λ where
    (inj₁ x) → refl
    (inj₂ y) → refl
  }

⊎-naturalʳ : ∀ {a b} {A B : Set a} → (A → B) → ⊎-functorʳ {a} {b} A ⇉ ⊎-functorʳ B
⊎-naturalʳ f = record
  { at = λ _ → map f id
  ; isNatural = λ _ → λ where
    (inj₁ x) → refl
    (inj₂ y) → refl
  }
