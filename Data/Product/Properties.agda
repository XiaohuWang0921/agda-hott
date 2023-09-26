{-# OPTIONS --without-K --safe #-}

module Data.Product.Properties where

open import Level
open import Data.Product.Base
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

<,>-cong : {f g : A → B} {h i : A → C} → f ≗ g → h ≗ i → < f , h > ≗ < g , i >
<,>-cong f≗g h≗i x = cong₂ _,_ (f≗g x) (h≗i x)

<,>-congˡ : {f g : A → B} {h : A → C} → f ≗ g → < f , h > ≗ < g , h >
<,>-congˡ f≗g x = (_, _) =$= f≗g x

<,>-congʳ : {f : A → B} {h i : A → C} → h ≗ i → < f , h > ≗ < f , i >
<,>-congʳ h≗i x = (_ ,_) =$= h≗i x

<,>-∘ : (f : B → C) (g : B → D) (h : A → B) → < f , g > ∘ h ≡ < f ∘ h , g ∘ h >
<,>-∘ _ _ _ = refl

<,>-proj₁ : (f : A → B) (g : A → C) → proj₁ ∘ < f , g > ≡ f
<,>-proj₁ _ _ = refl

<,>-proj₂ : (f : A → B) (g : A → C) → proj₂ ∘ < f , g > ≡ g
<,>-proj₂ _ _ = refl

map-cong : {f g : A → B} {h i : C → D} → f ≗ g → h ≗ i → map f h ≗ map g i
map-cong f≗g h≗i (x , y) = cong₂ _,_ (f≗g x) (h≗i y)

map-congˡ : {f g : A → B} {h : C → D} → f ≗ g → map f h ≗ map g h
map-congˡ f≗g (x , _) = (_, _) =$= f≗g x

map-congʳ : {f : A → B} {h i : C → D} → h ≗ i → map f h ≗ map f i
map-congʳ h≗i (_ , y) = (_ ,_) =$= h≗i y

map-∘ : (f : B → C) (g : A → B) (h : E → F) (i : D → E) → map (f ∘ g) (h ∘ i) ≡ map f h ∘ map g i
map-∘ _ _ _ _ = refl

map-id : map id id ≗ id {A = A × B}
map-id (_ , _) = refl

×-functorˡ : ∀ {a b} → Set b → Functor (category {a}) (category {a ⊔ b})
×-functorˡ B = record
  { obj = _× B
  ; hom = record
    { func = flip map id
    ; cong = map-congˡ
    }
  ; mor-∘ = λ _ _ _ → refl
  ; mor-id = map-id }

×-functorʳ : ∀ {a b} → Set a → Functor (category {b}) (category {a ⊔ b})
×-functorʳ A = record
  { obj = A ×_
  ; hom = record
    { func = map id
    ; cong = map-congʳ
    }
  ; mor-∘ = λ _ _ _ → refl
  ; mor-id = map-id }

×-naturalˡ : ∀ {a b} {A B : Set a} → (A → B) → ×-functorʳ {a} {b} A ⇉ ×-functorʳ B
×-naturalˡ f = record
  { at = λ _ → map f id
  ; isNatural = λ _ _ → refl
  }

×-naturalʳ : ∀ {a b} {A B : Set b} → (A → B) → ×-functorˡ {a} {b} A ⇉ ×-functorˡ B
×-naturalʳ f = record
  { at = λ _ → map id f
  ; isNatural = λ _ _ → refl
  }
