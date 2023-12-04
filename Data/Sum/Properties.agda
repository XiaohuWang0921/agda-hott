{-# OPTIONS --without-K --safe #-}

module Data.Sum.Properties where

open import Level
open import Data.Sum.Base
open import Universe.Set
open import Relation.Equality.Base hiding (cong)
open import Universe.Set.Categorical
open import Category.Functor hiding (_∘_)
open import Category.Natural hiding (id; _∘_)
open import Category.FunCat
open import Universe.Setoid using (func; cong)

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
map-cong f≗g h≗i = <⊹>-cong (λ x → inj₁ =$= f≗g x) (λ y → inj₂ =$= h≗i y)

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

⊎-functor : ∀ {a b} → Functor (SetCat a) (FunCat (SetCat b) (SetCat (a ⊔ b)))
⊎-functor .obj A .obj B = A ⊎ B
⊎-functor .obj _ .hom .func = map id
⊎-functor .obj _ .hom .cong = map-congʳ
⊎-functor .obj _ .mor-∘ = map-∘ id id
⊎-functor .obj _ .mor-id = map-id
⊎-functor .hom .func f .at _ = map f id
⊎-functor .hom .func _ .isNatural _ (inj₁ _) = refl
⊎-functor .hom .func _ .isNatural _ (inj₂ _) = refl
⊎-functor .hom .cong f≈g _ = map-congˡ f≈g
⊎-functor .mor-∘ f g _ = map-∘ f g id id
⊎-functor .mor-id _ = map-id

⊎-functorʳ : ∀ {a} b → Set a → Functor (SetCat b) (SetCat (a ⊔ b))
⊎-functorʳ _ = ⊎-functor <$>_

⊎-functorˡ : ∀ a {b} → Set b → Functor (SetCat a) (SetCat (a ⊔ b))
⊎-functorˡ _ = Λ ⊎-functor -_

inj₁-natural : ∀ a {b} (B : Set b) → LiftFunctor b ⇉ ⊎-functorˡ a B
inj₁-natural _ _ .at _ = inj₁ ∘ lower
inj₁-natural _ _ .isNatural _ _ = refl

inj₂-natural : ∀ {a} b (A : Set a) → LiftFunctor a ⇉ ⊎-functorʳ b A
inj₂-natural _ _ .at _ = inj₂ ∘ lower
inj₂-natural _ _ .isNatural _ _ = refl
