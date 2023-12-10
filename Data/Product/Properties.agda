{-# OPTIONS --without-K --safe #-}

module Data.Product.Properties where

open import Level
open import Data.Product.Base
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

,-injective : {w x : A} {y z : B} → (w , y) ≡ (x , z) → w ≡ x × y ≡ z
,-injective refl = refl , refl

,-injectiveˡ : {w x : A} {y z : B} → (w , y) ≡ (x , z) → w ≡ x
,-injectiveˡ refl = refl

,-injectiveʳ : {w x : A} {y z : B} → (w , y) ≡ (x , z) → y ≡ z
,-injectiveʳ refl = refl

<⋆>-cong : {f g : A → B} {h i : A → C} → f ≗ g → h ≗ i → < f ⋆ h > ≗ < g ⋆ i >
<⋆>-cong f≗g h≗i x = cong₂ _,_ (f≗g x) (h≗i x)

<⋆>-congˡ : {f g : A → B} {h : A → C} → f ≗ g → < f ⋆ h > ≗ < g ⋆ h >
<⋆>-congˡ f≗g x = (_, _) =$= f≗g x

<⋆>-congʳ : {f : A → B} {h i : A → C} → h ≗ i → < f ⋆ h > ≗ < f ⋆ i >
<⋆>-congʳ h≗i x = (_ ,_) =$= h≗i x

<⋆>-∘ : (f : B → C) (g : B → D) (h : A → B) → < f ⋆ g > ∘ h ≡ < f ∘ h ⋆ g ∘ h >
<⋆>-∘ _ _ _ = refl

<⋆>-proj₁ : (f : A → B) (g : A → C) → proj₁ ∘ < f ⋆ g > ≡ f
<⋆>-proj₁ _ _ = refl

<⋆>-proj₂ : (f : A → B) (g : A → C) → proj₂ ∘ < f ⋆ g > ≡ g
<⋆>-proj₂ _ _ = refl

map-cong : {f g : A → B} {h i : C → D} → f ≗ g → h ≗ i → map f h ≗ map g i
map-cong f≗g h≗i (x , y) = cong₂ _,_ (f≗g x) (h≗i y)

map-congˡ : {f g : A → B} {h : C → D} → f ≗ g → map f h ≗ map g h
map-congˡ f≗g (x , _) = (_, _) =$= f≗g x

map-congʳ : {f : A → B} {h i : C → D} → h ≗ i → map f h ≗ map f i
map-congʳ h≗i (_ , y) = (_ ,_) =$= h≗i y

map-∘ : (f : B → C) (g : A → B) (h : E → F) (i : D → E) → map (f ∘ g) (h ∘ i) ≡ map f h ∘ map g i
map-∘ _ _ _ _ = refl

map-id : map id id ≡ id {A = A × B}
map-id = refl

×-functor : ∀ {a b} → Functor (SetCat a) (FunCat (SetCat b) (SetCat (a ⊔ b)))
×-functor .obj A .obj = A ×_
×-functor .obj _ .hom .func = map id
×-functor .obj _ .hom .cong = map-congʳ
×-functor .obj _ .mor-∘ _ _ _ = refl
×-functor .obj _ .mor-id _ = refl
×-functor .hom .func f .at _ = map f id
×-functor .hom .func _ .isNatural _ _ = refl
×-functor .hom .cong f≈g _ = map-congˡ f≈g
×-functor .mor-∘ _ _ _ _ = refl
×-functor .mor-id _ _ = refl

×-functorʳ : ∀ {a} b → Set a → Functor (SetCat b) (SetCat (a ⊔ b))
×-functorʳ _ = ×-functor <$>_

×-functorˡ : ∀ a {b} → Set b → Functor (SetCat a) (SetCat (a ⊔ b))
×-functorˡ _ = Λ ×-functor -_

proj₁-natural : ∀ a {b} (B : Set b) → ×-functorˡ a B ⇉ LiftFunctor b
proj₁-natural _ _ .at _ = lift ∘ proj₁
proj₁-natural _ _ .isNatural _ _ = refl

proj₂-natural : ∀ {a} b (A : Set a) → ×-functorʳ b A ⇉ LiftFunctor a
proj₂-natural _ _ .at _ = lift ∘ proj₂
proj₂-natural _ _ .isNatural _ _ = refl
