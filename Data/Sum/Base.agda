{-# OPTIONS --without-K --safe #-}

module Data.Sum.Base where

open import Level

private
  variable
    a b c d : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

infixr 1 _⊎_
data _⊎_ (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

⟨_,_⟩ : (A → C) → (B → C) → A ⊎ B → C
⟨ f , _ ⟩ (inj₁ x) = f x
⟨ _ , g ⟩ (inj₂ y) = g y

map : (A → C) → (B → D) → A ⊎ B → C ⊎ D
map f g = ⟨ (λ x → inj₁ (f x)) , (λ y → inj₂ (g y)) ⟩
