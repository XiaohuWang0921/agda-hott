{-# OPTIONS --without-K --safe #-}

module Data.Product.Base where

open import Level
open import Data.Product.Core public

private
  variable
    a b c d : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

infixr 2 _×_
_×_ : Set a → Set b → Set (a ⊔ b)
A × B = Σ A (λ _ → B)

<_⋆_> : (A → B) → (A → C) → A → B × C
< f ⋆ g > x = f x , g x

map : (A → C) → (B → D) → A × B → C × D
map f g (x , y) = f x , g y

curry : (A × B → C) → A → B → C
curry f x y = f (x , y)

uncurry : (A → B → C) → A × B → C
uncurry f (x , y) = f x y
