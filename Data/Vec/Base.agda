{-# OPTIONS --without-K --safe #-}

module Data.Vec.Base where

open import Data.Nat.Base
open import Data.Fin.Base
open import Level
open import Universe.Set

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c
    n : ℕ

Vec : Set a → ℕ → Set a
Vec A n = Fin n → A

[] : Vec A 0
[] ()

infixr 5 _∷_
_∷_ : A → Vec A n → Vec A (suc n)
(x ∷ _) zero = x
(_ ∷ xs) (suc n) = xs n

head : Vec A (suc n) → A
head = _$ zero

tail : Vec A (suc n) → Vec A n
tail = _∘ suc

map : (A → B) → Vec A n → Vec B n
map = _∘_

zipWith : (A → B → C) → Vec A n → Vec B n → Vec C n
zipWith = (_ˢ_ ∘_) ∘ _∘_

foldl : (B → A → B) → Vec A n → B → B
foldl {n = zero} _ _ = id
foldl {n = suc _} f xs y = foldl f (tail xs) (f y (head xs))

foldr : (A → B → B) → Vec A n → B → B
foldr {n = zero} _ _ = id
foldr {n = suc _} f xs = f (head xs) ∘ foldr f (tail xs)

Pointwise : (A → B → Set c) → Vec A n → Vec B n → Set c
Pointwise _~_ xs ys = ∀ i → xs i ~ ys i
