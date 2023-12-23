{-# OPTIONS --without-K --safe #-}

module Data.Vec.Base where

open import Data.Nat.Base
open import Data.Fin.Base hiding (cast; tsac)
open import Level
open import Universe.Set
open import Relation.Equality.Base
open import Data.Nat.Properties
open import Data.Unit.Core
open import Data.Product.Base using (_×_)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c
    n : ℕ

infixr 5 _∷_
data Vec (A : Set a) : ℕ → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

cast : ∀ {m n} → .(m ≡ n) → Vec A m → Vec A n
cast {m = zero} {zero} _ [] = []
cast {m = suc _} {suc _} sm≡sn (x ∷ xs) = x ∷ cast (suc-injective sm≡sn) xs

tsac : ∀ {m n} → .(m ≡ n) → Vec A n → Vec A m
tsac m≡n = cast (sym m≡n)

-- head : Vec A (suc n) → A
-- head = _$ zero

-- tail : Vec A (suc n) → Vec A n
-- tail = _∘ suc

map : (A → B) → Vec A n → Vec B n
map _ [] = []
map f (x ∷ xs) = f x ∷ map f xs

zipWith : (A → B → C) → Vec A n → Vec B n → Vec C n
zipWith _ [] [] = []
zipWith _⊕_ (x ∷ xs) (y ∷ ys) = x ⊕ y ∷ zipWith _⊕_ xs ys

foldl : (B → A → B) → Vec A n → B → B
foldl _ [] = id
foldl f (x ∷ xs) y = foldl f xs (f y x)

foldr : (A → B → B) → Vec A n → B → B
foldr _ [] = id
foldr f (x ∷ xs) = f x ∘ foldr f xs

repeat : ∀ n → A → Vec A n
repeat 0 _ = []
repeat (suc n) x = x ∷ repeat n x

tabulate : (Fin n → A) → Vec A n
tabulate {n = zero} _ = []
tabulate {n = suc _} f = f zero ∷ tabulate (f ∘ suc)

lookup : Vec A n → Fin n → A
lookup (x ∷ _) zero = x
lookup (_ ∷ xs) (suc i) = lookup xs i

data Pointwise {A : Set a} {B : Set b} (_~_ : A → B → Set c) : Vec A n → Vec B n → Set (a ⊔ b ⊔ c) where
  [] : Pointwise _~_ [] []
  _∷_ : ∀ {x y} {xs : Vec A n} {ys} → x ~ y → Pointwise _~_ xs ys → Pointwise _~_ (x ∷ xs) (y ∷ ys)

data All {A : Set a} (P : A → Set b) : Vec A n → Set (a ⊔ b) where
  [] : All P []
  _∷_ : ∀ {x} {xs : Vec A n} → P x → All P xs → All P (x ∷ xs)

data Any {A : Set a} (P : A → Set b) : Vec A n → Set (a ⊔ b) where
  here : ∀ {x} {xs : Vec A n} → P x → Any P (x ∷ xs)
  there : ∀ {x} {xs : Vec A n} → Any P xs → Any P (x ∷ xs)
