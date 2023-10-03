{-# OPTIONS --without-K --safe #-}

module Relation.Equality.Base where

open import Relation.Core
open import Relation.Equality.Core public
open import Level
open import Universe.Setoid.Base
open import Data.Empty.Base

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c
    x y z : A
    u v : B

infix 4 _≢_
_≢_ : {A : Set a} → Rel A a
x ≢ y = x ≡ y → ⊥

trig : y ≡ x → y ≡ z → x ≡ z
trig refl p = p

sym : x ≡ y → y ≡ x
sym refl = refl

trans : x ≡ y → y ≡ z → x ≡ z
trans refl p = p

icong : {f : A → B} → x ≡ y → f x ≡ f y
icong refl = refl

icong₂ : {_∙_ : A → B → C} → x ≡ y → u ≡ v → x ∙ u ≡ y ∙ v
icong₂ refl refl = refl

cong : (f : A → B) → x ≡ y → f x ≡ f y
cong _ = icong

cong₂ : (_∙_ : A → B → C) → x ≡ y → u ≡ v → x ∙ u ≡ y ∙ v
cong₂ _ = icong₂

iresp : {P : A → Set b} → x ≡ y → P x → P y
iresp refl px = px

iresp₂ : {_~_ : A → B → Set c} → x ≡ y → u ≡ v → x ~ u → y ~ v
iresp₂ refl refl x~u = x~u

resp : (P : A → Set b) → x ≡ y → P x → P y
resp _ = iresp

resp₂ : (_~_ : A → B → Set c) → x ≡ y → u ≡ v → x ~ u → y ~ v
resp₂ _ = iresp₂

infixr 4.5 _=$=_
_=$=_ = cong

setoid : (A : Set a) → Setoid a a
setoid A = record
  { Carrier = A
  ; _≈_ = _≡_
  ; refl = refl
  ; trig = trig
  }
