{-# OPTIONS --without-K --safe #-}

module Relation.Equality.Base where

open import Relation.Core
open import Relation.Equality.Core public
open import Level
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

IJ : {P : ∀ {w} → x ≡ w → Set b} (q : x ≡ y) → P refl → P q
IJ refl pr = pr

J : (P : ∀ {w} → x ≡ w → Set b) (q : x ≡ y) → P refl → P q
J _ refl pr = pr

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

ipser : {P : A → Set b} → x ≡ y → P y → P x
ipser refl py = py

iresp₂ : {_~_ : A → B → Set c} → x ≡ y → u ≡ v → x ~ u → y ~ v
iresp₂ refl refl x~u = x~u

ipser₂ : {_~_ : A → B → Set c} → x ≡ y → u ≡ v → y ~ v → x ~ u
ipser₂ refl refl y~v = y~v

resp : (P : A → Set b) → x ≡ y → P x → P y
resp _ = iresp

pser : (P : A → Set b) → x ≡ y → P y → P x
pser _ = ipser

resp₂ : (_~_ : A → B → Set c) → x ≡ y → u ≡ v → x ~ u → y ~ v
resp₂ _ = iresp₂

pser₂ : (_~_ : A → B → Set c) → x ≡ y → u ≡ v → y ~ v → x ~ u
pser₂ _ = ipser₂

infixr 4.5 _=$=_
_=$=_ = cong
