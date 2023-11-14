{-# OPTIONS --without-K --safe #-}

module Universe.Set where

open import Level
open import Relation.Core
open import Universe.Setoid.Base
open import Relation.Equality.Base

record Lift {a} b (A : Set a) : Set (a ⊔ b) where
  constructor lift
  field
    lower : A

open Lift public

private
  variable
    a b c d : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

const : A → B → A
const = λ x _ → x
{-# INLINE const #-}

infixl 8 _ˢ_
_ˢ_ : (A → B → C) → (A → B) → A → C
_ˢ_ = λ f g x → f x (g x)
{-# INLINE _ˢ_ #-}

id : A → A
id = λ x → x
{-# INLINE id #-}

infixr 9 _∘_
_∘_ : (B → C) → (A → B) → A → C
_∘_ = const _ˢ_ ˢ const
{-# INLINE _∘_ #-}

infixr 9 _∘₂_
_∘₂_ : (C → D) → (A → B → C) → A → B → D
_∘₂_ = _∘_ ∘ _∘_

flip : (A → B → C) → B → A → C
flip = (_∘ const) ∘ _ˢ_
{-# INLINE flip #-}

infixr -1 _$_
_$_ : (A → B) → A → B
_$_ = id
{-# INLINE _$_ #-}

infixl 0 _|>_
_|>_ : A → (A → B) → B
_|>_ = flip _$_

infix 4 _≗_
_≗_ :  Rel (A → B) _
f ≗ g = ∀ x → f x ≡ g x

infix 4 _≗₂_
_≗₂_ : Rel (A → B → C) _
f ≗₂ g = ∀ x y → f x y ≡ g x y

infixr 0 _⇒_
_⇒_ : Set a → Set b → Setoid (a ⊔ b) (a ⊔ b)
A ⇒ B = record
  { Carrier = A → B
  ; _≈_ = _≗_
  ; refl = λ _ → refl
  ; trig = λ g≈f g≈h x → trig (g≈f x) (g≈h x)
  }
