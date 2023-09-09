{-# OPTIONS --without-K --safe #-}

module Universe.Type where

open import Level

Type : ∀ ℓ → Set (ℓsuc ℓ)
Type ℓ = Set ℓ

record Lift {a} b (A : Type a) : Type (a ⊔ b) where
  constructor lift
  field
    lower : A

open Lift public

private
  variable
    a b c : Level
    A : Type a
    B : Type b
    C : Type c

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

flip : (A → B → C) → B → A → C
flip = (_∘ const) ∘ _ˢ_
{-# INLINE flip #-}
