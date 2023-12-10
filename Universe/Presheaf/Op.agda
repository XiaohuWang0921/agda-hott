{-# OPTIONS --without-K --safe #-}

module Universe.Presheaf.Op where

open import Level hiding (_ℕ+_)
open import Universe.Presheaf.Base hiding (_∘_)
open import Data.Fin.Properties
open import Category.Functor
open import Data.Nat.Base

private
  variable
    a r : Level

infixr 6 _ℕ+_
_ℕ+_ : ℕ → Presheaf a r → Presheaf a r
n ℕ+ P = P ∘ Opposite (+-functorˡ n)

infixl 6 _+ℕ_
_+ℕ_ : Presheaf a r → ℕ → Presheaf a r
P +ℕ n = P ∘ Opposite (+-functorʳ n)

infixr 7 _ℕ*_
_ℕ*_ : ℕ → Presheaf a r → Presheaf a r
n ℕ* P = P ∘ Opposite (*-functorˡ n)

infixl 6 _*ℕ_
_*ℕ_ : Presheaf a r → ℕ → Presheaf a r
P *ℕ n = P ∘ Opposite (*-functorʳ n)

