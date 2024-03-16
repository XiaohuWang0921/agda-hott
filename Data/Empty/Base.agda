{-# OPTIONS --without-K --safe #-}

module Data.Empty.Base where

data ⊥ : Set where

⊥-elim : ∀ {ℓ} {A : Set ℓ} → ⊥ → A
⊥-elim ()
