{-# OPTIONS --without-K --safe #-}

module Data.Fin.Base where

open import Data.Nat.Base
open import Data.Sum.Base as Sum
open import Data.Product.Base as Product

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)

infixr 6 _ℕ+_
_ℕ+_ : ∀ m {n} → Fin n → Fin (m + n)
zero ℕ+ i = i
suc m ℕ+ i = suc (m ℕ+ i)

inj+ : ∀ {m} n → Fin m → Fin (m + n)
inj+ _ zero = zero
inj+ n (suc i) = suc (inj+ n i)

join : ∀ {m n} → Fin m ⊎ Fin n → Fin (m + n)
join = ⟨ inj+ _ , _ ℕ+_ ⟩

splitAt : ∀ m {n} → Fin (m + n) → Fin m ⊎ Fin n
splitAt 0 = inj₂
splitAt (suc _) zero = inj₁ zero
splitAt (suc m) (suc i) = Sum.map suc (λ j → j) (splitAt m i)

combine : ∀ {m n} → Fin m → Fin n → Fin (m * n)
combine zero j = inj+ _ j
combine (suc i) j = _ ℕ+ combine i j

extract : ∀ m {n} → Fin (m * n) → Fin m × Fin n
extract (suc m) i = ⟨ zero ,_ , (λ j → Product.map suc (λ k → k) (extract m j)) ⟩ (splitAt _ i)

private
  variable
    k l m n : ℕ

infixr 5 _++_
_++_ : (Fin k → Fin m) → (Fin l → Fin n) → Fin (k + l) → Fin (m + n)
(f ++ g) i = join (Sum.map f g (splitAt _ i))

infixr 6 _**_
_**_ : (Fin k → Fin m) → (Fin l → Fin n) → Fin (k * l) → Fin (m * n)
(f ** g) i = uncurry combine (Product.map f g (extract _ i))

initial : ∀ {a} {A : Set a} → Fin 0 → A
initial ()

terminal : ∀ {a} {A : Set a} → A → Fin 1
terminal _ = zero

swap : Fin (suc n) → Fin n → Fin (suc n) × Fin n
swap {suc _} zero j = suc j , zero
swap (suc i) zero = zero , i
swap (suc i) (suc j) = Product.map suc suc (swap i j)

punch : Fin (suc n) → Fin n → Fin (suc n)
punch i j = proj₁ (swap i j)

pinch : Fin n → Fin (suc n) → Fin n
pinch i j = proj₂ (swap j i)
