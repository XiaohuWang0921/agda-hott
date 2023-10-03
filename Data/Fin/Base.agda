{-# OPTIONS --without-K --safe #-}

module Data.Fin.Base where

open import Data.Nat.Base
open import Data.Sum.Base as Sum
open import Data.Product.Base as Product
open import Universe.Set
open import Universe.Set.Categorical
open import Category.Base
open import Relation.Equality.Base
open import Data.Empty.Base

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)

FinCat : Category _ _ _
FinCat = FullSub category Fin

infixr 6 _ℕ+_
_ℕ+_ : ∀ m {n} → Fin n → Fin (m + n)
_ℕ+_ zero = id
_ℕ+_ (suc m) = suc ∘ (m ℕ+_)

inj+ : ∀ {m} n → Fin m → Fin (m + n)
inj+ _ zero = zero
inj+ n (suc i) = suc (inj+ n i)

join : ∀ {m n} → Fin m ⊎ Fin n → Fin (m + n)
join = < inj+ _ ⊹ _ ℕ+_ >

splitAt : ∀ m {n} → Fin (m + n) → Fin m ⊎ Fin n
splitAt 0 = inj₂
splitAt (suc _) zero = inj₁ zero
splitAt (suc m) (suc i) = Sum.map suc (λ j → j) (splitAt m i)

combine : ∀ {m n} → Fin m → Fin n → Fin (m * n)
combine zero j = inj+ _ j
combine (suc i) j = _ ℕ+ combine i j

extract : ∀ m {n} → Fin (m * n) → Fin m × Fin n
extract (suc m) i = < zero ,_ ⊹ Product.map suc id ∘ extract m > (splitAt _ i)

private
  variable
    k l m n : ℕ

infixr 5 _++_
_++_ : (Fin l → Fin n) → (Fin m → Fin n) → Fin (l + m) → Fin n
f ++ g = < f ⊹ g > ∘ splitAt _

infixr 6 _**_
_**_ : (Fin l → Fin m) → (Fin l → Fin n) → Fin l → Fin (m * n)
(f ** g) i = combine (f i) (g i)

infixr 5 _∣_
_∣_ : (Fin k → Fin m) → (Fin l → Fin n) → Fin (k + l) → Fin (m + n)
f ∣ g = join ∘ Sum.map f g ∘ splitAt _

infixr 6 _∙_
_∙_ : (Fin k → Fin m) → (Fin l → Fin n) → Fin (k * l) → Fin (m * n)
f ∙ g = uncurry combine ∘ Product.map f g ∘ extract _

initial : ∀ {a} {A : Set a} → Fin 0 → A
initial ()

terminal : ∀ {a} {A : Set a} → A → Fin 1
terminal _ = zero

punchOut : {i j : Fin (suc n)} → .(i ≢ j) → Fin n
punchOut {_} {zero} {zero} 0≢0 = ⊥-elim (0≢0 refl)
punchOut {suc _} {zero} {suc j} _ = j
punchOut {suc _} {suc _} {zero} _ = zero
punchOut {suc _} {suc _} {suc _} si≢sj = suc (punchOut (si≢sj ∘ cong suc))

swap : Fin (suc n) → Fin n → Fin (suc n) × Fin n
swap {suc _} zero j = suc j , zero
swap (suc i) zero = zero , i
swap (suc i) (suc j) = Product.map suc suc (swap i j)

punchIn : Fin (suc n) → Fin n → Fin (suc n)
punchIn i j = proj₁ (swap i j)

pinch : Fin n → Fin (suc n) → Fin n
pinch i j = proj₂ (swap j i)
