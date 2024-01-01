{-# OPTIONS --without-K --safe #-}

module Data.Fin.Base where

open import Level hiding (_ℕ+_)
open import Data.Nat.Base hiding (_≤_; _≤?_; _≟_)
open import Data.Sum.Base as Sum
open import Data.Product.Base as Product
open import Universe.Set
open import Universe.Set.Categorical
open import Category.Base
open import Relation.Equality.Base
open import Data.Empty.Base
open import Data.Bool.Base hiding (_≟_)
open import Relation.Core
open import Algebra.Core
open import Category.FunCat
open import Data.Nat.Properties using (suc-injective)

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)

FinCat : Category _ _ _
FinCat = FullSub (SetCat 0ℓ) Fin

FinSucCat : Category _ _ _
FinSucCat = FullSub FinCat suc

cast : ∀ {m n} → .(m ≡ n) → Fin m → Fin n
cast {suc _} {suc _} _ zero = zero
cast {suc _} {suc _} sm≡sn (suc i) = suc (cast (suc-injective sm≡sn) i)

tsac : ∀ {m n} → .(m ≡ n) → Fin n → Fin m
tsac m≡n = cast (sym m≡n)

_≟_ : ∀ {n} → Fin n → Fin n → Bool
zero ≟ zero = true
suc m ≟ suc n = m ≟ n
_ ≟ _ = false

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

swap : Fin (suc n) → Fin n → Fin (suc n) × Fin n
swap {suc _} zero j = suc j , zero
swap (suc i) zero = zero , i
swap (suc i) (suc j) = Product.map suc suc (swap i j)

swap' : Fin n → Fin (n ∸ 1) → Fin n × Fin (n ∸ 1)
swap' {zero} = _,_
swap' {suc _} = swap

punchIn : Fin (suc n) → Fin n → Fin (suc n)
punchIn = proj₁ ∘₂ swap

pinch : Fin n → Fin (suc n) → Fin n
pinch = proj₂ ∘₂ flip swap

punchIn' : Fin n → Fin (n ∸ 1) → Fin n
punchIn' = proj₁ ∘₂ swap'

pinch' : Fin (pred n) → Fin n → Fin (pred n)
pinch' = proj₂ ∘₂ flip swap'
