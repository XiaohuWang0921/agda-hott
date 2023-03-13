-- Inductive representation of order-preserving finite functions.

{-# OPTIONS --without-K --safe #-}

module HoTT.OFF where

open import Level hiding (zero; suc)
open import Data.Nat.Base hiding (_≤_)
open import Data.Fin.Base hiding (_+_)
open import Data.Nat.Properties
open import Relation.Binary.Core
open import HoTT.EqNotation
open import Function.Base hiding (id; _∘_)
open import Data.Product

private
  variable
    i j k l m n : ℕ

data OFF : Rel ℕ 0ℓ where

  [] : OFF 0 0

  n∷_ : OFF m n → OFF m (suc n)

  a∷_ : OFF m (suc n) → OFF (suc m) (suc n)

subsf : k ≡ m → l ≡ n → OFF k l → OFF m n
subsf = subst₂ OFF

subsf₁ : k ≡ m → OFF k n → OFF m n
subsf₁ = flip subsf refl

subsf₂ : l ≡ n → OFF k l → OFF k n
subsf₂ = subsf refl

infixr 5 _$$_
_$$_ : OFF m n → Fin m → Fin n
[] $$ i = i
n∷ f $$ i = suc (f $$ i)
a∷ f $$ zero = zero
a∷ f $$ suc i = f $$ i

id : OFF n n
id {zero} = []
id {suc _} = a∷ n∷ id

infixr 9 _∘_
_∘_ : OFF m n → OFF l m → OFF l n
[] ∘ g = g
n∷ f ∘ g = n∷ (f ∘ g)
a∷ f ∘ n∷ g = f ∘ g
f @ (a∷ _) ∘ a∷ g = a∷ (f ∘ g)

infixr 5 _∷_
_∷_ : ∀ i → OFF m (n ℕ-ℕ inject₁ i) → OFF (suc m) n
zero ∷ f = a∷ f
suc i ∷ f = n∷ (i ∷ f)

shrink : ∀ i j → .(i ≤ j) → Fin (n ℕ-ℕ inject₁ i)
shrink zero j _ = j
shrink (suc i) (suc j) si≤sj = shrink i j (≤-pred si≤sj)

infixl 6 _⊕_
_⊕_ : ∀ i → Fin (n ℕ-ℕ inject₁ i) → Fin n
zero ⊕ j = j
suc i ⊕ j = suc (i ⊕ j)

shrink-≤ : ∀ (i j k : Fin n) i≤j j≤k → shrink i j i≤j ≤ shrink i k (≤-trans i≤j j≤k)
shrink-≤ zero _ _ _ j≤k = j≤k
shrink-≤ (suc i) (suc j) (suc k) (s≤s i≤j) (s≤s j≤k) = shrink-≤ i j k i≤j j≤k

empty : OFF 0 n
empty {zero} = []
empty {suc _} = n∷ empty

fromΠ : (f : Fin m → Fin n) → .(f Preserves _≤_ ⟶ _≤_) → OFF m n
fromΠ {zero} _ _ = empty
fromΠ {suc _} {zero} f = f zero |>′ λ ()
fromΠ {suc _} {suc _} f f-≤ =
  f zero ∷ fromΠ (λ i → shrink (f zero) (f (suc i)) (f-≤ z≤n))
                 (shrink-≤ (f zero) _ _ (f-≤ z≤n) ∘′ f-≤ ∘′ s≤s)

0th : OFF m (suc n)
0th {zero} = empty
0th {suc _} = a∷ 0th

pick : Fin n → OFF m n
pick zero = 0th
pick (suc i) = n∷ pick i

first : ∀ m → OFF m (m + n)
first zero = empty
first (suc m) = a∷ n∷ first m

stack : OFF k l → OFF m n → OFF (k + m) (l + n)
stack [] g = g
stack (n∷ f) g = n∷ stack f g
stack (a∷ f) g = a∷ stack f g

shiftˡ : ∀ l → OFF m n → OFF (l + m) (l + n)
shiftˡ _ = stack id

shiftʳ : ∀ n → OFF l m → OFF (l + n) (m + n)
shiftʳ _ = flip stack id

embed₁ : Fin n → OFF m (m * n)
embed₁ {m = zero} _ = empty
embed₁ {m = suc _} i = stack (pick {m = 1} i) (embed₁ i)

embed₂ : Fin m → OFF n (m * n)
embed₂ zero = first _
embed₂ (suc i) = stack empty (embed₂ i)

infixr 7 _ℕ*_
_ℕ*_ : ∀ l → OFF m n → OFF (l * m) (l * n)
zero ℕ* f = []
suc l ℕ* f = stack f (l ℕ* f)

skip : Fin (suc n) → OFF n (suc n)
skip zero = n∷ id
skip {suc _} (suc i) = a∷ n∷ skip i

switch : Fin n → Fin (suc n) → Fin n × Fin (suc n)
switch {suc _} i zero = zero , suc i
switch zero (suc j) = j , zero
switch (suc i) (suc j) = map suc suc (switch i j)
