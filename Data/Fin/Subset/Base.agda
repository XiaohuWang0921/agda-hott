{-# OPTIONS --without-K --safe #-}

module Data.Fin.Subset.Base where

open import Data.Nat.Base hiding (_≤_; _≤?_)
open import Data.Fin.Base
--open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Bool.Base hiding (_≟_)
open import Relation.Core
open import Level
open import Universe.Set
open import Algebra.Core
open import Data.Product.Base
open import Relation.Equality.Base

private
  variable
    k l m n : ℕ

inc : Bool → Op₁ ℕ
inc false = id
inc true = suc

infixr 5 _∷_
data CSet : ℕ → ℕ → Set where
  [] : CSet 0 0
  _∷_ : ∀ b → CSet k l → CSet (suc k) (inc b l)

infix 4 _∼_
_∼_ : CSet k l → CSet k m → Set
_∼_ {_} {l} {m} s t = Σ (l ≡ m) ((_≡ t) ∘ flip iresp s)

Subset : ℕ → Set
Subset n = Σ ℕ (CSet n)

infixr 5 _∺_
_∺_ : Bool → Subset k → Subset (suc k)
b ∺ s = mapp (inc b) (b ∷_) s

-- toVec : CSet k l → Vec Bool k
-- toVec [] = []
-- toVec (b ∷ s) = b ∷ toVec s

-- fromVec : Vec Bool k → Subset k
-- fromVec [] = 0 , []
-- fromVec (b ∷ v) = mapp (inc b) (b ∷_) (fromVec v)

zipWith : Op₂ Bool → CSet k l → CSet k m → Subset k
zipWith _ [] [] = 0 , []
zipWith _⊕_ (b ∷ s) (c ∷ t) = b ⊕ c ∺ zipWith _⊕_ s t

tabulate : (Fin k → Bool) → Subset k
tabulate {0} _ = 0 , []
tabulate {suc _} f = f zero ∺ tabulate (f ∘ suc)

infixl 0 _∋?_
_∋?_ : CSet k l → Fin k → Bool
b ∷ _ ∋? zero = b
_ ∷ s ∋? suc i = s ∋? i

infix 4 _⊂_ _⊂?_ _⊆_ _⊆?_

data _⊂_ : CSet k l → CSet k m → Set where
  [] : [] ⊂ []
  _∷_ : ∀ {b c} {s : CSet k l} {t : CSet k m} → b ≤ c → s ⊂ t → b ∷ s ⊂ c ∷ t

_⊂?_ : CSet k l → CSet k m → Bool
[] ⊂? [] = true
b ∷ s ⊂? c ∷ t = (b ≤? c) ∧ (s ⊂? t)

_⊆_ : ∀ {n} → Rel (Subset n) 0ℓ
s ⊆ t = s .proj₂ ⊂ t .proj₂

_⊆?_ : ∀ {n} → Subset n → Subset n → Bool
s ⊆? t = s .proj₂ ⊂? t .proj₂

full : ∀ n → CSet n n
full 0 = []
full (suc n) = true ∷ full n

empty : ∀ n → CSet n 0
empty 0 = []
empty (suc n) = false ∷ empty n

infixr 7 _∩_
infixr 6 _∪_

_∩_ : CSet k l → CSet k m → Subset k
_∩_ = zipWith _∧_

_∪_ : CSet k l → CSet k m → Subset k
_∪_ = zipWith _∨_

embed : {s : CSet k l} {t : CSet k m} → s ⊂ t → Fin l → Fin m
embed [] = id
embed (b≤b {false} ∷ s⊆t) = embed s⊆t
embed (b≤b {true} ∷ s⊆t) = id ∣ embed s⊆t
embed (f≤t ∷ s⊆t) = suc ∘ embed s⊆t

single : Fin k → CSet k 1
single zero = true ∷ empty _
single (suc i) = false ∷ single i

antisingle : Fin k → CSet k (pred k)
antisingle zero = false ∷ full _
antisingle {suc (suc _)} (suc i) = true ∷ antisingle i

preimage : (Fin k → Fin l) → CSet l m → Subset k
preimage f s = tabulate ((s ∋?_) ∘ f)

image : (Fin k → Fin l) → CSet k m → Subset l
image _ [] = 0 , empty _
image f (false ∷ s) = image (f ∘ suc) s
image f (true ∷ s) = (single (f zero)) ∪ image (f ∘ suc) s .proj₂

subsub : CSet k l → CSet l m → CSet k m
subsub [] t = t
subsub (false ∷ s) t = false ∷ subsub s t
subsub (true ∷ s) (b ∷ t) = b ∷ subsub s t

except : CSet k l → Fin l → CSet k (pred l)
except s i = subsub s (antisingle i)
