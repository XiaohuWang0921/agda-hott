{-# OPTIONS --without-K --safe #-}

module Data.Fin.Subset.Properties where

open import Data.Fin.Base
open import Data.Fin.Subset.Base
open import Data.Fin.Properties
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; 0≤n; s≤s)
open import Universe.Set
open import Relation.Equality.Base
open import Data.Unit.Core
open import Data.Bool.Base
open import Data.Vec.Base
open import Data.Bool.Properties as Boolₚ
open import Data.Nat.Properties as ℕₚ using (<⇒≤; <-suc; ≤-Cat)
open import Category.Base
open import Level
open import Category.Functor hiding (_∘_)

private
  variable
    m n : ℕ

⊆-tail : {s t : Subset (suc n)} → s ⊆ t → tail s ⊆ tail t
⊆-tail s⊆t i = s⊆t (suc i)

⊆?-Reflects-⊆ : (s t : Subset n) → (s ⊆? t) Reflects (s ⊆ t)
⊆?-Reflects-⊆ {zero} _ _ ()
⊆?-Reflects-⊆ {suc _} s t with head s ≤? head t | ≤?-Reflects-≤ (head s) (head t)
... | false | head-s≰head-t = λ s⊆t → head-s≰head-t (s⊆t zero)
... | true | head-s≤head-t with tail s ⊆? tail t | ⊆?-Reflects-⊆ (tail s) (tail t)
... | false | tail-s⊈tail-t = λ s⊆t → tail-s⊈tail-t (⊆-tail s⊆t)
... | true | tail-s⊆tail-t = λ where
  zero → head-s≤head-t
  (suc i) → tail-s⊆tail-t i

⊆?-⊆ˡ : {s t u : Subset n} → s ⊆ t → (t ⊆? u) ≤ (s ⊆? u)
⊆?-⊆ˡ {zero} _ = b≤b
⊆?-⊆ˡ {suc _} s⊆t = ∧-≤ (≤?-≤ˡ (s⊆t zero)) (⊆?-⊆ˡ (⊆-tail s⊆t))

⊆?-⊆ʳ : {s t u : Subset n} → t ⊆ u → (s ⊆? t) ≤ (s ⊆? u)
⊆?-⊆ʳ {zero} _ = b≤b
⊆?-⊆ʳ {suc _} t⊆u = ∧-≤ (≤?-≤ʳ (t⊆u zero)) (⊆?-⊆ʳ (⊆-tail t⊆u))

⊆-refl : {s : Subset n} → s ⊆ s
⊆-refl _ = ≤-refl

⊆-antisym : {s t : Subset n} → s ⊆ t → t ⊆ s → s ≗ t
⊆-antisym s⊆t t⊆s i = ≤-antisym (s⊆t i) (t⊆s i)

⊆-trans : {r s t : Subset n} → r ⊆ s → s ⊆ t → r ⊆ t
⊆-trans r⊆s s⊆t i = ≤-trans (r⊆s i) (s⊆t i)

⊆-full : {s : Subset n} → s ⊆ full n
⊆-full i = ≤-true

empty-⊆ : {s : Subset n} → empty n ⊆ s
empty-⊆ i = false-≤

∣∣-cong : {s t : Subset n} → s ≗ t → ∣ s ∣ ≡ ∣ t ∣
∣∣-cong {zero} _ = refl
∣∣-cong {suc _} {s} {t} s≗t with s zero | t zero | s≗t zero
... | false | false | _ = ∣∣-cong λ i → s≗t (suc i)
... | true | true | _ = suc =$= ∣∣-cong λ i → s≗t (suc i)

∣∣-⊆ : {s t : Subset n} → s ⊆ t → ∣ s ∣ ℕ.≤ ∣ t ∣
∣∣-⊆ {zero} _ = 0≤n
∣∣-⊆ {suc _} {s} {t} s⊆t with s zero | t zero | s⊆t zero
... | false | false | _ = ∣∣-⊆ λ i → s⊆t (suc i)
... | false | true | _ = ℕₚ.≤-trans (∣∣-⊆ (⊆-tail s⊆t)) (<⇒≤ <-suc)
... | true | true | _ = s≤s (∣∣-⊆ (⊆-tail s⊆t))

∣∣∘full : ∀ n → ∣ full n ∣ ≡ n
∣∣∘full zero = refl
∣∣∘full (suc n) = suc =$= ∣∣∘full n

∣∣∘empty : ∀ n → ∣ empty n ∣ ≡ 0
∣∣∘empty zero = refl
∣∣∘empty (suc n) = ∣∣∘empty n

∣∣∘singleton : ∣_∣ ∘ singleton {n} ≗ const 1
∣∣∘singleton {suc n} zero = suc =$= ∣∣∘empty n
∣∣∘singleton {suc _} (suc i) = ∣∣∘singleton i

⊆-Cat : ℕ → Category 0ℓ 0ℓ 0ℓ
⊆-Cat n = Preorder (_⊆_ {n}) ⊆-refl ⊆-trans

∣∣-functor : ∀ {n} → Functor (⊆-Cat n) ℕₚ.≤-Cat
∣∣-functor = record
  { obj = ∣_∣
  ; hom = record
    { func = ∣∣-⊆
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ _ _ → tt
  ; mor-id = tt
  }

⊆?-functorˡ : ∀ {n} → Subset n → Functor (⊆-Cat n) (Op Boolₚ.≤-Cat)
⊆?-functorˡ s = record
  { obj = _⊆? s
  ; hom = record
    { func = ⊆?-⊆ˡ
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ _ _ → tt
  ; mor-id = tt
  }

⊆?-functorʳ : ∀ {n} → Subset n → Functor (⊆-Cat n) (Boolₚ.≤-Cat)
⊆?-functorʳ s = record
  { obj = s ⊆?_
  ; hom = record
    { func = ⊆?-⊆ʳ
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ _ _ → tt
  ; mor-id = tt
  }
