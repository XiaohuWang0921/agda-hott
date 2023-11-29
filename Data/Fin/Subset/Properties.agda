{-# OPTIONS --without-K --safe #-}

module Data.Fin.Subset.Properties where

open import Data.Fin.Base
open import Data.Fin.Subset.Base
open import Data.Fin.Properties
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; 0≤n; s≤s)
open import Universe.Set
open import Relation.Equality.Base
open import Data.Unit.Core
open import Data.Bool.Base hiding (_≟_)
open import Data.Vec.Base
open import Data.Bool.Properties as Boolₚ
open import Data.Nat.Properties as ℕₚ using (<⇒≤; <-suc; ≤-Cat)
open import Category.Base
open import Level
open import Category.Functor hiding (_∘_)
open import Data.Vec.Properties

private
  variable
    m n : ℕ

tail-⊆ : {s t : Subset (suc n)} → s ⊆ t → tail s ⊆ tail t
tail-⊆ s⊆t i = s⊆t (suc i)

⊆?-Reflects-⊆ : (s t : Subset n) → (s ⊆? t) Reflects (s ⊆ t)
⊆?-Reflects-⊆ {zero} _ _ ()
⊆?-Reflects-⊆ {suc _} s t with head s ≤? head t | ≤?-Reflects-≤ (head s) (head t)
... | false | head-s≰head-t = λ s⊆t → head-s≰head-t (s⊆t zero)
... | true | head-s≤head-t with tail s ⊆? tail t | ⊆?-Reflects-⊆ (tail s) (tail t)
... | false | tail-s⊈tail-t = λ s⊆t → tail-s⊈tail-t (tail-⊆ s⊆t)
... | true | tail-s⊆tail-t = λ where
  zero → head-s≤head-t
  (suc i) → tail-s⊆tail-t i

⊆?-⊆ : {s t u v : Subset n} → s ⊆ t → u ⊆ v → (t ⊆? u) ≤ (s ⊆? v)
⊆?-⊆ {zero} _ _ = b≤b
⊆?-⊆ {suc _} s⊆t u⊆v = ∧-≤ (≤?-≤ (s⊆t zero) (u⊆v zero)) (⊆?-⊆ (tail-⊆ s⊆t) (tail-⊆ u⊆v))

⊆-refl : {s : Subset n} → s ⊆ s
⊆-refl _ = ≤-refl

⊆-antisym : {s t : Subset n} → s ⊆ t → t ⊆ s → s ≗ t
⊆-antisym s⊆t t⊆s i = ≤-antisym (s⊆t i) (t⊆s i)

⊆-trans : {r s t : Subset n} → r ⊆ s → s ⊆ t → r ⊆ t
⊆-trans r⊆s s⊆t i = ≤-trans (r⊆s i) (s⊆t i)

≗⇒⊆ : {s t : Subset n} → s ≗ t → s ⊆ t
≗⇒⊆ s≗t i rewrite s≗t i = ≤-refl

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
... | false | true | _ = ℕₚ.≤-trans (∣∣-⊆ (tail-⊆ s⊆t)) (<⇒≤ <-suc)
... | true | true | _ = s≤s (∣∣-⊆ (tail-⊆ s⊆t))

∣∣∘full : ∀ n → ∣ full n ∣ ≡ n
∣∣∘full zero = refl
∣∣∘full (suc n) = suc =$= ∣∣∘full n

∣∣∘empty : ∀ n → ∣ empty n ∣ ≡ 0
∣∣∘empty zero = refl
∣∣∘empty (suc n) = ∣∣∘empty n

∣∣∘singleton : ∣_∣ ∘ singleton {n} ≗ const 1
∣∣∘singleton {suc n} zero = suc =$= ∣∣∘empty n
∣∣∘singleton {suc _} (suc i) = ∣∣∘singleton i

∩-cong : {s t u v : Subset n} → s ≗ t → u ≗ v → s ∩ u ≗ t ∩ v
∩-cong = zipWith-cong _∧_

∪-cong : {s t u v : Subset n} → s ≗ t → u ≗ v → s ∪ u ≗ t ∪ v
∪-cong = zipWith-cong _∨_

∪-⊆ : {s t u v : Subset n} → s ⊆ t → u ⊆ v → s ∪ u ⊆ t ∪ v
∪-⊆ s⊆t u⊆v i = ∨-≤ (s⊆t i) (u⊆v i)

∪-empty : (s : Subset n) → s ∪ empty n ≗ s
∪-empty s i = ∨-false (s i)

image-cong : ∀ {f g : Fin m → Fin n} {s t} → f ≗ g → s ≗ t → image f s ≗ image g t
image-cong {zero} f≗g s≗t i = refl
image-cong {suc _} f≗g s≗t i = cong₂ _∨_ (cong₂ _∧_ (s≗t zero) ((_≟ i) =$= f≗g zero)) (image-cong (λ i → f≗g (suc i)) (λ i → s≗t (suc i)) i)

image-⊆ : ∀ (f : Fin m → Fin n) {s t} → s ⊆ t → image f s ⊆ image f t
image-⊆ {zero} _ _ _ = b≤b
image-⊆ {suc _} f s⊆t i = ∨-≤ (∧-≤ (s⊆t zero) ≤-refl) (image-⊆ (f ∘ suc) (tail-⊆ s⊆t) i)

image-empty : (f : Fin m → Fin n) → image f (empty m) ≡ empty n
image-empty {zero} _ = refl
image-empty {suc _} f = image-empty (f ∘ suc)

image-singleton : ∀ (f : Fin m → Fin n) i → image f (singleton i) ≗ singleton (f i)
image-singleton f zero rewrite image-empty (f ∘ suc) = ∪-empty _
image-singleton f (suc i) = image-singleton (f ∘ suc) i

⊆-Cat : ℕ → Category 0ℓ 0ℓ 0ℓ
⊆-Cat n = Preorder (_⊆_ {n}) ⊆-refl ⊆-trans

∣∣-functor : Functor (⊆-Cat n) ℕₚ.≤-Cat
∣∣-functor = record
  { obj = ∣_∣
  ; hom = record
    { func = ∣∣-⊆
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ _ _ → tt
  ; mor-id = tt
  }

⊆?-functorˡ : Subset n → Functor (⊆-Cat n) (Op Boolₚ.≤-Cat)
⊆?-functorˡ s = record
  { obj = _⊆? s
  ; hom = record
    { func = flip ⊆?-⊆ ⊆-refl
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ _ _ → tt
  ; mor-id = tt
  }

⊆?-functorʳ : Subset n → Functor (⊆-Cat n) (Boolₚ.≤-Cat)
⊆?-functorʳ s = record
  { obj = s ⊆?_
  ; hom = record
    { func = ⊆?-⊆ ⊆-refl
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ _ _ → tt
  ; mor-id = tt
  }

∪-functorˡ : Subset n → Functor (⊆-Cat n) (⊆-Cat n)
∪-functorˡ s = record
  { obj = _∪ s
  ; hom = record
    { func = flip ∪-⊆ ⊆-refl
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ _ _ → tt
  ; mor-id = tt
  }

∪-functorʳ : Subset n → Functor (⊆-Cat n) (⊆-Cat n)
∪-functorʳ s = record
  { obj = s ∪_
  ; hom = record
    { func = ∪-⊆ ⊆-refl
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ _ _ → tt
  ; mor-id = tt
  }

image-functor : (Fin m → Fin n) → Functor (⊆-Cat m) (⊆-Cat n)
image-functor f = record
  { obj = image f
  ; hom = record
    { func = image-⊆ f
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ _ _  → tt
  ; mor-id = tt
  }
