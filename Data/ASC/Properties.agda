{-# OPTIONS --without-K --safe #-}

module Data.ASC.Properties where

open import Data.ASC.Base
open import Data.Nat.Base hiding (_≤_)
open import Data.Bool.Base
open import Data.Bool.Properties
open import Relation.Equality.Base
open import Data.Fin.Subset.Base
open import Data.Fin.Subset.Properties
open import Category.Functor
open import Data.Unit.Core
open import Data.Vec.Base
open import Data.Fin.Base
open import Data.Sum.Base
open import Data.Product.Base

private
  variable
    m n : ℕ

⊑-refl : {a : ASC n} → a ⊑ a
⊑-refl _ = ≤-refl

⊑-antisym : {a b : ASC n} → a ⊑ b → b ⊑ a → a ≅ b
⊑-antisym a⊑b b⊑a s = ≤-antisym (a⊑b s) (b⊑a s)

⊑-trans : {a b c : ASC n} → a ⊑ b → b ⊑ c → a ⊑ c
⊑-trans a⊑b b⊑c s = ≤-trans (a⊑b s) (b⊑c s)

⊑-∈ : ∀ {a b : ASC n} s → a ⊑ b → s ∈ a → s ∈ b
⊑-∈ s a⊑b = T-≤ (a⊑b s)

⊑-add : ∀ s (asc : ASC n) → asc ⊑ add s asc
⊑-add _ _ _ = a≤a∨b

∈-add : ∀ s (asc : ASC n) → s ∈ add s asc
∈-add s asc rewrite Reflects-true (s ⊆? s) (⊆?-Reflects-⊆ s s) ⊆-refl rewrite ∨-true {has asc s} = tt

⊑-addAll : ∀ (ss : Fin m → Subset n) asc → asc ⊑ addAll ss asc
⊑-addAll {zero} _ asc = ⊑-refl {a = asc}
⊑-addAll {suc _} ss asc =
  let head-ss = ss zero
      tail-ss i = ss (suc i)
      added = add head-ss asc
      addedAll = addAll ss asc
  in ⊑-trans {_} {asc} {added} {addedAll} (⊑-add head-ss asc) (⊑-addAll tail-ss (added))

∈-addAll : ∀ (ss : Fin m → Subset n) asc i → ss i ∈ addAll ss asc
∈-addAll {suc _} ss asc zero =
  let head-ss = ss zero
      tail-ss i = ss (suc i)
      added = add head-ss asc
      addedAll = addAll ss asc
  in ⊑-∈ {_} {added} {addedAll} head-ss (⊑-addAll tail-ss added) (∈-add head-ss asc)
∈-addAll {suc _} ss asc (suc i) = ∈-addAll (λ i → ss (suc i)) (add (ss zero) asc) i

add-⊆ : ∀ {s t} {asc : ASC n} → s ∈ add t asc → s ⊆ t ⊎ (s ∈ asc)
add-⊆ {_} {s} {t} {asc} with has asc s
... | false = λ s⊆?t → inj₁ (T-Reflects (⊆?-Reflects-⊆ s t) s⊆?t)
... | true = λ _ → inj₂ tt

addAll-⊆ : ∀ {s} {ss : Fin m → Subset n} {asc} → s ∈ addAll ss asc → Σ (Fin m) (λ i → s ⊆ ss i) ⊎ (s ∈ asc)
addAll-⊆ {zero} s∈asc = inj₂ s∈asc
addAll-⊆ {suc _} {ss = ss} {asc} s∈addAll with addAll-⊆ {ss = λ i → ss (suc i)} s∈addAll
... | inj₁ (i , s⊆ss) = inj₁ (suc i , s⊆ss)
... | inj₂ s∈add with add-⊆ {_} {_} {ss zero} {asc} s∈add
... | inj₁ s⊆ss = inj₁ (zero , s⊆ss)
... | inj₂ s∈asc = inj₂ s∈asc

add-⊑ : ∀ {s} {a b : ASC n} → s ∈ b → a ⊑ b → add s a ⊑ b
add-⊑ {b = b} s∈b a⊑b t rewrite sym (∨-idem {has b t}) = ∨-≤ (a⊑b t) (Reflects-→ (⊆?-Reflects-⊆ t _) (id-Reflects-T (has b t)) λ t⊆s → Has-⊆ b t⊆s s∈b)

addAll-⊑ : ∀ {ss : Fin m → Subset n} {a b} → (∀ i → ss i ∈ b) → a ⊑ b → addAll ss a ⊑ b
addAll-⊑ {zero} _ a⊑b = a⊑b
addAll-⊑ {suc _} {_} {_} {a} {b} ∀ss∈b a⊑b = addAll-⊑ {b = b} (λ i → ∀ss∈b (suc i)) (add-⊑ {a = a} {b = b} (∀ss∈b zero) a⊑b)

empty∈asc : (asc : ASC (suc n)) → empty _ ∈ asc
empty∈asc asc = Has-⊆ asc empty⊆s (asc .hasAllPoints zero)

add-∈ : ∀ {s} (asc : ASC n) → s ∈ asc → add s asc ⊑ asc
add-∈ asc s∈asc = add-⊑ {a = asc} {b = asc} s∈asc (⊑-refl {a = asc})
