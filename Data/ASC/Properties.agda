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

⊑-add : ∀ (asc : ASC n) s → asc ⊑ add asc s
⊑-add _ _ _ = a≤a∨b

∈-add : ∀ (asc : ASC n) s → s ∈ add asc s
∈-add asc s rewrite Reflects-true (s ⊆? s) (⊆?-Reflects-⊆ s s) ⊆-refl rewrite ∨-true {has asc s} = tt

⊑-addAll : ∀ (ss : Fin m → Subset n) asc → asc ⊑ addAll ss asc
⊑-addAll {zero} _ asc = ⊑-refl {a = asc}
⊑-addAll {suc _} ss asc = ⊑-trans {_} {asc} {add asc (ss zero)} {addAll ss asc} (⊑-add asc (ss zero)) (⊑-addAll (λ i → ss (suc i)) (add asc (ss zero)))

∈-addAll : ∀ (ss : Fin m → Subset n) asc i → ss i ∈ addAll ss asc
∈-addAll {suc _} ss asc zero = ⊑-∈ {_} {add asc (ss zero)} {addAll ss asc} (ss zero) (⊑-addAll (λ i → ss (suc i)) (add asc (ss zero))) (∈-add asc (ss zero))
∈-addAll {suc _} ss asc (suc i) = ∈-addAll (λ i → ss (suc i)) (add asc (ss zero)) i

add-⊑ : ∀ {s} {a b : ASC n} → s ∈ b → a ⊑ b → add a s ⊑ b
add-⊑ {b = b} s∈b a⊑b t rewrite sym (∨-idem {has b t}) = ∨-≤ (a⊑b t) (Reflects-→ (⊆?-Reflects-⊆ t _) (id-Reflects-T (has b t)) λ t⊆s → Has-⊆ b t⊆s s∈b)

empty∈asc : (asc : ASC (suc n)) → empty _ ∈ asc
empty∈asc asc = Has-⊆ asc empty⊆s (asc .hasAllPoints zero)

-- add-empty : (asc : ASC (suc n)) → add asc (empty _) ≅ asc
-- add-empty asc = ⊑-antisym {a = add asc (empty _)} {b = asc} (add-⊑ {a = asc} {b = asc} (empty∈asc asc) (⊑-refl {a = asc})) (⊑-add asc (empty _))
