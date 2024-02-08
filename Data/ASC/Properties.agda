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
    k l m n : ℕ

⊑-refl : {a : ASC n} → a ⊑ a
⊑-refl _ = ≤-refl

⊑-antisym : {a b : ASC n} → a ⊑ b → b ⊑ a → a ≅ b
⊑-antisym a⊑b b⊑a s = ≤-antisym (a⊑b s) (b⊑a s)

⊑-trans : {a b c : ASC n} → a ⊑ b → b ⊑ c → a ⊑ c
⊑-trans a⊑b b⊑c s = ≤-trans (a⊑b s) (b⊑c s)

⊑-∈ : ∀ {a b} (s : CSet k l) → a ⊑ b → s ∈ a → s ∈ b
⊑-∈ s a⊑b = T-≤ (a⊑b s)

⊑-add : (s : CSet k l) (asc : ASC k) → asc ⊑ add s asc
⊑-add _ _ _ = a≤a∨b

∈-add : (s : CSet k l) (asc : ASC k) → s ∈ add s asc
∈-add s asc rewrite Reflects-true (s ⊂? s) (⊂?-Reflects-⊂ s s) ⊂-refl rewrite ∨-true {has asc (_ , s)} = tt

⊑-addAll : ∀ (ss : Fin m → CSet k l) asc → asc ⊑ addAll ss asc
⊑-addAll {zero} _ asc = ⊑-refl {a = asc}
⊑-addAll {suc _} ss asc =
  let head-ss = ss zero
      tail-ss i = ss (suc i)
      added = add head-ss asc
      addedAll = addAll ss asc
  in ⊑-trans {_} {asc} {added} {addedAll} (⊑-add head-ss asc) (⊑-addAll tail-ss (added))

∈-addAll : ∀ (ss : Fin m → CSet k l) asc i → ss i ∈ addAll ss asc
∈-addAll {suc _} ss asc zero =
  let head-ss = ss zero
      tail-ss i = ss (suc i)
      added = add head-ss asc
      addedAll = addAll ss asc
  in ⊑-∈ {a = added} {addedAll} head-ss (⊑-addAll tail-ss added) (∈-add head-ss asc)
∈-addAll {suc _} ss asc (suc i) = ∈-addAll (λ i → ss (suc i)) (add (ss zero) asc) i

add-⊂ : ∀ {s : CSet k l} {t : CSet k m} {asc} → s ∈ add t asc → s ⊂ t ⊎ (s ∈ asc)
add-⊂ {s = s} {t} {asc} with has asc (_ , s)
... | false = λ s⊂?t → inj₁ (T-Reflects (⊂?-Reflects-⊂ s t) s⊂?t)
... | true = λ _ → inj₂ tt

addAll-⊂ : ∀ {s : CSet k l} {ss : Fin m → CSet k n} {asc} → s ∈ addAll ss asc → Σ (Fin m) (λ i → s ⊂ ss i) ⊎ (s ∈ asc)
addAll-⊂ {m = zero} s∈asc = inj₂ s∈asc
addAll-⊂ {m = suc _} {ss = ss} {asc} s∈addAll with addAll-⊂ {ss = λ i → ss (suc i)} s∈addAll
... | inj₁ (i , s⊂ss) = inj₁ (suc i , s⊂ss)
... | inj₂ s∈add with add-⊂ {t = ss zero} {asc} s∈add
... | inj₁ s⊂ss = inj₁ (zero , s⊂ss)
... | inj₂ s∈asc = inj₂ s∈asc

add-⊑ : ∀ {s : CSet k l} {a b} → s ∈ b → a ⊑ b → add s a ⊑ b
add-⊑ {b = b} s∈b a⊑b t rewrite sym (∨-idem {has b (_ , t)}) = ∨-≤ (a⊑b t) (Reflects-→ (⊂?-Reflects-⊂ t _) (id-Reflects-T (has b (_ , t))) λ t⊆s → Has-⊆ b t⊆s s∈b)

addAll-⊑ : ∀ {ss : Fin m → CSet k l} {a b} → (∀ i → ss i ∈ b) → a ⊑ b → addAll ss a ⊑ b
addAll-⊑ {zero} _ a⊑b = a⊑b
addAll-⊑ {suc _} {a = a} {b} ∀ss∈b a⊑b = addAll-⊑ {b = b} (λ i → ∀ss∈b (suc i)) (add-⊑ {a = a} {b = b} (∀ss∈b zero) a⊑b)

add-⊂-⊑ : ∀ {s : CSet k l} {t : CSet k m} {a b} → s ⊂ t → a ⊑ b → add s a ⊑ add t b
add-⊂-⊑ s⊂t a⊑b u = ∨-≤ (a⊑b u) (⊂?-⊂ {s = u} ⊂-refl s⊂t)

empty∈asc : (asc : ASC (suc n)) → empty _ ∈ asc
empty∈asc asc = Has-⊆ asc empty⊂s (asc .hasAllPoints (single zero))

l≡0⇒s∈asc : (s : CSet (suc n) 0) (asc : ASC (suc n)) → s ∈ asc
l≡0⇒s∈asc s rewrite l≡0 s refl = empty∈asc

add-∈ : ∀ {s : CSet k l} asc → s ∈ asc → add s asc ⊑ asc
add-∈ asc s∈asc = add-⊑ {a = asc} {b = asc} s∈asc (⊑-refl {a = asc})
