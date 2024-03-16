{-# OPTIONS --without-K --safe #-}

open import Universe.Presheaf.Base

module Universe.Presheaf.SC {a r} (P : Presheaf a r) where
-- SC stands for Simplicial Complex
open import Data.ASC
open import Data.Nat.Base
open import Data.Fin.Subset.Base
open import Level

private
  module P = Presheaf P

  variable
    l m n : ℕ

record SC (asc : ASC n) : Set (a ⊔ r) where
  field
    for : {s : CSet n m} → s ∈ asc → Tope P m
    compat : ∀ {s : CSet n m} {t : CSet n l} t∈asc (s⊂t : s ⊂ t) → P.proj (embed s⊂t) (for t∈asc) P.≃ for (Has-⊆ asc s⊂t t∈asc)

open SC public

-- restrict : (b c : ASC n) → b ⊑ c → SC c → SC b
-- restrict b c b⊑c sc .for s∈b = sc .for (⊑-∈ {a = b} {c} _ b⊑c s∈b)
-- restrict b c b⊑c sc .compat t∈b s⊂t =
--   P.proj (embed s⊂t) (restrict b c b⊑c sc .for t∈b) ≡⟨⟩
--   P.proj (embed s⊂t) (sc .for (⊑-∈ {a = b} {c} _ b⊑c t∈b)) ≈⟨ sc .compat (⊑-∈ {a = b} {c} _ b⊑c t∈b) s⊂t ⟩
--   sc .for (Has-⊆ c s⊂t (⊑-∈ {a = b} {c} _ b⊑c t∈b)) ≡⟨ sc .for =$= T-irrel ⟩
--   sc .for (⊑-∈ {a = b} {c} _ b⊑c (Has-⊆ b s⊂t t∈b)) ≡⟨⟩
--   restrict b c b⊑c sc .for (Has-⊆ b s⊂t t∈b) ∎
--   where open Relation.Reasoning (P._≃_)
--         open Equiv (P.Space _ .refl) (P.Space _ .trig)
