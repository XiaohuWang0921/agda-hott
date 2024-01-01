{-# OPTIONS --without-K --safe #-}

open import Universe.Presheaf.Base

module Universe.Presheaf.SC {a r} (P : Presheaf a r) where
-- SC stands for Simplicial Complex
open import Data.ASC.Base
open import Data.ASC.Properties
open import Data.Fin.Base as Fin
open import Data.Nat.Base
open import Data.Fin.Subset.Base
open import Data.Fin.Subset.Properties
open import Level
open import Universe.Presheaf.Fillable
import Relation.Reasoning
open import Universe.Setoid
open import Relation.Equality.Base as Eq hiding (refl; trig; sym; trans; cong)
open import Data.Vec.Base
open import Data.Bool.Base
open import Data.Unit.Core
open import Data.Sum.Base
open import Data.Product.Base
open import Data.Bool.Properties
open import Universe.Presheaf.Cycle

module P = Presheaf P

private
  variable
    l m n : ℕ

record SC (asc : ASC n) : Set (a ⊔ r) where
  field
    for : ∀ {s} → s ∈ asc → Tope P ∣ s ∣
    compat : ∀ {s t} t∈asc (s⊆t : s ⊆ t) → for (Has-⊆ asc s⊆t t∈asc) P.≃ P.proj (embed s⊆t) (for t∈asc)

open SC

restrict : (b c : ASC n) → b ⊑ c → SC c → SC b
restrict b c b⊑c sc .for s∈b = sc .for (⊑-∈ {_} {b} {c} _ b⊑c s∈b)
restrict b c b⊑c sc .compat t∈b s⊆t =
  restrict b c b⊑c sc .for (Has-⊆ b s⊆t t∈b) ≡⟨⟩
  sc .for (⊑-∈ {_} {b} {c} _ b⊑c (Has-⊆ b s⊆t t∈b)) ≡⟨ sc .for =$= T-irrel ⟩
  sc .for (Has-⊆ c s⊆t (⊑-∈ {_} {b} {c} _ b⊑c t∈b)) ≈⟨ sc .compat (⊑-∈ {_} {b} {c} _ b⊑c t∈b) s⊆t ⟩
  P.proj (embed s⊆t) (sc .for (⊑-∈ {_} {b} {c} _ b⊑c t∈b)) ≡⟨⟩
  (P.proj (embed s⊆t) (restrict b c b⊑c sc .for t∈b) ∎)
  where open Relation.Reasoning (P._≃_)
        open Equiv (refl (P.Space _)) (trig (P.Space _))

module Fill (fillable : ∀ n → Fillable P n) where

  extend : ∀ (asc : ASC (suc n)) s → ∣ s ∣ ≡ l → SC asc → SC (add s asc)
  extendAll : ∀ asc (ss : Fin m → Subset (suc n)) → (∀ i → ∣ ss i ∣ ≡ l) → SC asc → SC (addAll ss asc)

  extend {l = 0} asc s ∣s∣≡0 rewrite ∣∣≡0 s ∣s∣≡0 = restrict _ asc (add-∈ asc (empty∈asc asc))
  extend {l = 1} asc s ∣s∣≡1 with ∣∣≡1 s ∣s∣≡1
  ... | i , s≡single rewrite s≡single = restrict _ asc (add-∈ asc (asc .hasAllPoints i))
  extend {l = suc (suc l)} asc s ∣s∣≡l+2 sc = {!!}
    where
      step₁ : SC (addAll (except s) asc)
      step₁ = extendAll asc (except s)
                        (λ i → Eq.trans (∣∣∘except s i) (pred =$= ∣s∣≡l+2)) sc

      step₂ : SC (add s asc)
      step₂ .for {t} t∈add with add-⊆ {_} {t} {s} {asc} t∈add
      ... | inj₂ t∈asc = sc .for t∈asc
      ... | inj₁ t⊆s with ⊆-except t⊆s
      ... | inj₁ t≡s = {!!}
        where
          cycl : Cycle P l
          cycl .face i =
            let i' = Fin.tsac ∣s∣≡l+2 i
            in resp P.Tope (Eq.trans (∣∣∘except s i') (pred =$= ∣s∣≡l+2)) (step₁ .for (∈-addAll (except s) asc i'))
          cycl .compatible i j =
            let i' = Fin.tsac (pred =$= ∣s∣≡l+2) i
                j' = Fin.tsac ∣s∣≡l+2 j
            in {!!}
      ... | inj₂ (i , t⊆except) =
        step₁ .for (Has-⊆ (addAll (except s) asc) t⊆except (∈-addAll (except s) asc i))
      step₂ .compat = {!!}

  extendAll {zero} _ _ _ sc = sc
  extendAll {suc _} asc ss ∀∣ss∣≡l sc = extendAll (add (ss zero) asc) (λ i → ss (suc i)) (λ i → ∀∣ss∣≡l (suc i)) (extend asc (ss zero) (∀∣ss∣≡l zero) sc)
  
