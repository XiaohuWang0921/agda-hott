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
    k l m n : ℕ

record SC (asc : ASC n) : Set (a ⊔ r) where
  field
    for : {s : CSet n m} → s ∈ asc → Tope P m
    compat : ∀ {s : CSet n m} {t : CSet n l} t∈asc (s⊂t : s ⊂ t) → for (Has-⊆ asc s⊂t t∈asc) P.≃ P.proj (embed s⊂t) (for t∈asc)

  for-resp : ∀ {s t : CSet n m} (s≡t : s ≡ t) s∈asc → for (resp (_∈ asc) s≡t s∈asc) ≡ for s∈asc
  for-resp Eq.refl _ = Eq.refl

  for-pser : ∀ {s t : CSet n m} (s≡t : s ≡ t) t∈asc → for (pser (_∈ asc) s≡t t∈asc) ≡ for t∈asc
  for-pser Eq.refl _ = Eq.refl

open SC

restrict : (b c : ASC n) → b ⊑ c → SC c → SC b
restrict b c b⊑c sc .for s∈b = sc .for (⊑-∈ {a = b} {c} _ b⊑c s∈b)
restrict b c b⊑c sc .compat t∈b s⊂t =
  restrict b c b⊑c sc .for (Has-⊆ b s⊂t t∈b) ≡⟨⟩
  sc .for (⊑-∈ {a = b} {c} _ b⊑c (Has-⊆ b s⊂t t∈b)) ≡⟨ sc .for =$= T-irrel ⟩
  sc .for (Has-⊆ c s⊂t (⊑-∈ {a = b} {c} _ b⊑c t∈b)) ≈⟨ sc .compat (⊑-∈ {a = b} {c} _ b⊑c t∈b) s⊂t ⟩
  P.proj (embed s⊂t) (sc .for (⊑-∈ {a = b} {c} _ b⊑c t∈b)) ≡⟨⟩
  (P.proj (embed s⊂t) (restrict b c b⊑c sc .for t∈b) ∎)
  where open Relation.Reasoning (P._≃_)
        open Equiv (refl (P.Space _)) (trig (P.Space _))

module Fill (fillable : ∀ n → Fillable P n) where

  extend : ∀ asc (s : CSet (suc k) l) → SC asc → SC (add s asc)
  extendAll : ∀ asc (ss : Fin m → CSet (suc k) l) → SC asc → SC (addAll ss asc)
  
  extend {l = 0} asc s rewrite l≡0 s Eq.refl =
    let e = empty _
    in restrict (add e asc) asc (add-∈ asc (empty∈asc asc))
  extend {l = 1} asc s = restrict (add s asc) asc (add-∈ asc (asc .hasAllPoints s))
  extend {k = k} {l = suc (suc l)} asc s with has asc (_ , s) in eq
  ... | true = restrict (add s asc) asc (add-∈ asc (pser T eq tt))
  ... | false = result
    module Extend where
      faces : SC asc → SC (addAll (except s) asc)
      faces = extendAll asc (except s)

      cycl : SC asc → Cycle P l
      cycl sc .face i = faces sc .for (∈-addAll (except s) asc i)
      cycl sc .compatible i j =
        P.proj (punchIn i) (cycl sc .face j) ≈˘⟨ P.map-cong (embed-except (except s j) Eq.refl _) _ ⟩
        P.proj (embed (except⊂s (except s j) i)) (cycl sc .face j) ≡⟨⟩
        P.proj (embed (except⊂s (except s j) i)) (faces sc .for (∈-addAll (except s) asc j)) ≈˘⟨ faces sc .compat (∈-addAll (except s) asc _) _ ⟩
        faces sc .for (Has-⊆ (addAll (except s) asc) (except⊂s (except s j) i) (∈-addAll (except s) asc j)) ≡˘⟨ for-resp (faces sc) _ _ ⟩
        faces sc .for (resp (_∈ addAll (except s) asc) (except-except s Eq.refl j i) (Has-⊆ (addAll (except s) asc) (except⊂s (except s j) i) (∈-addAll (except s) asc j))) ≡⟨ faces sc .for =$= T-irrel ⟩
        faces sc .for (Has-⊆ (addAll (except s) asc) (except⊂s (except s (punchIn j i)) (pinch i j)) (∈-addAll (except s) asc (punchIn j i))) ≈⟨ faces sc .compat _ _ ⟩
        P.proj (embed (except⊂s (except s (punchIn j i)) (pinch i j))) (faces sc .for (∈-addAll (except s) asc (punchIn j i))) ≡⟨⟩
        P.proj (embed (except⊂s (except s (punchIn j i)) (pinch i j))) (cycl sc .face (punchIn j i)) ≈⟨ P.map-cong (embed-except (except s (punchIn j i)) Eq.refl _) _ ⟩
        P.proj (punchIn (pinch i j)) (cycl sc .face (punchIn j i)) ∎
        where open Relation.Reasoning (P._≃_)
              open Equiv (refl (P.Space _)) (trig (P.Space _))
              _ = embed-except

      result : SC asc → SC (add s asc)
      result sc .for {s = t} t∈added with add-⊂ {s = t} {s} {asc} t∈added
      ... | inj₂ t∈asc = sc .for t∈asc
      ... | inj₁ t⊂s with ⊂-except t⊂s Eq.refl
      ... | inj₂ (i , t⊂except) = {!faces .for!}
      ... | inj₁ (Eq.refl , Eq.refl) = {!!}
      result sc .compat = {!!}

  extendAll {zero} _ _ sc = sc
  extendAll {suc _} asc ss sc =
    let head-ss = ss zero
        tail-ss i = ss (suc i)
    in extendAll (add head-ss asc) tail-ss (extend asc head-ss sc)
    
  -- extend {l = 0} asc s ∣s∣≡0 rewrite ∣∣≡0 s ∣s∣≡0 = restrict _ asc (add-∈ asc (empty∈asc asc))
  -- extend {l = 1} asc s ∣s∣≡1 with ∣∣≡1 s ∣s∣≡1
  -- ... | i , s≡single rewrite s≡single = restrict _ asc (add-∈ asc (asc .hasAllPoints i))
  -- extend {l = suc (suc l)} asc s ∣s∣≡l+2 sc = {!!}
  --   where
  --     step₁ : SC (addAll (except s) asc)
  --     step₁ = extendAll asc (except s)
  --                       (λ i → Eq.trans (∣∣∘except s i) (pred =$= ∣s∣≡l+2)) sc

  --     step₂ : SC (add s asc)
  --     step₂ .for {t} t∈add with add-⊆ {_} {t} {s} {asc} t∈add
  --     ... | inj₂ t∈asc = sc .for t∈asc
  --     ... | inj₁ t⊆s with ⊆-except t⊆s
  --     ... | inj₁ t≡s = {!!}
  --       where
  --         cycl : Cycle P l
  --         cycl .face i =
  --           let i' = Fin.tsac ∣s∣≡l+2 i
  --           in resp P.Tope (Eq.trans (∣∣∘except s i') (pred =$= ∣s∣≡l+2)) (step₁ .for (∈-addAll (except s) asc i'))
  --         cycl .compatible i j =
  --           let i' = Fin.tsac (pred =$= ∣s∣≡l+2) i
  --               j' = Fin.tsac ∣s∣≡l+2 j
  --           in {!!}
  --     ... | inj₂ (i , t⊆except) =
  --       step₁ .for (Has-⊆ (addAll (except s) asc) t⊆except (∈-addAll (except s) asc i))
  --     step₂ .compat = {!!}  
