{-# OPTIONS --without-K --safe #-}

open import Universe.Presheaf.Base
open import Universe.Presheaf.Fillable

module Universe.Presheaf.SC.Fill {a r} (P : Presheaf a r) (fillable : ∀ n → Fillable P n) where

open import Data.ASC
open import Data.Nat.Base
open import Universe.Presheaf.SC P
open import Data.Fin.Subset.Base
open import Relation.Equality.Base as Eq hiding (refl; sym; trig; trans)
import Relation.Reasoning
open import Data.Fin.Subset.Properties
open import Universe.Set as Set
open import Data.Bool.Base
open import Data.Product.Base
open import Universe.Setoid
open import Data.Fin.Base
open import Data.Bool.Properties
open import Data.Sum.Base
open import Universe.Presheaf.Cycle
open import Data.Unit.Core

private
  module P = Presheaf P
  
  variable
    k l m n : ℕ

module Continue {asc : ASC (suc k)} (sc : SC asc) where

  -- Maybe consider rewriting this into well-founded
  -- recursion/induction someday.
  topes : ∀ l → CSet (suc k) l → Tope P l
  topes-compat : ∀ l m {s : CSet (suc k) l} {t : CSet (suc k) m} (s⊂t : s ⊂ t) → P.proj (embed s⊂t) (topes m t) P.≃ topes l s

  ∼⇒compat : ∀ {l m} {s : CSet (suc k) l} {t : CSet (suc k) m} (s∼t : s ∼ t) → P.proj (embed (∼⇒⊂ s∼t)) (topes m t) P.≃ topes l s
  ∼⇒compat {s = s} (Eq.refl , Eq.refl) =
    P.proj (embed (∼⇒⊂ {s = s} (Eq.refl , Eq.refl))) (topes _ s) ≡⟨⟩
    P.proj (embed (⊂-refl {s = s})) (topes _ s) ≈⟨ P.map-cong (embed-refl s) _ ⟩
    P.proj Set.id (topes _ s) ≈⟨ P.map-id _ ⟩
    topes _ s ∎
    where open Relation.Reasoning (P._≃_)
          open Equiv (P.Space _ .refl) (P.Space _ .trig)
    
  topes 0 s = sc .for (l≡0⇒s∈asc s asc)
  topes 1 s = sc .for (hasAllPoints asc s)
  topes (suc (suc l)) s =
    if has asc (_ , s)
    then sc .for
    else λ _ → fillable l .fill ⟨$⟩ record
      { face = λ i → topes (suc l) (except s i)
      ; compatible = λ i j →
        P.proj (punchIn i) (topes (suc l) (except s j)) ≈˘⟨ P.map-cong (embed-except (except s j) Eq.refl i) _ ⟩
        P.proj (embed (except⊂s (except s j) i)) (topes (suc l) (except s j)) ≈⟨ topes-compat l (suc l) (except⊂s _ i) ⟩
        topes l (except (except s j) i) ≡⟨ topes l =$= except-except s Eq.refl j i ⟩
        topes l (except (except s (punchIn j i)) (pinch i j)) ≈˘⟨ topes-compat l (suc l) (except⊂s _ _) ⟩
        P.proj (embed (except⊂s (except s (punchIn j i)) (pinch i j))) (topes (suc l) (except s (punchIn j i))) ≈⟨ P.map-cong (embed-except (except s _) Eq.refl _) _ ⟩
        P.proj (punchIn (pinch i j)) (topes (suc l) (except s (punchIn j i))) ∎
      }
    where open Relation.Reasoning (P._≃_)
          open Equiv (P.Space _ .refl) (P.Space _ .trig)

  topes-compat l @ 0 m @ 0 {s} {t} s⊂t =
    P.proj (embed s⊂t) (topes m t) ≡⟨⟩
    P.proj (embed s⊂t) (sc .for (l≡0⇒s∈asc t asc)) ≈⟨ sc .compat _ s⊂t ⟩
    sc .for (Has-⊆ asc s⊂t (l≡0⇒s∈asc t asc)) ≡⟨ sc .for =$= T-irrel ⟩
    sc .for (l≡0⇒s∈asc s asc) ≡⟨⟩
    topes l s ∎
    where open Relation.Reasoning (P._≃_)
          open Equiv (refl (P.Space _)) (trig (P.Space _))

  topes-compat (suc _) 0 s⊂t = ⊂⇒≤ s⊂t |> λ ()

  topes-compat l @ 0 m @ 1 {s} {t} s⊂t =
    P.proj (embed s⊂t) (topes m t) ≡⟨⟩
    P.proj (embed s⊂t) (sc .for (hasAllPoints asc t)) ≈⟨ sc .compat _ s⊂t ⟩
    sc .for (Has-⊆ asc s⊂t (hasAllPoints asc t)) ≡⟨ sc .for =$= T-irrel ⟩
    sc .for (l≡0⇒s∈asc s asc) ≡⟨⟩
    topes l s ∎
    where open Relation.Reasoning (P._≃_)
          open Equiv (refl (P.Space _)) (trig (P.Space _))

  topes-compat l @ 1 m @ 1 {s} {t} s⊂t =
    P.proj (embed s⊂t) (topes m t) ≡⟨⟩
    P.proj (embed s⊂t) (sc .for (hasAllPoints asc t)) ≈⟨ sc .compat _ s⊂t ⟩
    sc .for (Has-⊆ asc s⊂t (hasAllPoints asc t)) ≡⟨ sc .for =$= T-irrel ⟩
    sc .for (hasAllPoints asc s) ≡⟨⟩
    topes l s ∎
    where open Relation.Reasoning (P._≃_)
          open Equiv (refl (P.Space _)) (trig (P.Space _))

  topes-compat (suc (suc _)) 1 s⊂t = ⊂⇒≤ s⊂t |> λ where
    (s≤s ())

  topes-compat l @ 0 (suc (suc m)) {s} {t} s⊂t =
    if has asc (_ , t)
    then (λ t∈asc →
      P.proj (embed s⊂t) (topes (suc (suc m)) t) ≡⟨ P.proj _ =$= if-T t∈asc ⟩
      P.proj (embed s⊂t) (sc .for t∈asc) ≈⟨ sc .compat _ _ ⟩
      sc .for (Has-⊆ asc s⊂t t∈asc) ≡⟨ sc .for =$= T-irrel ⟩
      sc .for (l≡0⇒s∈asc s asc) ≡⟨⟩
      topes l s ∎)
    else λ t∉asc →
      < (λ ())
      ⊹ (λ (i , s⊂except) →
        (P.proj (embed s⊂t) (topes (suc (suc m)) t) ≡⟨ P.proj _ =$= if-F t∉asc ⟩
        P.proj (embed s⊂t) (fill (fillable m) ⟨$⟩ _) ≡⟨ Set.flip P.proj _ =$= embed =$= (⊂-irrel s⊂t (⊂-trans s⊂except _)) ⟩
        P.proj (embed (⊂-trans s⊂except (except⊂s t i))) (fill (fillable m) ⟨$⟩ _) ≈⟨ P.map-cong (embed-trans s⊂except _) _ ⟩
        P.proj (embed (except⊂s t i) Set.∘ embed s⊂except) (fill (fillable m) ⟨$⟩ _) ≈⟨ P.map-∘ (embed s⊂except) _ _ ⟩
        P.proj (embed s⊂except) (P.proj (embed (except⊂s t i)) (fill (fillable m) ⟨$⟩ _)) ≈⟨ P.map _ ~$~ P.map-cong (embed-except t Eq.refl i) _ ⟩
        P.proj (embed s⊂except) (P.proj (punchIn i) (fill (fillable m) ⟨$⟩ _)) ≡⟨⟩
        P.proj (embed s⊂except) ((boundary P m ⟨$⟩ (fill (fillable m) ⟨$⟩ _)) .face i) ≈⟨ P.map _ ~$~ fillable m .isSection _ i ⟩
        P.proj (embed s⊂except) (topes (suc m) (except t i)) ≈⟨ topes-compat l (suc m) s⊂except ⟩
        topes l s ∎))
      > (⊂-except s⊂t Eq.refl)
    where open Relation.Reasoning (P._≃_)
          open Equiv (P.Space _ .refl) (P.Space _ .trig)

  topes-compat l @ 1 (suc (suc m)) {s} {t} s⊂t =
    if has asc (_ , t)
    then (λ t∈asc →
      P.proj (embed s⊂t) (topes (suc (suc m)) t) ≡⟨ P.proj _ =$= if-T t∈asc ⟩
      P.proj (embed s⊂t) (sc .for t∈asc) ≈⟨ sc .compat _ _ ⟩
      sc .for (Has-⊆ asc s⊂t t∈asc) ≡⟨ sc .for =$= T-irrel ⟩
      sc .for (hasAllPoints asc s) ≡⟨⟩
      topes l s ∎)
    else λ t∉asc →
      < (λ ())
      ⊹ (λ (i , s⊂except) →
        (P.proj (embed s⊂t) (topes (suc (suc m)) t) ≡⟨ P.proj _ =$= if-F t∉asc ⟩
        P.proj (embed s⊂t) (fill (fillable m) ⟨$⟩ _) ≡⟨ Set.flip P.proj _ =$= embed =$= (⊂-irrel s⊂t (⊂-trans s⊂except _)) ⟩
        P.proj (embed (⊂-trans s⊂except (except⊂s t i))) (fill (fillable m) ⟨$⟩ _) ≈⟨ P.map-cong (embed-trans s⊂except _) _ ⟩
        P.proj (embed (except⊂s t i) Set.∘ embed s⊂except) (fill (fillable m) ⟨$⟩ _) ≈⟨ P.map-∘ (embed s⊂except) _ _ ⟩
        P.proj (embed s⊂except) (P.proj (embed (except⊂s t i)) (fill (fillable m) ⟨$⟩ _)) ≈⟨ P.map _ ~$~ P.map-cong (embed-except t Eq.refl i) _ ⟩
        P.proj (embed s⊂except) (P.proj (punchIn i) (fill (fillable m) ⟨$⟩ _)) ≡⟨⟩
        P.proj (embed s⊂except) ((boundary P m ⟨$⟩ (fill (fillable m) ⟨$⟩ _)) .face i) ≈⟨ P.map _ ~$~ fillable m .isSection _ i ⟩
        P.proj (embed s⊂except) (topes (suc m) (except t i)) ≈⟨ topes-compat l (suc m) s⊂except ⟩
        topes l s ∎))
      > (⊂-except s⊂t Eq.refl)
    where open Relation.Reasoning (P._≃_)
          open Equiv (P.Space _ .refl) (P.Space _ .trig)

  topes-compat l @ (suc (suc _)) (suc (suc m)) {s} {t} s⊂t =
    if has asc (_ , t)
    then (λ t∈asc →
      P.proj (embed s⊂t) (topes (suc (suc m)) t) ≡⟨ P.proj _ =$= if-T t∈asc ⟩
      P.proj (embed s⊂t) (sc .for t∈asc) ≈⟨ sc .compat _ _ ⟩
      sc .for (Has-⊆ asc s⊂t t∈asc) ≡˘⟨ if-T (Has-⊆ asc s⊂t t∈asc) ⟩
      topes l s ∎)
    else λ t∉asc →
      < (λ s∼t →
        P.proj (embed s⊂t) (topes _ t) ≡⟨ Set.flip P.proj _ =$= embed =$= ⊂-irrel s⊂t (∼⇒⊂ s∼t) ⟩
        P.proj (embed (∼⇒⊂ s∼t)) (topes _ t) ≈⟨ ∼⇒compat s∼t ⟩
        topes _ s ∎)
      ⊹ (λ (i , s⊂except) →
        (P.proj (embed s⊂t) (topes (suc (suc m)) t) ≡⟨ P.proj _ =$= if-F t∉asc ⟩
        P.proj (embed s⊂t) (fill (fillable m) ⟨$⟩ _) ≡⟨ Set.flip P.proj _ =$= embed =$= (⊂-irrel s⊂t (⊂-trans s⊂except _)) ⟩
        P.proj (embed (⊂-trans s⊂except (except⊂s t i))) (fill (fillable m) ⟨$⟩ _) ≈⟨ P.map-cong (embed-trans s⊂except _) _ ⟩
        P.proj (embed (except⊂s t i) Set.∘ embed s⊂except) (fill (fillable m) ⟨$⟩ _) ≈⟨ P.map-∘ (embed s⊂except) _ _ ⟩
        P.proj (embed s⊂except) (P.proj (embed (except⊂s t i)) (fill (fillable m) ⟨$⟩ _)) ≈⟨ P.map _ ~$~ P.map-cong (embed-except t Eq.refl i) _ ⟩
        P.proj (embed s⊂except) (P.proj (punchIn i) (fill (fillable m) ⟨$⟩ _)) ≡⟨⟩
        P.proj (embed s⊂except) ((boundary P m ⟨$⟩ (fill (fillable m) ⟨$⟩ _)) .face i) ≈⟨ P.map _ ~$~ fillable m .isSection _ i ⟩
        P.proj (embed s⊂except) (topes (suc m) (except t i)) ≈⟨ topes-compat l (suc m) s⊂except ⟩
        topes l s ∎))
      > (⊂-except s⊂t Eq.refl)
    where open Relation.Reasoning (P._≃_)
          open Equiv (P.Space _ .refl) (P.Space _ .trig)

  restrict-topes : ∀ l {s : CSet (suc k) l} (s∈asc : s ∈ asc) → topes l s ≡ sc .for s∈asc
  restrict-topes 0 _ = sc .for =$= T-irrel
  restrict-topes 1 _ = sc .for =$= T-irrel
  restrict-topes (suc (suc _)) s∈asc = if-T s∈asc

continue : {asc : ASC (suc k)} → SC asc → SC (all (suc k))
continue sc .for {s = s} _ = let open Continue sc in topes _ s
continue sc .compat _ = let open Continue sc in topes-compat _ _

restrict-continue : ∀ {l} {asc : ASC (suc k)} {s : CSet (suc k) l} (sc : SC asc) (s∈asc : s ∈ asc) → continue sc .for {s = s} tt ≡ sc .for s∈asc
restrict-continue sc s∈asc = let open Continue sc in restrict-topes _ s∈asc
