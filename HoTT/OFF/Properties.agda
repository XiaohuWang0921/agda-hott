{-# OPTIONS --without-K --safe #-}

module HoTT.OFF.Properties where

open import Data.Nat.Base hiding (_≤_)
open import Data.Fin.Base hiding (pred)
open import Data.Nat.Properties hiding (suc-injective)
open import Data.Fin.Properties using (suc-injective)
open import HoTT.OFF
open import HoTT.EqNotation
open import Function.Base as Fun hiding (id; _∘_)
open import Relation.Binary
open import Relation.Nullary

open ≡-Reasoning

private
  variable
    i j k l m n : ℕ

n∷-injective : {f g : OFF m n} → n∷ f ≡ n∷ g → f ≡ g
n∷-injective refl = refl

a∷-injective : {f g : OFF m (suc n)} → a∷ f ≡ a∷ g → f ≡ g
a∷-injective refl = refl

subsf-refl : (f : OFF m n) → subsf refl refl f ≡ f
subsf-refl [] = refl
subsf-refl (n∷ f) = cong n∷_ (subsf-refl f)
subsf-refl (a∷ f) = cong a∷_ (subsf-refl f)

subsf-trans : ∀ .(i≡k : i ≡ k) .(j≡l : j ≡ l) .(k≡m : k ≡ m) .(l≡n : l ≡ n) f →
              subsf (i≡k ∙ k≡m) (j≡l ∙ l≡n) f ≡ subsf k≡m l≡n (subsf i≡k j≡l f)
subsf-trans {_} {_} {suc _} {suc _} {_} {suc _} i≡k sj≡sl k≡m sl≡sn (n∷ f) = cong n∷_ (subsf-trans i≡k (cong pred sj≡sl) k≡m (cong pred sl≡sn) f)
subsf-trans {zero} {zero} {zero} {zero} {zero} {zero} _ _ _ _ [] = refl
subsf-trans {suc _} {suc _} {suc _} {suc _} {suc _} {suc _} si≡sk j≡l sk≡sm l≡n (a∷ f) = cong a∷_ (subsf-trans (cong pred si≡sk) j≡l (cong pred sk≡sm) l≡n f)

∘-assoc : (f : OFF m n) (g : OFF l m) (h : OFF k l) → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
∘-assoc [] _ _ = refl
∘-assoc (n∷ f) g h = cong n∷_ (∘-assoc f g h)
∘-assoc (a∷ f) (n∷ g) h = ∘-assoc f g h
∘-assoc f @ (a∷ _) (a∷ g) (n∷ h) = ∘-assoc f g h
∘-assoc f @ (a∷ _) g @ (a∷ _) (a∷ h) = cong a∷_ (∘-assoc f g h)

∘-identityˡ : (f : OFF m n) → id ∘ f ≡ f
∘-identityˡ [] = refl
∘-identityˡ (n∷ f) = cong n∷_ (∘-identityˡ f)
∘-identityˡ (a∷ f) = cong a∷_ (∘-identityˡ f)

∘-identityʳ : (f : OFF m n) → f ∘ id ≡ f
∘-identityʳ [] = refl
∘-identityʳ (n∷ f) = cong n∷_ (∘-identityʳ f)
∘-identityʳ (a∷ f) = cong a∷_ (∘-identityʳ f)

empty-universal : (f : OFF 0 n) → f ≡ empty
empty-universal [] = refl
empty-universal (n∷ f) = cong n∷_ (empty-universal f)

∘-zeroˡ : (f : OFF 0 0) → empty ∘ f ≡ empty {n}
∘-zeroˡ _ = empty-universal _

∘-zeroʳ : (f : OFF m n) → f ∘ empty ≡ empty
∘-zeroʳ _ = empty-universal _

$$-∘ : ∀ (f : OFF m n) (g : OFF l m) i → f ∘ g $$ i ≡ f $$ g $$ i
$$-∘ [] g i = refl
$$-∘ (n∷ f) g i = cong suc ($$-∘ f g i)
$$-∘ (a∷ f) (n∷ g) i = $$-∘ f g i
$$-∘ (a∷ _) (a∷ _) zero = refl
$$-∘ f @ (a∷ _) (a∷ g) (suc i) = $$-∘ f g i

$$-injective : (f g : OFF m n) → f $$_ ≗ g $$_ → f ≡ g
$$-injective [] [] _ = refl
$$-injective (n∷ f) (n∷ g) n∷f≗n∷g = cong n∷_ ($$-injective f g (suc-injective Fun.∘ n∷f≗n∷g))
$$-injective (n∷ _) (a∷ _) n∷f≗a∷g = n∷f≗a∷g zero |>′ λ ()
$$-injective (a∷ _) (n∷ _) a∷f≗n∷g = a∷f≗n∷g zero |>′ λ ()
$$-injective (a∷ f) (a∷ g) a∷f≗a∷g = cong a∷_ ($$-injective f g (a∷f≗a∷g Fun.∘ suc))

$$-≤ : (f : OFF m n) → (f $$_) Preserves _≤_ ⟶ _≤_
$$-≤ (n∷ f) i≤j = s≤s ($$-≤ f i≤j)
$$-≤ (a∷ f) {zero} _ = z≤n
$$-≤ (a∷ f) {suc _} {suc _} (s≤s i≤j) = $$-≤ f i≤j

$$-∷z : ∀ i (f : OFF m (n ℕ-ℕ inject₁ i)) → (i ∷ f) $$ zero ≡ i
$$-∷z zero f = refl
$$-∷z (suc i) f = cong suc ($$-∷z i f)

$$-∷s : ∀ i (f : OFF m (n ℕ-ℕ inject₁ i)) j → (i ∷ f) $$ suc j ≡ i ⊕ (f $$ j)
$$-∷s zero f j = refl
$$-∷s (suc i) f j = cong suc ($$-∷s i f j)

⊕-shrink : ∀ (i : Fin n) j .(i≤j : i ≤ j) → i ⊕ shrink i j i≤j ≡ j
⊕-shrink zero _ _ = refl
⊕-shrink (suc i) (suc j) si≤sj = cong suc (⊕-shrink i j (≤-pred si≤sj))

⊕-≤ : ∀ (i : Fin n) j → i ≤ i ⊕ j
⊕-≤ zero _ = z≤n
⊕-≤ (suc i) j = s≤s (⊕-≤ i j)

shrink-⊕ : ∀ (i : Fin n) j → shrink i (i ⊕ j) (⊕-≤ i j) ≡ j
shrink-⊕ zero _ = refl
shrink-⊕ (suc i) j = shrink-⊕ i j

$$-fromΠ : (f : Fin m → Fin n) → .(f-≤ : f Preserves _≤_ ⟶ _≤_) →
           fromΠ f f-≤ $$_ ≗ f
$$-fromΠ {suc _} {zero} f = f zero |>′ λ ()
$$-fromΠ {suc _} {suc _} f f-≤ zero = $$-∷z (f zero) _
$$-fromΠ {suc _} {suc _} f f-≤ (suc i) = begin
  fromΠ f f-≤ $$ suc i ≡⟨⟩
  (f zero ∷ fromΠ (λ _ → shrink (f zero) _ _) _) $$ suc i ≡⟨ $$-∷s (f zero) _ _ ⟩
  f zero ⊕ (fromΠ (λ _ → shrink (f zero) _ _) _ $$ i) ≡⟨ cong (f zero ⊕_) ($$-fromΠ _ _ i) ⟩
  f zero ⊕ shrink (f zero) (f (suc i)) _ ≡⟨ ⊕-shrink (f zero) (f (suc i)) _ ⟩
  f (suc i) ∎

fromΠ-$$ : (f : OFF m n) → fromΠ (f $$_) ($$-≤ f) ≡ f
fromΠ-$$ f = $$-injective (fromΠ (f $$_) ($$-≤ f)) f ($$-fromΠ (f $$_) ($$-≤ f))

0th-const : 0th {m} {n} $$_ ≗ const zero
0th-const zero = refl
0th-const (suc i) = 0th-const i

pick-const : ∀ i → pick {m} {n} i $$_ ≗ const i
pick-const zero = 0th-const
pick-const (suc i) = cong suc Fun.∘ pick-const i

first-∘ : (f : OFF k l) (g : OFF m n) → first l ∘ f ≡ stack f g ∘ first k
first-∘ [] _ = empty-universal _ ∙ empty-universal _ ⋆
first-∘ (n∷ f) g = cong n∷_ (first-∘ f g)
first-∘ (a∷ f) g = cong a∷_ (first-∘ f g)

stack-id-empty : subsf₁ (+-identityʳ m) (stack id empty) ≡ first {n} m
stack-id-empty {zero} = subsf-refl empty
stack-id-empty {suc m} = cong (a∷_ ∘′ n∷_) stack-id-empty

stack-assoc : (f : OFF i j) (g : OFF k l) (h : OFF m n) →
              subsf (+-assoc i k m) (+-assoc j l n) (stack (stack f g) h) ≡
                                                     stack f (stack g h)
stack-assoc [] g h = subsf-refl (stack g h)
stack-assoc (n∷ f) g h = cong n∷_ (stack-assoc f g h)
stack-assoc (a∷ f) g h = cong a∷_ (stack-assoc f g h)
