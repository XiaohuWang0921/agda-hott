{-# OPTIONS --without-K --safe #-}

module HoTT.OFF.Properties where

open import Data.Nat.Base hiding (_≤_)
open import Data.Fin.Base hiding (pred; _+_)
open import Data.Nat.Properties hiding (suc-injective)
open import Data.Fin.Properties using (suc-injective)
open import HoTT.OFF
open import HoTT.EqNotation
open import Function.Base as Fun hiding (id; _∘_)
open import Relation.Binary
open import Relation.Nullary
open import Data.Product

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

stack-id : stack (id {m}) (id {n}) ≡ id
stack-id {zero} = refl
stack-id {suc m} = cong (a∷_ ∘′ n∷_) (stack-id {m})

stack-∘ : (f : OFF j k) (g : OFF i j) (f′ : OFF m n) (g′ : OFF l m) →
          stack (f ∘ g) (f′ ∘ g′) ≡ stack f f′ ∘ stack g g′
stack-∘ (n∷ f) g f′ g′ = cong n∷_ (stack-∘ f g f′ g′)
stack-∘ [] [] _ _ = refl
stack-∘ (a∷ f) (n∷ g) f′ g′ = stack-∘ f g f′ g′
stack-∘ f @ (a∷ _) (a∷ g) f′ g′ = cong a∷_ (stack-∘ f g f′ g′)

stack-stackˡ : (f : OFF i j) (g : OFF k l) (h : OFF m n) → stack (stack f g) h ≡
               subsf (+-assoc i k m ⋆) (+-assoc j l n ⋆) (stack f (stack g h))
stack-stackˡ [] g h = subsf-refl (stack g h) ⋆
stack-stackˡ (n∷ f) g h = cong n∷_ (stack-stackˡ f g h)
stack-stackˡ (a∷ f) g h = cong a∷_ (stack-stackˡ f g h)

stack-stackʳ : (f : OFF i j) (g : OFF k l) (h : OFF m n) → stack f (stack g h) ≡
               subsf (+-assoc i k m) (+-assoc j l n) (stack (stack f g) h)
stack-stackʳ [] g h = subsf-refl (stack g h) ⋆
stack-stackʳ (n∷ f) g h = cong n∷_ (stack-stackʳ f g h)
stack-stackʳ (a∷ f) g h = cong a∷_ (stack-stackʳ f g h)

stack-subsf : ∀ {o p} .(i≡m : i ≡ m) .(j≡n : j ≡ n) .(k≡o : k ≡ o) .(l≡p : l ≡ p) f g →
              stack (subsf i≡m j≡n f) (subsf k≡o l≡p g) ≡
              subsf (cong₂ _+_ i≡m k≡o) (cong₂ _+_ j≡n l≡p) (stack f g)
stack-subsf {_} {_} {suc _} {suc _} i≡m sj≡sn k≡o l≡p (n∷ f) g = cong n∷_ (stack-subsf i≡m (cong pred sj≡sn) k≡o l≡p f g)
stack-subsf {zero} {zero} {zero} {zero} _ _ _ _ [] _ = refl
stack-subsf {suc _} {suc _} {suc _} {suc _} si≡sm j≡n k≡o l≡p (a∷ f) g = cong a∷_ (stack-subsf (cong pred si≡sm) j≡n k≡o l≡p f g)

stack-subsf₁ : .(i≡k : i ≡ k) .(j≡l : j ≡ l) (f : OFF i m) (g : OFF j n) →
               stack (subsf₁ i≡k f) (subsf₁ j≡l g) ≡
               subsf₁ (cong₂ _+_ i≡k j≡l) (stack f g)
stack-subsf₁ i≡k j≡l = stack-subsf i≡k refl j≡l refl

stack-subsf₂ : .(k≡m : k ≡ m) .(l≡n : l ≡ n) (f : OFF i k) (g : OFF j l) →
               stack (subsf₂ k≡m f) (subsf₂ l≡n g) ≡
               subsf₂ (cong₂ _+_ k≡m l≡n) (stack f g)
stack-subsf₂ k≡m = stack-subsf refl k≡m refl

stack-subsfˡ : .(i≡k : i ≡ k) .(j≡l : j ≡ l) (f : OFF i j) (g : OFF m n) →
               stack (subsf i≡k j≡l f) g ≡ subsf (cong (_+ m) i≡k) (cong (_+ n) j≡l) (stack f g)
stack-subsfˡ i≡k j≡l f g = cong (stack _) (subsf-refl g) ⋆ ∙
                           stack-subsf i≡k j≡l refl refl f g

stack-subsfʳ : .(k≡m : k ≡ m) .(l≡n : l ≡ n) (f : OFF i j) (g : OFF k l) →
               stack f (subsf k≡m l≡n g) ≡ subsf (cong (i +_) k≡m) (cong (j +_) l≡n) (stack f g)
stack-subsfʳ k≡m l≡n f g = cong (flip stack _) (subsf-refl f) ⋆ ∙
                           stack-subsf refl refl k≡m l≡n f g

shiftˡ-shiftʳ : (f : OFF k l) (g : OFF m n) →
                shiftˡ n f ∘ shiftʳ k g ≡ shiftʳ l g ∘ shiftˡ m f
shiftˡ-shiftʳ f g = begin
  shiftˡ _ f ∘ shiftʳ _ g ≡⟨⟩
  stack id f ∘ stack g id ≡˘⟨ stack-∘ id g f id ⟩
  stack (id ∘ g) (f ∘ id) ≡⟨ cong (stack _) (∘-identityʳ f) ⟩
  stack (id ∘ g) f ≡⟨ cong (flip stack _) (∘-identityˡ g) ⟩
  stack g f ≡˘⟨ cong (flip stack _) (∘-identityʳ g) ⟩
  stack (g ∘ id) f ≡˘⟨ cong (stack _) (∘-identityˡ f) ⟩
  stack (g ∘ id) (id ∘ f) ≡⟨ stack-∘ g id id f ⟩
  stack g id ∘ stack id f ≡⟨⟩
  shiftʳ _ g ∘ shiftˡ _ f ∎

shiftˡ-∘ : ∀ k (f : OFF m n) (g : OFF l m) →
           shiftˡ k (f ∘ g) ≡ shiftˡ k f ∘ shiftˡ k g
shiftˡ-∘ _ f g = cong (flip stack (f ∘ g)) (∘-identityˡ id) ⋆ ∙ stack-∘ id id f g

shiftʳ-∘ : ∀ k (f : OFF m n) (g : OFF l m) →
           shiftʳ k (f ∘ g) ≡ shiftʳ k f ∘ shiftʳ k g
shiftʳ-∘ _ f g = cong (stack (f ∘ g)) (∘-identityʳ id) ⋆ ∙ stack-∘ f g id id

embed₂-∘ : (i : Fin l) (f : OFF m n) → embed₂ i ∘ f ≡ l ℕ* f ∘ embed₂ i
embed₂-∘ {suc l} zero f = first-∘ f (l ℕ* f)
embed₂-∘ {suc l} (suc i) f = begin
  embed₂ (suc i) ∘ f ≡⟨⟩
  stack empty (embed₂ i) ∘ f ≡⟨⟩
  stack empty (embed₂ i) ∘ stack [] f ≡˘⟨ stack-∘ empty [] (embed₂ i) f ⟩
  stack (empty ∘ []) (embed₂ i ∘ f) ≡⟨ cong (flip stack (embed₂ i ∘ f)) (empty-universal _) ⟩
  stack empty (embed₂ i ∘ f) ≡⟨ cong (stack _) (embed₂-∘ i f) ⟩
  stack empty (l ℕ* f ∘ embed₂ i) ≡˘⟨ cong (flip stack _) (empty-universal (f ∘ empty)) ⟩
  stack (f ∘ empty) (l ℕ* f ∘ embed₂ i) ≡⟨ stack-∘ f _ (l ℕ* f) _ ⟩
  stack f (l ℕ* f) ∘ stack empty (embed₂ i) ≡⟨⟩
  suc l ℕ* f ∘ embed₂ (suc i) ∎

ℕ*-pick : (i : Fin n) → subsf₁ (*-identityʳ m) (m ℕ* pick i) ≡ embed₁ i
ℕ*-pick {m = zero} _ = subsf-refl []
ℕ*-pick {m = suc m} i = begin
  subsf₁ (*-identityʳ (suc m)) (suc m ℕ* pick i) ≡⟨⟩
  subsf₁ (cong suc (*-identityʳ m)) (stack (pick i) (m ℕ* pick i)) ≡˘⟨ stack-subsf₁ refl (*-identityʳ m) (pick i) (m ℕ* pick i) ⟩
  stack (subsf₁ refl (pick i)) (subsf₁ (*-identityʳ m) (m ℕ* pick i)) ≡⟨ cong (flip stack _) (subsf-refl (pick i)) ⟩
  stack (pick i) (subsf₁ (*-identityʳ m) (m ℕ* pick i)) ≡⟨ cong (stack (pick i)) (ℕ*-pick i) ⟩
  stack (pick i) (embed₁ i) ≡⟨⟩
  embed₁ i ∎

ℕ*-id : ∀ m → m ℕ* (id {n}) ≡ id
ℕ*-id zero = refl
ℕ*-id {n} (suc m) = cong (stack id) (ℕ*-id m) ∙ stack-id {n}

ℕ*-∘ : ∀ k (f : OFF m n) (g : OFF l m) → k ℕ* (f ∘ g) ≡ k ℕ* f ∘ k ℕ* g
ℕ*-∘ zero _ _ = refl
ℕ*-∘ (suc k) f g = cong (stack (f ∘ g)) (ℕ*-∘ k f g) ∙ stack-∘ f g _ _

stack-ℕ* : ∀ k l (f : OFF m n) → stack (k ℕ* f) (l ℕ* f) ≡
           subsf (*-distribʳ-+ m k l) (*-distribʳ-+ n k l) ((k + l) ℕ* f)
stack-ℕ* zero _ _ = subsf-refl _ ⋆
stack-ℕ* {m} {n} (suc k) l f = begin
  stack (suc k ℕ* f) (l ℕ* f) ≡⟨⟩
  stack (stack f (k ℕ* f)) (l ℕ* f) ≡⟨ stack-stackˡ f _ _ ⟩
  subsf _ _ (stack f (stack (k ℕ* f) (l ℕ* f))) ≡⟨ cong (subsf _ _ ∘′ stack f) (stack-ℕ* k l f) ⟩
  subsf _ _ (stack f (subsf _ _ ((k + l) ℕ* f))) ≡⟨ cong (subsf _ _) (stack-subsfʳ (*-distribʳ-+ m k l) _ f _) ⟩
  subsf _ _ (subsf _ _ (stack f ((k + l) ℕ* f))) ≡˘⟨ subsf-trans _ _ _ _ _ ⟩
  subsf _ _ (stack f ((k + l) ℕ* f)) ≡⟨⟩
  subsf _ _ ((suc k + l) ℕ* f) ∎

ℕ*-ℕ* : ∀ k l (f : OFF m n) → k ℕ* l ℕ* f ≡
        subsf (*-assoc k l m) (*-assoc k l n) ((k * l) ℕ* f)
ℕ*-ℕ* zero _ _ = subsf-refl _ ⋆
ℕ*-ℕ* (suc k) l f = begin
  suc k ℕ* l ℕ* f ≡⟨⟩
  stack (l ℕ* f) (k ℕ* l ℕ* f) ≡⟨ cong (stack _) (ℕ*-ℕ* k l f) ⟩
  stack (l ℕ* f) (subsf _ _ ((k * l) ℕ* f)) ≡⟨ stack-subsfʳ _ _ (l ℕ* f) _ ⟩
  subsf _ _ (stack (l ℕ* f) ((k * l) ℕ* f)) ≡⟨ cong (subsf _ _) (stack-ℕ* l (k * l) f) ⟩
  subsf _ _ (subsf _ _ ((suc k * l) ℕ* f)) ≡˘⟨ subsf-trans _ _ _ _ _ ⟩
  subsf _ _ ((suc k * l) ℕ* f) ∎

skip-switch : ∀ i (j : Fin (suc n)) → skip i ∘ skip j ≡
              let j′ , i′ = switch i j
              in  skip j′ ∘ skip i′
skip-switch zero j = cong n∷_ (∘-identityˡ (skip j) ∙ ∘-identityʳ _ ⋆)
skip-switch (suc i) zero = cong n∷_ (∘-identityʳ (skip i) ∙ ∘-identityˡ _ ⋆)
skip-switch {suc _} (suc i) (suc j) = cong (a∷_ ∘′ n∷_) (skip-switch i j)
