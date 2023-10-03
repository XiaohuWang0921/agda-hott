{-# OPTIONS --without-K --safe #-}

module Data.Fin.Properties where

open import Data.Fin.Base as Fin
open import Relation.Equality.Base
open import Data.Sum.Base as Sum
open import Data.Product.Base as Product
open import Data.Nat.Base
open import Relation.Reasoning.Setoid
open import Relation.Equality.Base
open import Universe.Set
open import Data.Sum.Properties as Sumᵖ
open import Data.Product.Properties as Productᵖ
open import Category.Functor hiding (_∘_)
open import Category.Natural hiding (id; _∘_)
open import Data.Empty.Base

private
  instance
    ≡setoid : ∀ {a} {A : Set a} → _
    ≡setoid {A = A} = setoid A

splitAt∘inj+ : ∀ {m} n → splitAt m ∘ inj+ n ≗ inj₁
splitAt∘inj+ _ zero = refl
splitAt∘inj+ n (suc i) = Sum.map suc id =$= splitAt∘inj+ n i

splitAt∘ℕ+ : ∀ m {n} → splitAt m ∘ (_ℕ+_ m {n}) ≗ inj₂
splitAt∘ℕ+ 0 _ = refl
splitAt∘ℕ+ (suc m) i = Sum.map suc id =$= splitAt∘ℕ+ m i

join∘splitAt : ∀ m {n} → join ∘ splitAt m {n} ≗ id
join∘splitAt 0 _ = refl
join∘splitAt (suc _) zero = refl
join∘splitAt (suc m) (suc i) with splitAt m i in eq
... | inj₁ j =
  join (Sum.map suc id (inj₁ j)) ≡⟨⟩
  join (inj₁ (suc j)) ≡⟨⟩
  inj+ _ (suc j) ≡⟨⟩
  suc (inj+ _ j) ≡⟨⟩
  suc (join (inj₁ j)) ≡˘⟨ suc =$= join =$= eq ⟩
  suc (join (splitAt m i)) ≡⟨ suc =$= join∘splitAt m i ⟩
  suc i ∎
--   where
--     open Relation.Reasoning (_≡_ {A = Fin _})
--     open Equiv refl trig
... | inj₂ j =
  join (Sum.map suc id (inj₂ j)) ≡⟨⟩
  join (inj₂ j) ≡⟨⟩
  suc m ℕ+ j ≡⟨⟩
  suc (m ℕ+ j) ≡⟨⟩
  suc (join (inj₂ j)) ≡˘⟨ suc =$= join =$= eq ⟩
  suc (join (splitAt m i)) ≡⟨ suc =$= join∘splitAt m i ⟩
  suc i ∎
--   where
--     open Relation.Reasoning (_≡_ {A = Fin _})
--     open Equiv refl trig

splitAt∘join : ∀ {m n} → splitAt m {n} ∘ join ≗ id
splitAt∘join (inj₁ i) = splitAt∘inj+ _ i
splitAt∘join (inj₂ i) = splitAt∘ℕ+ _ i

combine∘extract : ∀ m {n} → uncurry combine ∘ extract m {n} ≗ id
combine∘extract (suc m) {n} i with splitAt n i in eq
... | inj₁ j =
  uncurry combine (zero {m} , j) ≡⟨⟩
  combine {suc m} zero j ≡⟨⟩
  inj+ (m * n) j ≡⟨⟩
  join (inj₁ j) ≡˘⟨ join =$= eq ⟩
  join (splitAt n i) ≡⟨ join∘splitAt n i ⟩
  i ∎
--   where
--     open Relation.Reasoning (_≡_ {A = Fin _})
--     open Equiv refl trig
... | inj₂ j with extract m j in eq'
... | h , l =
  uncurry combine (Product.map suc id (h , l)) ≡⟨⟩
  uncurry combine (suc h , l) ≡⟨⟩
  combine (suc h) l ≡⟨⟩
  n ℕ+ combine h l ≡⟨⟩
  n ℕ+ uncurry combine (h , l) ≡˘⟨ n ℕ+_ =$= uncurry combine =$= eq' ⟩
  n ℕ+ uncurry combine (extract m j) ≡⟨ n ℕ+_ =$= combine∘extract m j ⟩
  n ℕ+ j ≡⟨⟩
  join (inj₂ j) ≡˘⟨ join =$= eq ⟩
  join (splitAt n i) ≡⟨ join∘splitAt n i ⟩
  i ∎
--   where
--     open Relation.Reasoning (_≡_ {A = Fin _})
--     open Equiv refl trig

extract∘combine : ∀ {m n} → extract m {n} ∘₂ combine ≗₂ _,_
extract∘combine {suc m} {n} zero j =
  extract _ (combine {suc m} zero j) ≡⟨⟩
  extract _ (inj+ _ j) ≡⟨⟩
  < zero ,_ ⊹ (λ k → Product.map suc id (extract m k)) > (splitAt n (inj+ _ j)) ≡⟨ < _ ⊹ _ > =$= splitAt∘inj+ (m * n) j ⟩
  < zero ,_ ⊹ (λ k → Product.map suc id (extract m k)) > (inj₁ j) ≡⟨⟩
  zero , j ∎
--   where
--     open Relation.Reasoning (_≡_ {A = Fin (suc m) × Fin n})
--     open Equiv refl trig
extract∘combine {suc m} {n} (suc i) j =
  extract _ (combine (suc i) j) ≡⟨⟩
  extract _ (n ℕ+ combine i j) ≡⟨⟩
  < zero ,_ ⊹ (λ k → Product.map suc id (extract m k)) > (splitAt n (n ℕ+ combine i j)) ≡⟨ < _ ⊹ _ > =$= splitAt∘ℕ+ n (combine i j) ⟩
  < zero ,_ ⊹ (λ k → Product.map suc id (extract m k)) > (inj₂ (combine i j)) ≡⟨⟩
  Product.map suc id (extract m (combine i j)) ≡⟨ Product.map suc id =$= extract∘combine i j ⟩
  Product.map suc id (i , j) ≡⟨⟩
  suc i , j ∎
  -- where                         
  --   open Relation.Reasoning (_≡_ {A = Fin (suc m) × Fin n})
  --   open Equiv refl trig

private
  variable
    k l m n o p : ℕ

suc-injective : {i j : Fin n} → Fin.suc i ≡ suc j → i ≡ j
suc-injective refl = refl

++-cong : {f g : Fin l → Fin n} {h i : Fin m → Fin n} → f ≗ g → h ≗ i → f ++ h ≗ g ++ i
++-cong f≗g h≗i j = <⊹>-cong f≗g h≗i (splitAt _ j)

++-∘ : (f : Fin m → Fin n) (g : Fin k → Fin m) (h : Fin l → Fin m) → f ∘ (g ++ h) ≗ f ∘ g ++ f ∘ h
++-∘ f g h i = <⊹>-∘ f g h (splitAt _ i)

++-inj+ : (f : Fin l → Fin n) (g : Fin m → Fin n) → (f ++ g) ∘ inj+ m ≗ f
++-inj+ f g i = < f ⊹ g > =$= splitAt∘inj+ _ i

++-ℕ+ : (f : Fin l → Fin n) (g : Fin m → Fin n) → (f ++ g) ∘ (l ℕ+_) ≗ g
++-ℕ+ f g i = < f ⊹ g > =$= splitAt∘ℕ+ _ i

∣-cong : {f g : Fin k → Fin m} {h i : Fin l → Fin n} → f ≗ g → h ≗ i → f ∣ h ≗ g ∣ i
∣-cong f≗g h≗i j = join =$= Sumᵖ.map-cong f≗g h≗i (splitAt _ j)

∣-∘ : (f : Fin n → Fin p) (g : Fin m → Fin o) (h : Fin l → Fin n) (i : Fin k → Fin m) → f ∘ h ∣ g ∘ i ≗ (f ∣ g) ∘ (h ∣ i)
∣-∘ f g h i j = join =$=
  (Sum.map (f ∘ h) (g ∘ i) (splitAt _ j) ≈⟨ Sumᵖ.map-∘ f h g i (splitAt _ j) ⟩
  Sum.map f g (Sum.map h i (splitAt _ j)) ≈˘⟨ Sum.map f g =$= splitAt∘join (Sum.map h i (splitAt _ j)) ⟩
  Sum.map f g (splitAt _ (join (Sum.map h i (splitAt _ j)))) ∎)

∣-id : id {A = Fin m} ∣ id {A = Fin n} ≗ id
∣-id {m} i =
  (id {A = Fin m} ∣ id) i ≡⟨⟩
  join (Sum.map id id (splitAt m i)) ≈⟨ join =$= Sumᵖ.map-id (splitAt m i) ⟩
  join (splitAt m i) ≈⟨ join∘splitAt m i ⟩
  i ∎

**-cong : {f g : Fin l → Fin m} {h i : Fin l → Fin n} → f ≗ g → h ≗ i → f ** h ≗ g ** i
**-cong f≗g h≗i j = cong₂ combine (f≗g j) (h≗i j)

**-∘ : (f : Fin l → Fin m) (g : Fin l → Fin n) (h : Fin k → Fin l) → (f ** g) ∘ h ≡ f ∘ h ** g ∘ h
**-∘ f g h = refl

∙-cong : {f g : Fin k → Fin m} {h i : Fin l → Fin n} → f ≗ g → h ≗ i → f ∙ h ≗ g ∙ i
∙-cong f≗g h≗i j = uncurry combine =$= Productᵖ.map-cong f≗g h≗i (extract _ j)

∙-∘ : (f : Fin n → Fin p) (g : Fin m → Fin o) (h : Fin l → Fin n) (i : Fin k → Fin m) → f ∘ h ∙ g ∘ i ≗ (f ∙ g) ∘ (h ∙ i)
∙-∘ f g h i j = uncurry combine =$= Product.map f g =$= sym (extract∘combine _ _)

∙-id : id {A = Fin m} ∙ id {A = Fin n} ≗ id
∙-id {m} = combine∘extract m

+-functorˡ : ℕ → Functor FinCat FinCat
+-functorˡ n = record
  { obj = _+ n
  ; hom = record
    { func = _∣ id
    ; cong = flip ∣-cong λ _ → refl
    }
  ; mor-∘ = λ f g → ∣-∘ f id g id
  ; mor-id = λ {m} → ∣-id {m = m}
  }

+-functorʳ : ℕ → Functor FinCat FinCat
+-functorʳ m = record
  { obj = m +_
  ; hom = record
    { func = id ∣_
    ; cong = ∣-cong λ _ → refl
    }
  ; mor-∘ = λ f g → ∣-∘ id f id g
  ; mor-id = λ {n} → ∣-id {n = n}
  }

+-naturalˡ : (Fin m → Fin n) → +-functorˡ m ⇉ +-functorˡ n
+-naturalˡ f = record
  { at = λ _ → id ∣ f
  ; isNatural = λ g x →
    (id ∣ f) ((g ∣ id) x) ≈˘⟨ ∣-∘ id f g id x ⟩
    (id ∘ g ∣ f ∘ id) x ≡⟨⟩
    (g ∣ f) x ≡⟨⟩
    (g ∘ id ∣ id ∘ f) x ≈⟨ ∣-∘ g id id f x ⟩
    (g ∣ id) ((id ∣ f) x) ∎
  }

+-naturalʳ : (Fin m → Fin n) → +-functorʳ m ⇉ +-functorʳ n
+-naturalʳ f = record
  { at = λ _ → f ∣ id
  ; isNatural = λ g x →
    (f ∣ id) ((id ∣ g) x) ≈˘⟨ ∣-∘ f id id g x ⟩
    (f ∘ id ∣ id ∘ g) x ≡⟨⟩
    (f ∣ g) x ≡⟨⟩
    (id ∘ f ∣ g ∘ id) x ≈⟨ ∣-∘ id g f id x ⟩
    (id ∣ g) ((f ∣ id) x) ∎
  }
  
*-functorˡ : ℕ → Functor FinCat FinCat
*-functorˡ n = record
  { obj = _* n
  ; hom = record
    { func = _∙ id
    ; cong = flip (∙-cong {h = id}) λ _ → refl
    }
  ; mor-∘ = λ f g → ∙-∘ f id g id
  ; mor-id = λ {m} → ∙-id {m = m}
  }

*-functorʳ : ℕ → Functor FinCat FinCat
*-functorʳ m = record
  { obj = m *_
  ; hom = record
    { func = id {A = Fin m} ∙_
    ; cong = ∙-cong {k = m} {f = id} λ _ → refl
    }
  ; mor-∘ = λ f g → ∙-∘ {n = m} id f id g
  ; mor-id = λ {n} → ∙-id {m = m} {n = n}
  }

*-naturalˡ : (Fin m → Fin n) → *-functorˡ m ⇉ *-functorˡ n
*-naturalˡ f = record
  { at = λ m → id {A = Fin m} ∙ f
  ; isNatural = λ {m n} g x →
    (id {A = Fin n} ∙ f) ((g ∙ id) x) ≈˘⟨ ∙-∘ id f g id x ⟩
    (id ∘ g ∙ f ∘ id) x ≡⟨⟩
    (g ∙ f) x ≡⟨⟩
    (g ∘ id ∙ id ∘ f) x ≈⟨ ∙-∘ g id id f x ⟩
    (g ∙ id) ((id {A = Fin m} ∙ f) x) ∎
  }

*-naturalʳ : (Fin m → Fin n) → *-functorʳ m ⇉ *-functorʳ n
*-naturalʳ {m} {n} f = record
  { at = λ _ → f ∙ id
  ; isNatural = λ g x →
    (f ∙ id) ((id {A = Fin m} ∙ g) x) ≈˘⟨ ∙-∘ f id id g x ⟩
    (f ∘ id ∙ id ∘ g) x ≡⟨⟩
    (f ∙ g) x ≡⟨⟩
    (id ∘ f ∙ g ∘ id) x ≈⟨ ∙-∘ id g f id x ⟩
    (id {A = Fin n} ∙ g) ((f ∙ id) x) ∎
  }

-- swap∘swap : uncurry swap ∘₂ swap {n} ≗₂ _,_
-- swap∘swap {suc _} zero j = refl
-- swap∘swap (suc i) zero = refl
-- swap∘swap (suc i) (suc j) = Product.map suc suc =$= swap∘swap i j

swap∘punchOut : {i j : Fin (suc n)} .(i≢j : i ≢ j) →
                swap i (punchOut i≢j) ≡ (j , punchOut (i≢j ∘ sym))
swap∘punchOut {_} {zero} {zero} 0≢0 = ⊥-elim (0≢0 refl)
swap∘punchOut {suc _} {zero} {suc _} _ = refl
swap∘punchOut {suc _} {suc _} {zero} _ = refl
swap∘punchOut {suc _} {suc _} {suc _} si≢sj = Product.map suc suc =$= swap∘punchOut (si≢sj ∘ cong suc)

punchIn∘punchOut : {i j : Fin (suc n)} .(i≢j : i ≢ j) →
                   punchIn i (punchOut i≢j) ≡ j
punchIn∘punchOut i≢j = proj₁ =$= swap∘punchOut i≢j

punchIn-injective : ∀ i (j k : Fin n) → punchIn i j ≡ punchIn i k → j ≡ k
punchIn-injective {suc _} zero _ _ sj≡sk = suc-injective sj≡sk
punchIn-injective (suc _) zero zero _ = refl
punchIn-injective (suc _) zero (suc _) 0≡s = (λ ()) $ 0≡s
punchIn-injective (suc _) (suc _) zero s≡0 = (λ ()) $ s≡0
punchIn-injective (suc i) (suc j) (suc k) eq = suc =$= punchIn-injective i j k (suc-injective eq)

punchIn-≢ : ∀ i (j : Fin n) → i ≢ punchIn i j
punchIn-≢ {suc _} zero _ ()
punchIn-≢ (suc _) zero ()
punchIn-≢ (suc i) (suc j) eq = punchIn-≢ i j (suc-injective eq)

punchOut∘punchIn : ∀ i (j : Fin n) → punchOut (punchIn-≢ i j) ≡ j
punchOut∘punchIn i j = punchIn-injective i (punchOut (punchIn-≢ i j)) j (punchIn∘punchOut (punchIn-≢ i j))

punchIn∘punchIn : ∀ i (j : Fin (suc n)) → punchIn i ∘ punchIn j ≗ punchIn (punchIn i j) ∘ punchIn (pinch j i)
punchIn∘punchIn {suc _} zero _ _ = refl
punchIn∘punchIn {suc _} (suc _) zero _ = refl
punchIn∘punchIn (suc _) (suc _) zero = refl
punchIn∘punchIn (suc i) (suc j) (suc k) = suc =$= punchIn∘punchIn i j k
