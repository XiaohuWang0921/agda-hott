{-# OPTIONS --without-K --safe #-}

module Data.Fin.Properties where

open import Data.Fin.Base as Fin
open import Relation.Equality.Base hiding (cong)
open import Data.Sum.Base as Sum
open import Data.Product.Base as Product
open import Data.Nat.Base as ℕ hiding (_≟_)
open import Universe.Set
open import Data.Sum.Properties as Sumᵖ
open import Data.Product.Properties as Productᵖ
open import Category.Functor hiding (_∘_)
open import Category.Natural hiding (id; _∘_)
open import Data.Empty.Base
open import Data.Bool.Base hiding (_≟_)
open import Data.Unit.Core
open import Relation.Reasoning.Set
open import Category.FunCat
open import Universe.Setoid using (func; cong)

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
... | inj₂ j =
  join (Sum.map suc id (inj₂ j)) ≡⟨⟩
  join (inj₂ j) ≡⟨⟩
  suc m ℕ+ j ≡⟨⟩
  suc (m ℕ+ j) ≡⟨⟩
  suc (join (inj₂ j)) ≡˘⟨ suc =$= join =$= eq ⟩
  suc (join (splitAt m i)) ≡⟨ suc =$= join∘splitAt m i ⟩
  suc i ∎

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

extract∘combine : ∀ {m n} → extract m {n} ∘₂ combine ≗₂ _,_
extract∘combine {suc m} {n} zero j =
  extract _ (combine {suc m} zero j) ≡⟨⟩
  extract _ (inj+ _ j) ≡⟨⟩
  < zero ,_ ⊹ (λ k → Product.map suc id (extract m k)) > (splitAt n (inj+ _ j)) ≡⟨ < _ ⊹ _ > =$= splitAt∘inj+ (m * n) j ⟩
  < zero ,_ ⊹ (λ k → Product.map suc id (extract m k)) > (inj₁ j) ≡⟨⟩
  zero , j ∎
extract∘combine {suc m} {n} (suc i) j =
  extract _ (combine (suc i) j) ≡⟨⟩
  extract _ (n ℕ+ combine i j) ≡⟨⟩
  < zero ,_ ⊹ (λ k → Product.map suc id (extract m k)) > (splitAt n (n ℕ+ combine i j)) ≡⟨ < _ ⊹ _ > =$= splitAt∘ℕ+ n (combine i j) ⟩
  < zero ,_ ⊹ (λ k → Product.map suc id (extract m k)) > (inj₂ (combine i j)) ≡⟨⟩
  Product.map suc id (extract m (combine i j)) ≡⟨ Product.map suc id =$= extract∘combine i j ⟩
  Product.map suc id (i , j) ≡⟨⟩
  suc i , j ∎

private
  variable
    k l m n o p : ℕ

zero≢suc : {i : Fin n} → zero ≢ suc i
zero≢suc ()

suc-injective : {i j : Fin n} → Fin.suc i ≡ suc j → i ≡ j
suc-injective refl = refl

≟-Reflects-≡ : (i j : Fin n) → (i ≟ j) Reflects (i ≡ j)
≟-Reflects-≡ zero zero = refl
≟-Reflects-≡ zero (suc _) = zero≢suc
≟-Reflects-≡ (suc _) zero = zero≢suc ∘ sym
≟-Reflects-≡ (suc i) (suc j) with i ≟ j | ≟-Reflects-≡ i j
... | false | i≢j = i≢j ∘ suc-injective
... | true  | i≡j = suc =$= i≡j

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

∣-congˡ : {f g : Fin k → Fin m} {h : Fin l → Fin n} → f ≗ g → f ∣ h ≗ g ∣ h
∣-congˡ f≗g = ∣-cong f≗g λ _ → refl

∣-congʳ : {f : Fin k → Fin m} {h i : Fin l → Fin n} → h ≗ i → f ∣ h ≗ f ∣ i
∣-congʳ = ∣-cong λ _ → refl

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

∙-congˡ : {f g : Fin k → Fin m} {h : Fin l → Fin n} → f ≗ g → f ∙ h ≗ g ∙ h
∙-congˡ {h = h} f≗g = ∙-cong {h = h} f≗g λ _ → refl

∙-congʳ : {f : Fin k → Fin m} {h i : Fin l → Fin n} →  h ≗ i → f ∙ h ≗ f ∙ i
∙-congʳ {f = f} = ∙-cong {f = f} λ _ → refl

∙-∘ : (f : Fin n → Fin p) (g : Fin m → Fin o) (h : Fin l → Fin n) (i : Fin k → Fin m) → f ∘ h ∙ g ∘ i ≗ (f ∙ g) ∘ (h ∙ i)
∙-∘ f g h i j = uncurry combine =$= Product.map f g =$= sym (extract∘combine _ _)

∙-id : id {A = Fin m} ∙ id {A = Fin n} ≗ id
∙-id {m} = combine∘extract m

+-functor : Functor FinCat (FunCat FinCat FinCat)
+-functor .obj m .obj = m +_
+-functor .obj _ .hom .func = id ∣_
+-functor .obj _ .hom .cong = ∣-congʳ
+-functor .obj _ .mor-∘ f g = ∣-∘ id f id g
+-functor .obj _ .mor-id {n} = ∣-id {n = n}
+-functor .hom .func f .at n = f ∣ id
+-functor .hom .func f .isNatural g i =
  (f ∣ id) ((id ∣ g) i) ≡˘⟨ ∣-∘ f id id g i ⟩
  (f ∘ id ∣ id ∘ g) i ≡⟨⟩
  (f ∣ g) i ≡⟨⟩
  (id ∘ f ∣ g ∘ id) i ≡⟨ ∣-∘ id g f id i ⟩
  (id ∣ g) ((f ∣ id) i) ∎
+-functor .hom .cong f≈g _ = ∣-congˡ f≈g
+-functor .mor-∘ f g _ = ∣-∘ f id g id
+-functor .mor-id {m} _ = ∣-id {m = m}

+-functorʳ : ℕ → Functor FinCat FinCat
+-functorʳ = +-functor <$>_

+-functorˡ : ℕ → Functor FinCat FinCat
+-functorˡ = Λ +-functor -_

inj+-natural : ∀ n → Id ⇉ +-functorˡ n
inj+-natural n .at _ = inj+ n
inj+-natural n .isNatural f i = join =$= Sum.map f id =$= sym (splitAt∘inj+ n i)

ℕ+-natural : ∀ m → Id ⇉ +-functorʳ m
ℕ+-natural m .at _ = m ℕ+_
ℕ+-natural m .isNatural f i = join =$= Sum.map id f =$= sym (splitAt∘ℕ+ m i)

*-functor : Functor FinCat (FunCat FinCat FinCat)
*-functor .obj m .obj = m *_
*-functor .obj m .hom .func = id {A = Fin m} ∙_
*-functor .obj m .hom .cong = ∙-congʳ {k = m} {f = id}
*-functor .obj m .mor-∘ f g = ∙-∘ {n = m} id f id g
*-functor .obj m .mor-id {n} = ∙-id {m = m} {n = n}
*-functor .hom .func f .at n = f ∙ id
*-functor .hom {m} {n} .func f .isNatural g i =
  (f ∙ id) ((id {A = Fin m} ∙ g) i) ≡˘⟨ ∙-∘ f id id g i ⟩
  (f ∘ id ∙ id ∘ g) i ≡⟨⟩
  (f ∙ g) i ≡⟨⟩
  (id ∘ f ∙ g ∘ id) i ≡⟨ ∙-∘ id g f id i ⟩
  (id {A = Fin n} ∙ g) ((f ∙ id) i) ∎
*-functor .hom .cong f≈g _ = ∙-congˡ {h = id} f≈g
*-functor .mor-∘ f g _ = ∙-∘ f id g id
*-functor .mor-id {m} _ = ∙-id {m = m}

*-functorʳ : ℕ → Functor FinCat FinCat
*-functorʳ = *-functor <$>_

*-functorˡ : ℕ → Functor FinCat FinCat
*-functorˡ = Λ *-functor -_

extract-naturalˡ : ∀ n → *-functorˡ n ⇉ Id
extract-naturalˡ _ .at m = proj₁ ∘ extract m
extract-naturalˡ _ .isNatural _ _ = proj₁ =$= extract∘combine _ _

extract-naturalʳ : ∀ n → *-functorʳ n ⇉ Id
extract-naturalʳ m .at _ = proj₂ ∘ extract m
extract-naturalʳ m .isNatural _ i = proj₂ =$= extract∘combine (proj₁ (extract m i)) _

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

-- punchOut∘punchIn : ∀ i (j : Fin n) → punchOut (punchIn-≢ i j) ≡ j
-- punchOut∘punchIn i j = punchIn-injective i (punchOut (punchIn-≢ i j)) j (punchIn∘punchOut (punchIn-≢ i j))

punchIn∘punchIn : ∀ i (j : Fin (suc n)) → punchIn i ∘ punchIn j ≗ punchIn (punchIn i j) ∘ punchIn (pinch j i)
punchIn∘punchIn {suc _} zero _ _ = refl
punchIn∘punchIn {suc _} (suc _) zero _ = refl
punchIn∘punchIn (suc _) (suc _) zero = refl
punchIn∘punchIn (suc i) (suc j) (suc k) = suc =$= punchIn∘punchIn i j k

pinch∘pinch : ∀ (i : Fin n) j → pinch i ∘ pinch j ≗ pinch (pinch i j) ∘ pinch (punchIn j i)
pinch∘pinch {suc _} _ _ zero = refl
pinch∘pinch {suc _} _ zero (suc zero) = refl
pinch∘pinch zero (suc j) (suc zero) = refl
pinch∘pinch (suc zero) (suc j) (suc zero) = refl
pinch∘pinch (suc (suc _)) (suc j) (suc zero) = refl
pinch∘pinch zero zero (suc (suc k)) = refl
pinch∘pinch (suc i) zero (suc (suc k)) = refl
pinch∘pinch zero (suc j) (suc (suc k)) = refl
pinch∘pinch (suc i) (suc j) (suc (suc k)) = suc =$= pinch∘pinch i j (suc k)
