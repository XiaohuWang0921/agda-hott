{-# OPTIONS --without-K --safe #-}

module Data.Nat.Properties where

open import Data.Nat.Base
open import Data.Bool.Base as Bool hiding (_≟_; _≤?_; _≤_)
open import Relation.Equality.Base hiding (cong)
open import Universe.Set
open import Data.Empty.Base
open import Data.Unit.Core
open import Data.Bool.Properties as Boolₚ using (b≤true; false≤b)
open import Category.Base
open import Category.Functor hiding (_∘_)
open import Level
open import Universe.Setoid using (func; cong)
open import Category.FunCat
open import Category.Natural hiding (id; _∘_)

zero≢suc : ∀ {n} → zero ≢ suc n
zero≢suc ()

suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

pred≤pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
pred≤pred (s≤s m≤n) = m≤n

≤?-≤ : ∀ {k l m n} → k ≤ l → m ≤ n → (l ≤? m) Bool.≤ (k ≤? n)
≤?-≤ 0≤n _ = b≤true
≤?-≤ (s≤s k≤l) 0≤n = false≤b
≤?-≤ (s≤s k≤l) (s≤s m≤n) = ≤?-≤ k≤l m≤n

<?-≤ : ∀ {k l m n} → k ≤ l → m ≤ n → (l <? m) Bool.≤ (k <? n)
<?-≤ _ 0≤n = false≤b
<?-≤ 0≤n (s≤s m≤n) = b≤true
<?-≤ (s≤s k≤l) (s≤s m≤n) = <?-≤ k≤l m≤n

<?-Reflects-< : ∀ m n → (m <? n) Reflects (m < n)
<?-Reflects-< _ zero ()
<?-Reflects-< zero (suc _) = s≤s 0≤n
<?-Reflects-< (suc m) (suc n) with m <? n | <?-Reflects-< m n
... | false | m≮n = m≮n ∘ pred≤pred
... | true | m<n = s≤s m<n

≤?-Reflects-≤ : ∀ m n → (m ≤? n) Reflects (m ≤ n)
≤?-Reflects-≤ zero _ = 0≤n
≤?-Reflects-≤ (suc m) (suc n) with m ≤? n | ≤?-Reflects-≤ m n
... | false | m≰n = m≰n ∘ pred≤pred
... | true | m≤n = s≤s m≤n

≟-Reflects-≡ : ∀ m n → (m ≟ n) Reflects (m ≡ n)
≟-Reflects-≡ zero zero = refl
≟-Reflects-≡ zero (suc _) = zero≢suc
≟-Reflects-≡ (suc _) zero = zero≢suc ∘ sym
≟-Reflects-≡ (suc m) (suc n) with m ≟ n | ≟-Reflects-≡ m n
... | false | m≢n = m≢n ∘ suc-injective
... | true  | m≡n = suc =$= m≡n

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero} = 0≤n
≤-refl {suc n} = s≤s ≤-refl

≤-antisym : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
≤-antisym {zero} {zero} _ _ = refl
≤-antisym {suc m} {suc n} (s≤s m≤n) (s≤s n≤m) = suc =$= ≤-antisym m≤n n≤m

≤-trans : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
≤-trans 0≤n _ = 0≤n
≤-trans (s≤s l≤m) (s≤s m≤n) = s≤s (≤-trans l≤m m≤n)

<-suc : ∀ {n} → n < suc n
<-suc = ≤-refl

<⇒≤ : ∀ {m n} → m < n → m ≤ n
<⇒≤ {zero} (s≤s _) = 0≤n
<⇒≤ {suc _} (s≤s m<n) = s≤s (<⇒≤ m<n)

≤-Cat : Category 0ℓ 0ℓ 0ℓ
≤-Cat = Preorder _≤_ ≤-refl ≤-trans

suc-functor : Functor ≤-Cat ≤-Cat
suc-functor .obj = suc
suc-functor .hom .func = s≤s
suc-functor .hom .cong _ = tt
suc-functor .mor-∘ _ _ = tt
suc-functor .mor-id = tt

≤?-functor : Functor (Op ≤-Cat) (FunCat ≤-Cat Boolₚ.≤-Cat)
≤?-functor .obj m .obj = m ≤?_
≤?-functor .obj m .hom .func = ≤?-≤ {m} ≤-refl
≤?-functor .obj _ .hom .cong _ = tt
≤?-functor .obj _ .mor-∘ _ _ = tt
≤?-functor .obj _ .mor-id = tt
≤?-functor .hom .func m≤n .at _ = ≤?-≤ m≤n ≤-refl
≤?-functor .hom .func m≤n .isNatural _ = tt
≤?-functor .hom .cong _ _ = tt
≤?-functor .mor-∘ _ _ _ = tt
≤?-functor .mor-id _ = tt

≤?-functorʳ : ℕ → Functor ≤-Cat Boolₚ.≤-Cat
≤?-functorʳ = ≤?-functor <$>_

≤?-functorˡ : ℕ → Functor (Op ≤-Cat) Boolₚ.≤-Cat
≤?-functorˡ = Λ ≤?-functor -_

<?-functor : Functor (Op ≤-Cat) (FunCat ≤-Cat Boolₚ.≤-Cat)
<?-functor .obj m .obj = m <?_
<?-functor .obj m .hom .func = <?-≤ {m} ≤-refl
<?-functor .obj _ .hom .cong _ = tt
<?-functor .obj _ .mor-∘ _ _ = tt
<?-functor .obj _ .mor-id = tt
<?-functor .hom .func m≤n .at n = <?-≤ {m = n} m≤n ≤-refl
<?-functor .hom .func m≤n .isNatural _ = tt
<?-functor .hom .cong _ _ = tt
<?-functor .mor-∘ _ _ _ = tt
<?-functor .mor-id _ = tt

<?-functorʳ : ℕ → Functor ≤-Cat Boolₚ.≤-Cat
<?-functorʳ = <?-functor <$>_

<?-functorˡ : ℕ → Functor (Op ≤-Cat) Boolₚ.≤-Cat
<?-functorˡ = Λ <?-functor -_
