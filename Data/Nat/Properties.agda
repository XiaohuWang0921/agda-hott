{-# OPTIONS --without-K --safe #-}

module Data.Nat.Properties where

open import Data.Nat.Base
open import Data.Bool.Base as Bool hiding (_≟_; _≤?_; _≤_)
open import Relation.Equality.Base
open import Universe.Set
open import Data.Empty.Base
open import Data.Unit.Core
open import Data.Bool.Properties as Boolₚ using (≤-true; false-≤)
open import Category.Base
open import Category.Functor hiding (_∘_)
open import Level

zero≢suc : ∀ {n} → zero ≢ suc n
zero≢suc ()

suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

pred≤pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
pred≤pred (s≤s m≤n) = m≤n

≤?-≤ : ∀ {k l m n} → k ≤ l → m ≤ n → (l ≤? m) Bool.≤ (k ≤? n)
≤?-≤ 0≤n _ = ≤-true
≤?-≤ (s≤s k≤l) 0≤n = false-≤
≤?-≤ (s≤s k≤l) (s≤s m≤n) = ≤?-≤ k≤l m≤n

<?-≤ : ∀ {k l m n} → k ≤ l → m ≤ n → (l <? m) Bool.≤ (k <? n)
<?-≤ _ 0≤n = false-≤
<?-≤ 0≤n (s≤s m≤n) = ≤-true
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
suc-functor = record
  { obj = suc
  ; hom = record
    { func = s≤s
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ _ _ → tt
  ; mor-id = tt
  }

≤?-functorˡ : ℕ → Functor ≤-Cat (Op Boolₚ.≤-Cat)
≤?-functorˡ n = record
  { obj = _≤? n
  ; hom = record
    { func = flip ≤?-≤ ≤-refl
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ _ _ → tt
  ; mor-id = tt
  }

≤?-functorʳ : ℕ → Functor ≤-Cat Boolₚ.≤-Cat
≤?-functorʳ n = record
  { obj = n ≤?_
  ; hom = record
    { func = ≤?-≤ {n} ≤-refl
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ _ _ → tt
  ; mor-id = tt
  }

<?-functorˡ : ℕ → Functor ≤-Cat (Op Boolₚ.≤-Cat)
<?-functorˡ n = record
  { obj = _<? n
  ; hom = record
    { func = flip (<?-≤ {m = n}) ≤-refl
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ _ _ → tt
  ; mor-id = tt
  }

<?-functorʳ : ℕ → Functor ≤-Cat Boolₚ.≤-Cat
<?-functorʳ n = record
  { obj = n <?_
  ; hom = record
    { func = <?-≤ ≤-refl
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ _ _ → tt
  ; mor-id = tt
  }