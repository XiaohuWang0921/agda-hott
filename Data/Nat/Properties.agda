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

≤?-≤ˡ : ∀ {l m n} → l ≤ m → (m ≤? n) Bool.≤ (l ≤? n)
≤?-≤ˡ 0≤n = ≤-true
≤?-≤ˡ {n = zero} (s≤s _) = b≤b
≤?-≤ˡ {n = suc _} (s≤s l≤m) = ≤?-≤ˡ l≤m

≤?-≤ʳ : ∀ {l m n} → m ≤ n → (l ≤? m) Bool.≤ (l ≤? n)
≤?-≤ʳ {zero} _ = b≤b
≤?-≤ʳ {suc _} 0≤n = false-≤
≤?-≤ʳ {suc l} (s≤s m≤n) = ≤?-≤ʳ {l} m≤n

<?-≤ˡ : ∀ {l m n} → l ≤ m → (m <? n) Bool.≤ (l <? n)
<?-≤ˡ {n = zero} _ = b≤b
<?-≤ˡ {n = suc _} 0≤n = ≤-true
<?-≤ˡ {n = suc n} (s≤s l≤m) = <?-≤ˡ {n = n} l≤m

<?-≤ʳ : ∀ {l m n} → m ≤ n → (l <? m) Bool.≤ (l <? n)
<?-≤ʳ 0≤n = false-≤
<?-≤ʳ {zero} (s≤s m≤n) = b≤b
<?-≤ʳ {suc _} (s≤s m≤n) = <?-≤ʳ m≤n

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

≤?-functorˡ : ℕ → Functor ≤-Cat (Op Boolₚ.≤-Cat)
≤?-functorˡ n = record
  { obj = _≤? n
  ; hom = record
    { func = ≤?-≤ˡ
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ _ _ → tt
  ; mor-id = tt
  }

≤?-functorʳ : ℕ → Functor ≤-Cat Boolₚ.≤-Cat
≤?-functorʳ n = record
  { obj = n ≤?_
  ; hom = record
    { func = ≤?-≤ʳ {n}
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ _ _ → tt
  ; mor-id = tt
  }

<?-functorˡ : ℕ → Functor ≤-Cat (Op Boolₚ.≤-Cat)
<?-functorˡ n = record
  { obj = _<? n
  ; hom = record
    { func = <?-≤ˡ {n = n}
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ _ _ → tt
  ; mor-id = tt
  }

<?-functorʳ : ℕ → Functor ≤-Cat Boolₚ.≤-Cat
<?-functorʳ n = record
  { obj = n <?_
  ; hom = record
    { func = <?-≤ʳ
    ; cong = λ _ → tt
    }
  ; mor-∘ = λ _ _ → tt
  ; mor-id = tt
  }
