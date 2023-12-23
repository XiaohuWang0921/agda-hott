{-# OPTIONS --without-K --safe #-}

module Data.Fin.Subset.Properties where

open import Data.Fin.Base as Fin
open import Data.Fin.Subset.Base
open import Data.Fin.Properties hiding (suc-injective)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; 0≤n; s≤s; _∸_; _+_)
open import Universe.Set
open import Relation.Equality.Base hiding (cong)
open import Data.Unit.Core
open import Data.Bool.Base hiding (_≟_)
open import Data.Vec.Base
open import Data.Bool.Properties as Boolₚ
open import Data.Nat.Properties as ℕₚ hiding (≤?-Reflects-≤; ≤?-≤; ≤-refl; ≤-antisym; ≤-trans; ≤-Cat)
open import Category.Base
open import Level
open import Category.Functor hiding (_∘_)
open import Data.Vec.Properties
open import Universe.Setoid using (func; cong)
open import Category.FunCat
open import Category.Natural using (at; isNatural)
open import Data.Empty.Base
open import Data.Product.Base
import Relation.Reasoning
open import Data.Sum.Base as Sum

private
  variable
    m n : ℕ

⊆?-Reflects-⊆ : (s t : Subset n) → (s ⊆? t) Reflects (s ⊆ t)
⊆?-Reflects-⊆ [] [] = []
⊆?-Reflects-⊆ (b ∷ s) (c ∷ t) with b ≤? c | ≤?-Reflects-≤ b c
... | false | b≰c = λ where
  (b≤c ∷ _) → b≰c b≤c
... | true | b≤c with s ⊆? t | ⊆?-Reflects-⊆ s t
... | false | s⊈t = λ where
  (_ ∷ s⊆t) → s⊈t s⊆t
... | true | s⊆t = b≤c ∷ s⊆t

⊆?-⊆ : {s t u v : Subset n} → s ⊆ t → u ⊆ v → (t ⊆? u) ≤ (s ⊆? v)
⊆?-⊆ [] [] = b≤b
⊆?-⊆ (a≤b ∷ s⊆t) (c≤d ∷ u⊆v) = ∧-≤ (≤?-≤ a≤b c≤d) (⊆?-⊆ s⊆t u⊆v)

⊆-refl : {s : Subset n} → s ⊆ s
⊆-refl {zero} {[]} = []
⊆-refl {suc _} {_ ∷ _} = ≤-refl ∷ ⊆-refl

⊆-antisym : {s t : Subset n} → s ⊆ t → t ⊆ s → s ≡ t
⊆-antisym [] [] = refl
⊆-antisym (b≤b ∷ s⊆t) (_ ∷ t⊆s) = _ ∷_ =$= ⊆-antisym s⊆t t⊆s

⊆-trans : {r s t : Subset n} → r ⊆ s → s ⊆ t → r ⊆ t
⊆-trans [] [] = []
⊆-trans (a≤b ∷ r⊆s) (b≤c ∷ s⊆t) = (≤-trans a≤b b≤c) ∷ ⊆-trans r⊆s s⊆t

≡⇒⊆ : {s t : Subset n} → s ≡ t → s ⊆ t
≡⇒⊆ s≡t rewrite s≡t = ⊆-refl

s⊆full : {s : Subset n} → s ⊆ full n
s⊆full {_} {[]} = []
s⊆full {_} {_ ∷ s} = b≤true ∷ s⊆full

empty⊆s : {s : Subset n} → empty n ⊆ s
empty⊆s {_} {[]} = []
empty⊆s {_} {_ ∷ s} = false≤b ∷ empty⊆s

∣∣-⊆ : {s t : Subset n} → s ⊆ t → ∣ s ∣ ℕ.≤ ∣ t ∣
∣∣-⊆ [] = 0≤n
∣∣-⊆ (b≤b {false} ∷ s⊆t) = ∣∣-⊆ s⊆t
∣∣-⊆ (b≤b {true} ∷ s⊆t) = s≤s (∣∣-⊆ s⊆t)
∣∣-⊆ (f≤t ∷ s⊆t) = <⇒≤ (s≤s (∣∣-⊆ s⊆t))

∣s∣≤n : (s : Subset n) → ∣ s ∣ ℕ.≤ n
∣s∣≤n [] = 0≤n
∣s∣≤n (false ∷ s) = ℕₚ.≤-trans (∣s∣≤n s) (<⇒≤ <-suc)
∣s∣≤n (true ∷ s) = s≤s (∣s∣≤n s)

∣∣∘full : ∀ n → ∣ full n ∣ ≡ n
∣∣∘full zero = refl
∣∣∘full (suc n) = suc =$= ∣∣∘full n

∣∣∘empty : ∀ n → ∣ empty n ∣ ≡ 0
∣∣∘empty zero = refl
∣∣∘empty (suc n) = ∣∣∘empty n

∣∣∘∁ : ∣_∣ ∘ ∁ {n} ≗ (n ∸_) ∘ ∣_∣
∣∣∘∁ [] = refl
∣∣∘∁ (false ∷ s) = trans (suc =$= ∣∣∘∁ s) (∸-suc (∣s∣≤n s))
∣∣∘∁ (true ∷ s) = ∣∣∘∁ s

∣∣∘single : ∣_∣ ∘ single {n} ≗ const 1
∣∣∘single {suc n} zero = suc =$= ∣∣∘empty n
∣∣∘single {suc _} (suc i) = ∣∣∘single i

∣∣∘antisingle : ∣_∣ ∘ antisingle {n} ≗ const (n ∸ 1)
∣∣∘antisingle {suc n} zero = ∣∣∘full n
∣∣∘antisingle {suc (suc _)} (suc i) = suc =$= (∣∣∘antisingle i)

∣∣∘subSub : (s : Subset n) → ∣_∣ ∘ subSub s ≗ ∣_∣
∣∣∘subSub [] [] = refl
∣∣∘subSub (false ∷ s) t = ∣∣∘subSub s t
∣∣∘subSub (true ∷ s) (false ∷ t) = ∣∣∘subSub s t
∣∣∘subSub (true ∷ s) (true ∷ t) = suc =$= ∣∣∘subSub s t

∣∣∘except : (s : Subset n) → ∣_∣ ∘ except s ≗ const (∣ s ∣ ∸ 1)
∣∣∘except s i = trans (∣∣∘subSub s (antisingle i)) (∣∣∘antisingle i)

∣∣≡n : ∀ s → ∣ s ∣ ≡ n → s ≡ full n
∣∣≡n [] _ = refl
∣∣≡n (false ∷ s) ∣s∣≡sn = ⊥-elim (<-irrefl (resp (ℕ._≤ _) ∣s∣≡sn (∣s∣≤n s)))
∣∣≡n (true ∷ s) s∣s∣≡sn = true ∷_ =$= ∣∣≡n s (suc-injective s∣s∣≡sn)

∣∣≡0 : ∀ s → ∣ s ∣ ≡ 0 → s ≡ empty n
∣∣≡0 [] _ = refl
∣∣≡0 (false ∷ s) ∣s∣≡0 = false ∷_ =$= ∣∣≡0 s ∣s∣≡0

∣∣≡1 : ∀ s → ∣ s ∣ ≡ 1 → Σ (Fin n) λ i → s ≡ single i
∣∣≡1 (false ∷ s) ∣s∣≡1 = let j , s≡single = ∣∣≡1 s ∣s∣≡1 in suc j , (false ∷_ =$= s≡single)
∣∣≡1 (true ∷ s) s∣s∣≡1 = zero , (true ∷_ =$= (∣∣≡0 s (suc-injective s∣s∣≡1)))

∪-⊆ : {s t u v : Subset n} → s ⊆ t → u ⊆ v → s ∪ u ⊆ t ∪ v
∪-⊆ [] [] = []
∪-⊆ (a≤b ∷ s⊆t) (b≤c ∷ t⊆u) = (∨-≤ a≤b b≤c) ∷ (∪-⊆ s⊆t t⊆u)

∩-⊆ : {s t u v : Subset n} → s ⊆ t → u ⊆ v → s ∩ u ⊆ t ∩ v
∩-⊆ [] [] = []
∩-⊆ (a≤b ∷ s⊆t) (b≤c ∷ t⊆u) = (∧-≤ a≤b b≤c) ∷ (∩-⊆ s⊆t t⊆u)

∪-empty : ∀ {s} → s ∪ empty n ≡ s
∪-empty {_} {[]} = refl
∪-empty {_} {_ ∷ s} = cong₂ _∷_ ∨-false ∪-empty

empty-∪ : ∀ {s} → empty n ∪ s ≡ s
empty-∪ {_} {[]} = refl
empty-∪ {_} {b ∷ s} = b ∷_ =$= empty-∪

empty-∩ : ∀ {s} → empty n ∩ s ≡ empty n
empty-∩ {_} {[]} = refl
empty-∩ {_} {_ ∷ s} = false ∷_ =$= empty-∩

full-∩ : ∀ {s} → full n ∩ s ≡ s
full-∩ {_} {[]} = refl
full-∩ {_} {b ∷ s} = b ∷_ =$= full-∩

-- single-cast : ∀ .(m≡n : m ≡ n) i → single (cast m≡n i) ≗ vecCast m≡n (single i)
-- single-cast {suc _} {suc _} _ zero zero = refl
-- single-cast {suc _} {suc _} _ zero (suc _) = refl
-- single-cast {suc _} {suc _} _ (suc _) zero = refl
-- single-cast {suc _} {suc _} sm≡sn (suc i) (suc j) = single-cast (suc-injective sm≡sn) i j

-- antisingle-cast : ∀ .(m≡n : m ≡ n) i → antisingle (cast m≡n i) ≗ vecCast m≡n (antisingle i)
-- antisingle-cast m≡n i j = not =$= single-cast m≡n i j

image-cong : ∀ {f g : Fin m → Fin n} s → f ≗ g → image f s ≡ image g s
image-cong [] _ = refl
image-cong (b ∷ s) f≗g = cong₂ _∪_ (zipWith _ _ =$= (single =$= (f≗g zero))) (image-cong s λ i → f≗g (suc i))

image-⊆ : ∀ (f : Fin m → Fin n) {s t} → s ⊆ t → image f s ⊆ image f t
image-⊆ _ [] = ⊆-refl
image-⊆ f (b≤c ∷ s⊆t) = ∪-⊆ (∩-⊆ (repeatPointwise _ b≤c) ⊆-refl) (image-⊆ (f ∘ suc) s⊆t)

image-empty : (f : Fin m → Fin n) → image f (empty m) ≡ empty n
image-empty {zero} _ = refl
image-empty {suc m} f = 
  image f (empty (suc m)) ≡⟨⟩
  image f (repeat (suc m) false) ≡⟨⟩
  image f (false ∷ repeat m false) ≡⟨⟩
  repeat _ false ∩ single (f zero) ∪ image (f ∘ suc) (repeat m false) ≡⟨⟩
  empty _ ∩ single (f zero) ∪ image (f ∘ suc) (empty m) ≡⟨ _∪ image (f ∘ suc) (empty m) =$= empty-∩ ⟩
  empty _ ∪ image (f ∘ suc) (empty m) ≡⟨ empty-∪ ⟩
  image (f ∘ suc) (empty m) ≡⟨ image-empty (f ∘ suc) ⟩
  empty _ ∎
  where open Relation.Reasoning _≡_
        open Equiv refl trig

image-single : ∀ (f : Fin m → Fin n) i → image f (single i) ≡ single (f i)
image-single f zero = 
  image f (single zero) ≡⟨⟩
  image f (true ∷ empty _) ≡⟨⟩
  repeat _ true ∩ single (f zero) ∪ image (f ∘ suc) (empty _) ≡⟨⟩
  full _ ∩ single (f zero) ∪ image (f ∘ suc) (empty _) ≡⟨ _∪ image (f ∘ suc) (empty _) =$= full-∩ ⟩
  single (f zero) ∪ image (f ∘ suc) (empty _) ≡⟨ single (f zero) ∪_ =$= (image-empty (f ∘ suc)) ⟩
  single (f zero) ∪ empty _ ≡⟨ ∪-empty ⟩
  single (f zero) ∎
  where open Relation.Reasoning _≡_
        open Equiv refl trig
image-single f (suc i) = 
  image f (single (suc i)) ≡⟨⟩
  (image f (false ∷ single i) ≡⟨⟩
  repeat _ false ∩ single (f zero) ∪ image (f ∘ suc) (single i) ≡⟨⟩
  empty _ ∩ single (f zero) ∪ image (f ∘ suc) (single i) ≡⟨ _∪ image (f ∘ suc) (single i) =$= empty-∩ ⟩
  empty _ ∪ image (f ∘ suc) (single i) ≡⟨ empty-∪ ⟩
  image (f ∘ suc) (single i) ≡⟨ image-single (f ∘ suc) i ⟩
  single (f (suc i)) ∎)
  where open Relation.Reasoning _≡_
        open Equiv refl trig

-- image-preimage : ∀ (f : Fin m → Fin n) s → image f (preimage f s) ⊆ s
-- image-preimage {zero} _ _ = empty⊆s
-- image-preimage {suc _} f s i = {!!}

-- preimage-image : ∀ (f : Fin m → Fin n) s → s ⊆ preimage f (image f s)
-- preimage-image = {!!}

-- embed-irrel : {s t : Subset n} (a b : s ⊆ t) → embed a ≗ embed b
-- embed-irrel {suc _} {s} {t} a b with s zero | t zero | a zero | b zero
-- ... | false | false | _ | _ = embed-irrel (tail-⊆ a) (tail-⊆ b)
-- ... | false | true | _ | _ = λ i → suc =$= embed-irrel (tail-⊆ a) (tail-⊆ b) i
-- ... | true | true | _ | _ = λ where
--   zero → refl
--   (suc i) → suc =$= embed-irrel (tail-⊆ a) (tail-⊆ b) i

-- embed-refl : {s : Subset n} (s⊆s : s ⊆ s) → embed s⊆s ≗ id
-- embed-refl {suc _} {s} s⊆s with s zero | s⊆s zero
-- ... | false | _ = embed-refl (tail-⊆ s⊆s)
-- ... | true | _ = λ where
--   zero → refl
--   (suc i) → suc =$= embed-refl (tail-⊆ s⊆s) i

-- embed-trans : {s t u : Subset n} (s⊆t : s ⊆ t) (t⊆u : t ⊆ u) (s⊆u : s ⊆ u) → embed s⊆u ≗ embed t⊆u ∘ embed s⊆t
-- embed-trans {suc _} {s} {t} {u} s⊆t t⊆u s⊆u with s zero | t zero | u zero | s⊆t zero | t⊆u zero | s⊆u zero
-- ... | false | false | false | _ | _ | _ = embed-trans (tail-⊆ s⊆t) (tail-⊆ t⊆u) (tail-⊆ s⊆u)
-- ... | false | false | true | _ | _ | _ = λ i → suc =$= embed-trans (tail-⊆ s⊆t) (tail-⊆ t⊆u) (tail-⊆ s⊆u) i
-- ... | false | true | true | _ | _ | _ = λ i → suc =$= embed-trans (tail-⊆ s⊆t) (tail-⊆ t⊆u) (tail-⊆ s⊆u) i
-- ... | true | true | true | _ | _ | _ = λ where
--   zero → refl
--   (suc i) → suc =$= embed-trans (tail-⊆ s⊆t) (tail-⊆ t⊆u) (tail-⊆ s⊆u) i

subSub⊆s : ∀ s (t : Subset ∣ s ∣) → subSub {n} s t ⊆ s
subSub⊆s [] [] = []
subSub⊆s (false ∷ s) t = b≤b ∷ subSub⊆s s t
subSub⊆s (true ∷ s) (b ∷ t) = b≤true ∷ subSub⊆s s t

-- subSub-⊆ : ∀ s {u v} → u ⊆ v → subSub {n} s u ⊆ subSub s v
-- subSub-⊆ {suc _} s {u} {v} u⊆v with head s
-- ... | false = λ where
--   zero → b≤b
--   (suc i) → subSub-⊆ (tail s) u⊆v i
-- ... | true = λ where
--   zero → u⊆v zero
--   (suc i) → subSub-⊆ (tail s) (tail-⊆ u⊆v) i

subSub-full : ∀ s → subSub {n} s (full ∣ s ∣) ≡ s
subSub-full [] = refl
subSub-full (false ∷ s) = false ∷_ =$= (subSub-full s)
subSub-full (true ∷ s) = true ∷_ =$= (subSub-full s)
-- subSub-full {suc _} s zero with head s
-- ... | false = refl
-- ... | true = refl
-- subSub-full {suc _} s (suc i) with head s
-- ... | false = subSub-full (tail s) i 
-- ... | true = subSub-full (tail s) i

-- subSub∘subSub : ∀ (s : Subset n) t u → subSub (subSub s t) u ≗ subSub s (subSub t (vecCast (∣∣∘subSub s t) u))
-- subSub∘subSub {suc _} s t u zero with head s
-- ... | false = refl
-- ... | true with head t
-- ... | false = refl
-- ... | true = refl
-- subSub∘subSub {suc _} s t u (suc i) with head s
-- ... | false = subSub∘subSub (tail s) t u i
-- ... | true with head t
-- ... | false = subSub∘subSub (tail s) (tail t) u i
-- ... | true = subSub∘subSub (tail s) (tail t) (tail u) i

-- embed-subSub : ∀ (s : Subset n) {u v} u⊆v → embed (subSub-⊆ s u⊆v) ≗ tsac (∣∣∘subSub s v) ∘ embed u⊆v ∘ cast (∣∣∘subSub s u)
-- embed-subSub {suc _} s {u} {v} u⊆v with head s
-- ... | false = embed-subSub (tail s) u⊆v
-- ... | true with head u | head v | u⊆v zero
-- ... | false | false | _ = embed-subSub (tail s) (tail-⊆ u⊆v)
-- ... | false | true | _ = λ i → suc =$= embed-subSub (tail s) (tail-⊆ u⊆v) i
-- ... | true | true | _ = λ where
--   zero → refl
--   (suc i) → suc =$= embed-subSub (tail s) (tail-⊆ u⊆v) i

⊆-except : {s t : Subset n} → s ⊆ t → s ≡ t ⊎ Σ _ λ i → s ⊆ except t i
⊆-except [] = inj₁ refl
⊆-except (b≤b {false} ∷ s⊆t) with ⊆-except s⊆t
... | inj₁ s≡t = inj₁ (false ∷_ =$= s≡t)
... | inj₂ (i , s⊆except) = inj₂ (i , (b≤b ∷ s⊆except))
⊆-except (b≤b {true} ∷ s⊆t) with ⊆-except s⊆t
... | inj₁ s≡t = inj₁ (true ∷_ =$= s≡t)
... | inj₂ (i , s⊆except) = inj₂ (suc i , b≤b ∷ s⊆except)
⊆-except (f≤t ∷ s⊆t) = inj₂ (zero , (b≤b ∷ pser (_ ⊆_) (subSub-full _) s⊆t))

except⊆s : ∀ (s : Subset n) i → except s i ⊆ s
except⊆s s i = subSub⊆s s (antisingle i)

embed∘except : ∀ (s : Subset n) i → embed (except⊆s s i) ≗ punchIn' i ∘ Fin.cast (∣∣∘except s i)
embed∘except (false ∷ s) = embed∘except s
embed∘except (true ∷ []) zero ()
embed∘except (true ∷ false ∷ s) zero j = embed∘except (true ∷ s) zero j
embed∘except (true ∷ true ∷ s) zero zero = refl
embed∘except (true ∷ true ∷ []) zero (suc ())
embed∘except (true ∷ true ∷ false ∷ s) zero (suc j) = embed∘except (true ∷ true ∷ s) zero (suc j)
embed∘except (true ∷ true ∷ true ∷ s) zero (suc zero) = refl
embed∘except (true ∷ true ∷ true ∷ s) zero (suc j) = suc =$= (embed∘except (true ∷ true ∷ s) zero j)
embed∘except (true ∷ false ∷ s) (suc i) j = embed∘except (true ∷ s) (suc i) j
embed∘except (true ∷ true ∷ s) (suc i) zero = refl
embed∘except (true ∷ true ∷ s) (suc i) (suc j) = suc =$= (embed∘except (true ∷ s) i j)

⊆-Cat : ℕ → Category 0ℓ 0ℓ 0ℓ
⊆-Cat n = Preorder (_⊆_ {n}) ⊆-refl ⊆-trans

∣∣-functor : Functor (⊆-Cat n) ℕₚ.≤-Cat
∣∣-functor .obj = ∣_∣
∣∣-functor .hom .func = ∣∣-⊆
∣∣-functor .hom .cong _ = tt
∣∣-functor .mor-∘ _ _ = tt
∣∣-functor .mor-id = tt

⊆?-functor : Functor (Op (⊆-Cat n)) (FunCat (⊆-Cat n) Boolₚ.≤-Cat)
⊆?-functor .obj s .obj = s ⊆?_
⊆?-functor .obj s .hom .func = ⊆?-⊆ (⊆-refl {s = s})
⊆?-functor .obj s .hom .cong _ = tt
⊆?-functor .obj s .mor-∘ _ _ = tt
⊆?-functor .obj s .mor-id = tt
⊆?-functor .hom .func s⊆t .at _ = ⊆?-⊆ s⊆t ⊆-refl
⊆?-functor .hom .func _ .isNatural _ = tt
⊆?-functor .hom .cong _ _ = tt
⊆?-functor .mor-∘ _ _ _ = tt
⊆?-functor .mor-id _ = tt

⊆?-functorʳ : Subset n → Functor (⊆-Cat n) Boolₚ.≤-Cat
⊆?-functorʳ = ⊆?-functor <$>_

⊆?-functorˡ : Subset n → Functor (Op (⊆-Cat n)) Boolₚ.≤-Cat
⊆?-functorˡ = Λ ⊆?-functor -_
-- ∪-functorˡ : Subset n → Functor (⊆-Cat n) (⊆-Cat n)
-- ∪-functorˡ s = record
--   { obj = _∪ s
--   ; hom = record
--     { func = flip ∪-⊆ ⊆-refl
--     ; cong = λ _ → tt
--     }
--   ; mor-∘ = λ _ _ → tt
--   ; mor-id = tt
--   }

-- ∪-functorʳ : Subset n → Functor (⊆-Cat n) (⊆-Cat n)
-- ∪-functorʳ s = record
--   { obj = s ∪_
--   ; hom = record
--     { func = ∪-⊆ ⊆-refl
--     ; cong = λ _ → tt
--     }
--   ; mor-∘ = λ _ _ → tt
--   ; mor-id = tt
--   }

image-functor : (Fin m → Fin n) → Functor (⊆-Cat m) (⊆-Cat n)
image-functor f .obj = image f
image-functor f .hom .func = image-⊆ f
image-functor f .hom .cong _ = tt
image-functor f .mor-∘ _ _ = tt
image-functor f .mor-id = tt
