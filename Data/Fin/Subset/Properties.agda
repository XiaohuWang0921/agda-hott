{-# OPTIONS --without-K --safe #-}

module Data.Fin.Subset.Properties where

open import Data.Fin.Base as Fin
open import Data.Fin.Subset.Base
open import Data.Fin.Properties
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; 0≤n; s≤s; _∸_; _+_; pred)
open import Universe.Set
open import Relation.Equality.Base hiding (cong)
open import Data.Unit.Core
open import Data.Bool.Base hiding (_≟_)
-- open import Data.Vec.Base
open import Data.Bool.Properties as Boolₚ
open import Data.Nat.Properties as ℕₚ hiding (≤?-Reflects-≤; ≤?-≤; ≤-refl; ≤-antisym; ≤-trans; ≤-Cat; suc-monic)
open import Category.Base
open import Level
open import Category.Functor hiding (_∘_)
open import Universe.Setoid using (func; cong)
open import Category.FunCat
open import Category.Natural using (at; isNatural)
open import Data.Empty.Base
open import Data.Product.Base
import Relation.Reasoning
open import Data.Sum.Base as Sum
open import Data.Fin.Properties

private
  variable
    k l m n o : ℕ
    s : CSet k l
    t : CSet k m
    u : CSet k n
    v : CSet k o

⊂-irrel : (x y : s ⊂ t) → x ≡ y
⊂-irrel [] [] = refl
⊂-irrel (b≤b {false} ∷ x) (b≤b ∷ y) = b≤b ∷_ =$= ⊂-irrel x y
⊂-irrel (b≤b {true} ∷ x) (b≤b ∷ y) = b≤b ∷_ =$= ⊂-irrel x y
⊂-irrel (f≤t ∷ x) (f≤t ∷ y) = f≤t ∷_ =$= ⊂-irrel x y

⊂?-Reflects-⊂ : (s : CSet k l) (t : CSet k m) → (s ⊂? t) Reflects (s ⊂ t)
⊂?-Reflects-⊂ [] [] = []
⊂?-Reflects-⊂ (b ∷ s) (c ∷ t) with b ≤? c | ≤?-Reflects-≤ b c
... | false | b≰c = λ where
  (b≤c ∷ _) → b≰c b≤c
... | true | b≤c with s ⊂? t | ⊂?-Reflects-⊂ s t
... | false | s⊈t = λ where
  (_ ∷ s⊂t) → s⊈t s⊂t
... | true | s⊂t = b≤c ∷ s⊂t

⊆?-Reflects-⊆ : (s t : Subset k) → (s ⊆? t) Reflects (s ⊆ t)
⊆?-Reflects-⊆ s t = ⊂?-Reflects-⊂ (s .proj₂) (t .proj₂)

⊂?-⊂ : s ⊂ t → u ⊂ v → (t ⊂? u) ≤ (s ⊂? v)
⊂?-⊂ [] [] = b≤b
⊂?-⊂ (a≤b ∷ s⊂t) (c≤d ∷ u⊂v) = ∧-≤ (≤?-≤ a≤b c≤d) (⊂?-⊂ s⊂t u⊂v)

⊆?-⊆ : {s t u v : Subset n} → s ⊆ t → u ⊆ v → (t ⊆? u) ≤ (s ⊆? v)
⊆?-⊆ = ⊂?-⊂

⊂-refl : s ⊂ s
⊂-refl {s = []} = []
⊂-refl {s = _ ∷ _} = ≤-refl ∷ ⊂-refl

⊆-refl : {s : Subset n} → s ⊆ s
⊆-refl = ⊂-refl

⊂-antisym : s ⊂ t → t ⊂ s → s ∼ t
⊂-antisym [] [] = refl , refl
⊂-antisym (b≤b {false} ∷ s⊂t) (b≤b ∷ t⊂s) with ⊂-antisym s⊂t t⊂s
... | refl , refl = refl , refl
⊂-antisym (b≤b {true} ∷ s⊂t) (b≤b ∷ t⊂s) with ⊂-antisym s⊂t t⊂s
... | refl , refl = refl , refl

⊆-antisym : {s t : Subset n} → s ⊆ t → t ⊆ s → s ≡ t
⊆-antisym s⊆t t⊆s with ⊂-antisym s⊆t t⊆s
... | refl , refl = refl

⊂-trans : s ⊂ t → t ⊂ u → s ⊂ u
⊂-trans [] [] = []
⊂-trans (a≤b ∷ r⊂s) (b≤c ∷ s⊂t) = (≤-trans a≤b b≤c) ∷ (⊂-trans r⊂s s⊂t)

⊆-trans : {s t u : Subset n} → s ⊆ t → t ⊆ u → s ⊆ u
⊆-trans = ⊂-trans

∼⇒⊂ : s ∼ t → s ⊂ t
∼⇒⊂ (refl , refl) = ⊂-refl

≡⇒⊆ : {s t : Subset n} → s ≡ t → s ⊆ t
≡⇒⊆ refl = ⊆-refl

⊂-∋? : s ⊂ t → ∀ i → (s ∋? i) ≤ (t ∋? i)
⊂-∋? (b≤c ∷ _) zero = b≤c
⊂-∋? (_ ∷ s⊂t) (suc i) = ⊂-∋? s⊂t i

tabulate-≤ : {f g : Fin k → Bool} → (∀ i → f i ≤ g i) → tabulate f ⊆ tabulate g
tabulate-≤ {zero} _ = []
tabulate-≤ {suc _} f≤g = f≤g zero ∷ tabulate-≤ λ i → f≤g (suc i)

s⊂full : {s : CSet k l} → s ⊂ full k
s⊂full {s = []} = []
s⊂full {s = _ ∷ _} = b≤true ∷ s⊂full

empty⊂s : {s : CSet k l} → empty k ⊂ s
empty⊂s {s = []} = []
empty⊂s {s = _ ∷ _} = false≤b ∷ empty⊂s

⊂⇒≤ : {s : CSet k l} {t : CSet k m} → s ⊂ t → l ℕ.≤ m
⊂⇒≤ [] = 0≤n
⊂⇒≤ (b≤b {false} ∷ s⊂t) = ⊂⇒≤ s⊂t
⊂⇒≤ (b≤b {true} ∷ s⊂t) = s≤s (⊂⇒≤ s⊂t)
⊂⇒≤ (f≤t ∷ s⊂t) = <⇒≤ (s≤s (⊂⇒≤ s⊂t))

l≤k : (s : CSet k l) → l ℕ.≤ k
l≤k [] = 0≤n
l≤k (false ∷ s) = <⇒≤ (s≤s (l≤k s))
l≤k (true ∷ s) = s≤s (l≤k s)

l≡k : (s : CSet k l) (l≡k : l ≡ k) → resp (CSet k) l≡k s ≡ full k
l≡k [] refl = refl
l≡k (false ∷ s) refl = ⊥-elim (<-irrefl (l≤k s))
l≡k (true ∷ s) refl = true ∷_ =$= (l≡k s refl)

l≡0 : (s : CSet k l) (l≡0 : l ≡ 0) → resp (CSet k) l≡0 s ≡ empty k
l≡0 [] refl = refl
l≡0 (false ∷ s) refl = false ∷_ =$= (l≡0 s refl)

l≡1 : (s : CSet k l) (l≡1 : l ≡ 1) → Σ (Fin k) ((resp (CSet k) l≡1 s ≡_) ∘ single)
l≡1 (false ∷ s) refl = mapp suc (false ∷_ =$=_) (l≡1 s refl)
l≡1 (true ∷ s) refl = zero , (true ∷_ =$= (l≡0 s refl))

k≡l+1 : (s : CSet (suc l) l) → Σ (Fin (suc l)) ((s ≡_) ∘ antisingle)
k≡l+1 (false ∷ s) = zero , (false ∷_ =$= (l≡k s refl))
k≡l+1 (true ∷ s) = mapp suc (true ∷_ =$=_) (k≡l+1 s)

∪-⊂ : s ⊂ t → u ⊂ v → s ∪ u ⊆ t ∪ v
∪-⊂ [] [] = []
∪-⊂ (a≤b ∷ s⊆t) (b≤c ∷ t⊆u) = (∨-≤ a≤b b≤c) ∷ (∪-⊂ s⊆t t⊆u)

∩-⊂ : s ⊂ t → u ⊂ v → s ∩ u ⊆ t ∩ v
∩-⊂ [] [] = []
∩-⊂ (a≤b ∷ s⊆t) (b≤c ∷ t⊆u) = (∧-≤ a≤b b≤c) ∷ (∩-⊂ s⊆t t⊆u)

∪-comm : s ∪ t ≡ t ∪ s
∪-comm {s = []} {t = []} = refl
∪-comm {s = b ∷ s} {t = c ∷ t} = cong₂ _∺_ (∨-comm {b} {c}) (∪-comm {s = s} {t = t})

⊂-∪ : s ⊂ t → s ∪ t ≡ (_ , t)
⊂-∪ [] = refl
⊂-∪ (b≤b {b} ∷ s⊂t) rewrite ∨-idem {b} = mapp (inc b) (b ∷_) =$= ⊂-∪ s⊂t
⊂-∪ (f≤t ∷ s⊂t) = mapp suc (true ∷_) =$= ⊂-∪ s⊂t

s⊆s∪t : (_ , s) ⊆ s ∪ t
s⊆s∪t {s = []} {t = []} = []
s⊆s∪t {s = b ∷ s} {t = c ∷ t} = a≤a∨b ∷ s⊆s∪t

t⊆s∪t : (_ , t) ⊆ s ∪ t
t⊆s∪t {t = t} {s = s} rewrite ∪-comm {s = s} {t = t} = s⊆s∪t

∪-idem : s ∪ s ≡ (_ , s)
∪-idem = ⊂-∪ ⊂-refl

empty∪s : empty n ∪ s ≡ (_ , s)
empty∪s = ⊂-∪ empty⊂s

s∪empty : s ∪ empty k ≡ (_ , s)
s∪empty = trans ∪-comm empty∪s

empty∩s : empty k ∩ s ≡ (0 , empty k)
empty∩s {s = []} = refl
empty∩s {s = _ ∷ _} = false ∺_ =$= empty∩s

full-∩ : full k ∩ s ≡ (_ , s)
full-∩ {s = []} = refl
full-∩ {s = b ∷ _} = b ∺_ =$= full-∩

embed-monic : (s⊂t : s ⊂ t) → IsMonic (embed s⊂t)
embed-monic (b≤b {false} ∷ s⊂t) = embed-monic s⊂t
embed-monic (b≤b {true} ∷ s⊂t) {zero} {zero} _ = refl
embed-monic (b≤b {true} ∷ s⊂t) {suc i} {suc j} s≡s = suc =$= embed-monic s⊂t (suc-monic s≡s)
embed-monic (f≤t ∷ s⊂t) s≡s = embed-monic s⊂t (suc-monic s≡s)

embed-full-∋ : ∀ i → s ∋ embed {s = s} s⊂full i
embed-full-∋ {s = false ∷ s} i = embed-full-∋ {s = s} i
embed-full-∋ {s = true ∷ s} zero = tt
embed-full-∋ {s = true ∷ s} (suc i) = embed-full-∋ {s = s} i

-- single-cast : ∀ .(m≡n : m ≡ n) i → single (cast m≡n i) ≗ vecCast m≡n (single i)
-- single-cast {suc _} {suc _} _ zero zero = refl
-- single-cast {suc _} {suc _} _ zero (suc _) = refl
-- single-cast {suc _} {suc _} _ (suc _) zero = refl
-- single-cast {suc _} {suc _} sm≡sn (suc i) (suc j) = single-cast (suc-injective sm≡sn) i j

-- antisingle-cast : ∀ .(m≡n : m ≡ n) i → antisingle (cast m≡n i) ≗ vecCast m≡n (antisingle i)
-- antisingle-cast m≡n i j = not =$= single-cast m≡n i j

empty-∌ : ∀ i → empty k ∌ i
empty-∌ zero = tt
empty-∌ (suc i) = empty-∌ i

single-∋ : (i : Fin k) → single i ∋ i
single-∋ zero = tt
single-∋ (suc i) = single-∋ i

∋-single : ∀ (s : CSet k l) i → s ∋ i → single i ⊂ s
∋-single (true ∷ s) zero _ = b≤b ∷ empty⊂s
∋-single (_ ∷ s) (suc i) s∋i = false≤b ∷ ∋-single s i s∋i

-- image-cong : ∀ {f g : Fin k → Fin l} (s : CSet k m) → f ≗ g → image f s ≡ image g s
-- image-cong [] _ = refl
-- image-cong (false ∷ s) f≗g = image-cong s λ i → f≗g (suc i)
-- image-cong (true ∷ s) f≗g rewrite (f≗g zero) rewrite image-cong s λ i → f≗g (suc i) = refl

image-⊂ : ∀ (f : Fin m → Fin n) → s ⊂ t → image f s ⊆ image f t
image-⊂ _ [] = ⊆-refl
image-⊂ f (b≤b {false} ∷ s⊂t) = image-⊂ (f ∘ suc) s⊂t
image-⊂ f (b≤b {true} ∷ s⊂t) = ∪-⊂ (⊂-refl {s = single (f zero)}) (image-⊂ (f ∘ suc) s⊂t)
image-⊂ {s = false ∷ s} f (f≤t ∷ s⊂t) rewrite sym (empty∪s {s = image (f ∘ suc) s .proj₂}) = ∪-⊂ (empty⊂s {s = single (f zero)}) (image-⊂ (f ∘ suc) s⊂t)

image-empty : (f : Fin k → Fin l) → image f (empty k) ≡ (0 , empty l)
image-empty {zero} _ = refl
image-empty {suc _} f = image-empty (f ∘ suc)

image-single : ∀ (f : Fin k → Fin l) i → image f (single i) ≡ (1 , single (f i))
image-single f zero rewrite image-empty (f ∘ suc) = s∪empty
image-single f (suc i) = image-single (f ∘ suc) i

preimage-⊂ : ∀ (f : Fin m → Fin n) → s ⊂ t → preimage f s ⊆ preimage f t
preimage-⊂ {zero} _ _ = []
preimage-⊂ {suc _} f s⊂t = ⊂-∋? s⊂t (f zero) ∷ preimage-⊂ (f ∘ suc) s⊂t

preimage-empty : (f : Fin k → Fin l) → preimage f (empty l) ≡ (0 , empty k)
preimage-empty {zero} _ = refl
preimage-empty {suc _} f rewrite F-false (empty-∌ (f zero)) = mapp id (false ∷_) =$= preimage-empty (f ∘ suc)

image-preimage : (f : Fin k → Fin l) (s : CSet l m) → image f (preimage f s .proj₂) ⊆ (m , s)
image-preimage {zero} _ _ = empty⊂s
image-preimage {suc _} f s with s ∋? f zero in eq
... | false = image-preimage (f ∘ suc) s
... | true = ⊂-trans (∪-⊂ (∋-single s (f zero) (pser T eq tt)) (image-preimage (f ∘ suc) s)) (≡⇒⊆ ∪-idem)

preimage-image : (f : Fin k → Fin l) (s : CSet k m) → (m , s) ⊆ preimage f (image f s .proj₂)
preimage-image f [] = []
preimage-image f (false ∷ s) = false≤b ∷ (preimage-image (f ∘ suc) s)
preimage-image f (true ∷ s) =
  let headf = f zero
      tailf = f ∘ suc
  in resp (_≤ (image f (true ∷ s) .proj₂ ∋? headf)) (T-true (single-∋ headf)) (⊂-∋? (s⊆s∪t {s = single headf}) headf) ∷
     ⊂-trans (preimage-image tailf s) (tabulate-≤ λ i → ⊂-∋? (t⊆s∪t {t = image tailf s .proj₂} {s = single headf}) (tailf i))

-- embed-irrel : {s t : Subset n} (a b : s ⊆ t) → embed a ≗ embed b
-- embed-irrel {suc _} {s} {t} a b with s zero | t zero | a zero | b zero
-- ... | false | false | _ | _ = embed-irrel (tail-⊆ a) (tail-⊆ b)
-- ... | false | true | _ | _ = λ i → suc =$= embed-irrel (tail-⊆ a) (tail-⊆ b) i
-- ... | true | true | _ | _ = λ where
--   zero → refl
--   (suc i) → suc =$= embed-irrel (tail-⊆ a) (tail-⊆ b) i

-- embed-refl : {s : Subset n} (s⊂s : s ⊆ s) → embed s⊂s ≗ id
-- embed-refl {suc _} {s} s⊂s with s zero | s⊂s zero
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

subsub-fullˡ : (s : CSet k l) → subsub (full k) s ≡ s
subsub-fullˡ [] = refl
subsub-fullˡ (b ∷ s) = b ∷_ =$= (subsub-fullˡ s)

subsub-fullʳ : (s : CSet k l) → subsub s (full l) ≡ s
subsub-fullʳ [] = refl
subsub-fullʳ (false ∷ s) = false ∷_ =$= subsub-fullʳ s
subsub-fullʳ (true ∷ s) = true ∷_ =$= subsub-fullʳ s

subsub⊂s : (s : CSet k l) (t : CSet l m) → subsub s t ⊂ s
subsub⊂s [] [] = []
subsub⊂s (false ∷ s) t = b≤b ∷ subsub⊂s s t
subsub⊂s (true ∷ s) (b ∷ t) = b≤true ∷ subsub⊂s s t

except⊂s : ∀ (s : CSet k l) i → except s i ⊂ s
except⊂s {l = suc _} s i = subsub⊂s s (antisingle i)

embed-refl : (s : CSet k l) → embed (⊂-refl {s = s}) ≗ id
embed-refl [] _ = refl
embed-refl (false ∷ s) = embed-refl s
embed-refl (true ∷ s) zero = refl
embed-refl (true ∷ s) (suc i) = suc =$= (embed-refl s i)

embed-trans : {s : CSet k l} {t : CSet k m} {u : CSet k n} (s⊂t : s ⊂ t) (t⊂u : t ⊂ u) → embed (⊂-trans s⊂t t⊂u) ≗ embed t⊂u ∘ embed s⊂t
embed-trans [] [] _ = refl
embed-trans (b≤b {false} ∷ s⊂t) (b≤b ∷ t⊂u) = embed-trans s⊂t t⊂u
embed-trans (b≤b {false} ∷ s⊂t) (f≤t ∷ t⊂u) i = suc =$= embed-trans s⊂t t⊂u i
embed-trans (b≤b {true} ∷ s⊂t) (b≤b ∷ t⊂u) zero = refl
embed-trans (b≤b {true} ∷ s⊂t) (b≤b ∷ t⊂u) (suc i) = suc =$= embed-trans s⊂t t⊂u i
embed-trans (f≤t ∷ s⊂t) (b≤b ∷ t⊂u) i = suc =$= embed-trans s⊂t t⊂u i

embed-subsub-full : (s : CSet k l) → embed (subsub⊂s s (full l)) ≗ id
embed-subsub-full [] _ = refl
embed-subsub-full (false ∷ s) = embed-subsub-full s
embed-subsub-full (true ∷ s) zero = refl
embed-subsub-full (true ∷ s) (suc i) = suc =$= (embed-subsub-full s i)

embed-except : ∀ (s : CSet k l) (l≡m : l ≡ m) i → embed (except⊂s (resp (CSet k) l≡m s) i) ≗ punchIn' i
embed-except {m = suc _} (false ∷ s) refl = embed-except s refl
embed-except (true ∷ s) refl zero zero = suc =$= embed-subsub-full s zero
embed-except (true ∷ s) refl zero (suc j) = suc =$= embed-subsub-full s (suc j)
embed-except (true ∷ s) refl (suc i) zero = refl
embed-except (true ∷ s) refl (suc i) (suc j) = suc =$= embed-except s refl i j

except-except : ∀ (s : CSet k l) (l≡m+1 : l ≡ suc m) i j → except (except (resp (CSet k) l≡m+1 s) i) j ≡ except (except (resp (CSet k) l≡m+1 s) (punchIn i j)) (pinch j i)
except-except (false ∷ s) refl i j = false ∷_ =$= (except-except s refl i j)
except-except {m = suc _} (true ∷ s) refl zero j = false ∷_ =$= trans (flip subsub _ =$= subsub-fullʳ s) (sym (subsub-fullʳ _))
except-except {m = suc _} (true ∷ s) refl (suc i) zero = false ∷_ =$= trans (subsub-fullʳ _) (sym (flip subsub _ =$= (subsub-fullʳ s)))
except-except {m = suc (suc _)} (true ∷ s) refl (suc i) (suc j) = true ∷_ =$= (except-except s refl i j)

⊂-except : {s : CSet k l} {t : CSet k m} → s ⊂ t → m ≡ n → Σ (l ≡ m) ((_≡ t) ∘ flip (resp (CSet k)) s) ⊎ Σ (Fin m) ((s ⊂_) ∘ except t)
⊂-except [] refl = inj₁ (refl , refl)
⊂-except (b≤b {false} ∷ s⊂t) refl with ⊂-except s⊂t refl
... | inj₁ (refl , refl) = inj₁ (refl , refl)
... | inj₂ (i , s⊂except) = inj₂ (i , b≤b ∷ s⊂except)
⊂-except {n = 1} (b≤b {true} ∷ s⊂t) refl with ⊂-except s⊂t refl
... | inj₁ (refl , refl) = inj₁ (refl , refl)
⊂-except {n = suc (suc _)} (b≤b {true} ∷ s⊂t) refl with ⊂-except s⊂t refl
... | inj₁ (refl , refl) = inj₁ (refl , refl)
... | inj₂ (i , s⊂except) = inj₂ (suc i , b≤b ∷ s⊂except)
⊂-except (f≤t ∷ s⊂t) refl = inj₂ (zero , b≤b ∷ pser (_ ⊂_) (subsub-fullʳ _) s⊂t)

⊆-Cat : ℕ → Category 0ℓ 0ℓ 0ℓ
⊆-Cat n = Preorder (_⊆_ {n}) ⊆-refl ⊆-trans

proj₁-functor : Functor (⊆-Cat n) ℕₚ.≤-Cat
proj₁-functor .obj = proj₁
proj₁-functor .hom .func = ⊂⇒≤
proj₁-functor .hom .cong _ = tt
proj₁-functor .mor-∘ _ _ = tt
proj₁-functor .mor-id = tt

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
--     { func = flip ∪-⊂ ⊆-refl
--     ; cong = λ _ → tt
--     }
--   ; mor-∘ = λ _ _ → tt
--   ; mor-id = tt
--   }

-- ∪-functorʳ : Subset n → Functor (⊆-Cat n) (⊆-Cat n)
-- ∪-functorʳ s = record
--   { obj = s ∪_
--   ; hom = record
--     { func = ∪-⊂ ⊆-refl
--     ; cong = λ _ → tt
--     }
--   ; mor-∘ = λ _ _ → tt
--   ; mor-id = tt
--   }

image-functor : (Fin m → Fin n) → Functor (⊆-Cat m) (⊆-Cat n)
image-functor f .obj s = image f (s .proj₂)
image-functor f .hom .func = image-⊂ f
image-functor f .hom .cong _ = tt
image-functor f .mor-∘ _ _ = tt
image-functor f .mor-id = tt

preimage-functor : (Fin m → Fin n) → Functor (⊆-Cat n) (⊆-Cat m)
preimage-functor f .obj s = preimage f (s .proj₂)
preimage-functor f .hom .func = preimage-⊂ f
preimage-functor f .hom .cong _ = tt
preimage-functor f .mor-∘ _ _ = tt
preimage-functor f .mor-id = tt
