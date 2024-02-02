{-# OPTIONS --without-K --safe #-}

module Data.Bool.Properties where

open import Data.Bool.Base
open import Relation.Equality.Base hiding (cong)
open import Universe.Set
open import Data.Empty.Base
open import Data.Unit.Core
open import Category.Base
open import Category.Functor hiding (_∘_)
open import Universe.Set.Categorical
open import Level
open import Universe.Setoid using (func; cong)
open import Category.FunCat
open import Category.Natural using (_⇉_; at; isNatural)

private
  variable
    a b c d : Bool

false≢true : false ≢ true
false≢true ()

T-irrel : {x y : T b} → x ≡ y
T-irrel {true} {tt} {tt} = refl

id-Reflects-T : ∀ b → b Reflects T b
id-Reflects-T false = id
id-Reflects-T true = tt

≤?-Reflects-≤ : ∀ b c → (b ≤? c) Reflects (b ≤ c)
≤?-Reflects-≤ false false = b≤b
≤?-Reflects-≤ false true = f≤t
≤?-Reflects-≤ true true = b≤b

≟-Reflects-≡ : ∀ b c → (b ≟ c) Reflects (b ≡ c)
≟-Reflects-≡ false false = refl
≟-Reflects-≡ false true = false≢true
≟-Reflects-≡ true false = false≢true ∘ sym
≟-Reflects-≡ true true = refl

Reflects-true : ∀ {ℓ} {P : Set ℓ} b → b Reflects P → P → b ≡ true
Reflects-true false ¬p p = ⊥-elim (¬p p)
Reflects-true true _ _ = refl

Reflects-false : ∀ {ℓ} {P : Set ℓ} b → b Reflects P → (P → ⊥) → b ≡ false
Reflects-false false _ _ = refl
Reflects-false true p ¬p = ⊥-elim (¬p p)

T-F : T b → F b → ⊥
T-F {false} ()
T-F {true} _ ()

if-T : ∀ {p} {P : Set p} {then : T b → P} {else : F b → P} (t : T b) → if b then then else else ≡ then t
if-T {true} tt = refl

if-F : ∀ {p} {P : Set p} {then : T b → P} {else : F b → P} (f : F b) → if b then then else else ≡ else f
if-F {false} tt = refl

b≤true : b ≤ true
b≤true {false} = f≤t
b≤true {true} = b≤b

false≤b : false ≤ b
false≤b {false} = b≤b
false≤b {true} = f≤t

Reflects-≤ : ∀ {p q} {P : Set p} {Q : Set q} → b Reflects P → c Reflects Q → b ≤ c → P → Q
Reflects-≤ ¬p _ (b≤b {false}) p = ⊥-elim (¬p p)
Reflects-≤ _ q (b≤b {true}) _ = q
Reflects-≤ _ q f≤t _ = q

Reflects-→ : ∀ {p q} {P : Set p} {Q : Set q} → b Reflects P → c Reflects Q → (P → Q) → b ≤ c
Reflects-→ {false} {false} _ _ _ = b≤b
Reflects-→ {false} {true} _ _ _ = f≤t
Reflects-→ {true} {false} p ¬q f = ⊥-elim (¬q (f p))
Reflects-→ {true} {true} _ _ _ = b≤b

T-Reflects : ∀ {p} {P : Set p} → b Reflects P → T b → P
T-Reflects {b = true} p tt = p

not-≤ : a ≤ b → not b ≤ not a
not-≤ b≤b = b≤b
not-≤ f≤t = f≤t

T-≤ : a ≤ b → T a → T b
T-≤ {a} {b} = Reflects-≤ (id-Reflects-T a) (id-Reflects-T b)

≤?-≤ : a ≤ b → c ≤ d → (b ≤? c) ≤ (a ≤? d)
≤?-≤ {false} {false} _ = const b≤b
≤?-≤ {false} {true} _ = const b≤true
≤?-≤ {true} {true} _ = id

∧-≤ : a ≤ b → c ≤ d → a ∧ c ≤ b ∧ d
∧-≤ {false} {false} = const (const b≤b)
∧-≤ {false} {true} = const (const false≤b)
∧-≤ {true} {true} = const id

-- ∧-idem : b ∧ b ≡ b
-- ∧-idem {false} = refl
-- ∧-idem {true} = refl

a∧b≤a : a ∧ b ≤ a
a∧b≤a {false} = b≤b
a∧b≤a {true} = b≤true

a∧b≤b : a ∧ b ≤ b
a∧b≤b {false} = false≤b
a∧b≤b {true} = b≤b

∨-≤ : a ≤ b → c ≤ d → a ∨ c ≤ b ∨ d
∨-≤ {false} {false} = const id
∨-≤ {false} {true} = const (const b≤true)
∨-≤ {true} {true} = const (const b≤b)

∨-idem : b ∨ b ≡ b
∨-idem {false} = refl
∨-idem {true} = refl

b∨false : b ∨ false ≡ b
b∨false {false} = refl
b∨false {true} = refl

∨-true : b ∨ true ≡ true
∨-true {false} = refl
∨-true {true} = refl

a≤a∨b : a ≤ a ∨ b
a≤a∨b {false} = false≤b
a≤a∨b {true} = b≤b

b≤a∨b : ∀ {b} → b ≤ a ∨ b
b≤a∨b {false} = b≤b
b≤a∨b {true} = b≤true

eval : (a ≤? b) ≤ c ≤? d → a ≤ b → c ≤ d
eval = Reflects-≤ (≤?-Reflects-≤ _ _) (≤?-Reflects-≤ _ _)

≤-refl : b ≤ b
≤-refl = b≤b

≡⇒≤ : a ≡ b → a ≤ b
≡⇒≤ refl = ≤-refl

≤-antisym : a ≤ b → b ≤ a → a ≡ b
≤-antisym b≤b _ = refl

≤-trans : a ≤ b → b ≤ c → a ≤ c
≤-trans b≤b a≤c = a≤c
≤-trans f≤t b≤b = f≤t

≤-Cat : Category 0ℓ 0ℓ 0ℓ
≤-Cat = Preorder _≤_ ≤-refl ≤-trans

T-functor : Functor ≤-Cat (SetCat 0ℓ)
T-functor .obj = T
T-functor .hom .func = T-≤
T-functor .hom {true} {true} .cong _ _ = refl
T-functor .mor-∘ {true} {true} {true} _ _ _ = refl
T-functor .mor-id {true} tt = refl

not-functor : Functor ≤-Cat (Op ≤-Cat)
not-functor .obj = not
not-functor .hom .func = not-≤
not-functor .hom .cong _ = tt
not-functor .mor-∘ _ _ = tt
not-functor .mor-id = tt

≤?-functor : Functor (Op ≤-Cat) (FunCat ≤-Cat ≤-Cat)
≤?-functor .obj a .obj = a ≤?_
≤?-functor .obj a .hom .func = ≤?-≤ ≤-refl
≤?-functor .obj a .hom .cong _ = tt
≤?-functor .obj a .mor-∘ _ _ = tt
≤?-functor .obj a .mor-id = tt
≤?-functor .hom .func a≤b .at _ = ≤?-≤ a≤b ≤-refl
≤?-functor .hom .func _ .isNatural _ = tt
≤?-functor .hom .cong _ _ = tt
≤?-functor .mor-∘ _ _ _ = tt
≤?-functor .mor-id _ = tt

≤?-functorʳ : Bool → Functor ≤-Cat ≤-Cat
≤?-functorʳ = ≤?-functor <$>_

≤?-functorˡ : Bool → Functor (Op ≤-Cat) ≤-Cat
≤?-functorˡ = Λ ≤?-functor -_

∧-functor : Functor ≤-Cat (FunCat ≤-Cat ≤-Cat)
∧-functor .obj a .obj = a ∧_
∧-functor .obj a .hom .func = ∧-≤ ≤-refl
∧-functor .obj a .hom .cong _ = tt
∧-functor .obj a .mor-∘ _ _ = tt
∧-functor .obj a .mor-id = tt
∧-functor .hom .func a≤b .at _ = ∧-≤ a≤b ≤-refl
∧-functor .hom .func _ .isNatural _ = tt
∧-functor .hom .cong _ _ = tt
∧-functor .mor-∘ _ _ _ = tt
∧-functor .mor-id _ = tt

∧-functorʳ : Bool → Functor ≤-Cat ≤-Cat
∧-functorʳ = ∧-functor <$>_

∧-functorˡ : Bool → Functor ≤-Cat ≤-Cat
∧-functorˡ = Λ ∧-functor -_

∧-naturalʳ : ∀ b → ∧-functorʳ b ⇉ Id
∧-naturalʳ b .at _ = a∧b≤b
∧-naturalʳ b .isNatural _ = tt

∧-naturalˡ : ∀ b → ∧-functorˡ b ⇉ Id
∧-naturalˡ b .at _ = a∧b≤a
∧-naturalˡ b .isNatural _ = tt

∨-functor : Functor ≤-Cat (FunCat ≤-Cat ≤-Cat)
∨-functor .obj a .obj = a ∨_
∨-functor .obj a .hom .func = ∨-≤ ≤-refl
∨-functor .obj a .hom .cong _ = tt
∨-functor .obj a .mor-∘ _ _ = tt
∨-functor .obj a .mor-id = tt
∨-functor .hom .func a≤b .at _ = ∨-≤ a≤b ≤-refl
∨-functor .hom .func _ .isNatural _ = tt
∨-functor .hom .cong _ _ = tt
∨-functor .mor-∘ _ _ _ = tt
∨-functor .mor-id _ = tt

∨-functorʳ : Bool → Functor ≤-Cat ≤-Cat
∨-functorʳ = ∨-functor <$>_

∨-functorˡ : Bool → Functor ≤-Cat ≤-Cat
∨-functorˡ = Λ ∨-functor -_

∨-naturalʳ : ∀ b → Id ⇉ ∨-functorʳ b
∨-naturalʳ b .at _ = b≤a∨b
∨-naturalʳ b .isNatural _ = tt

∨-naturalˡ : ∀ b → Id ⇉ ∨-functorˡ b
∨-naturalˡ b .at _ = a≤a∨b
∨-naturalˡ b .isNatural _ = tt
