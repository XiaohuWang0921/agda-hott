{-# OPTIONS --without-K --safe #-}

module HoTT.Setoid.Morphism where

open import Level
open import Function.Base as Fun hiding (id; const; _∘_; _ˢ_; flip)
open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.Bundles
open import Relation.Binary.Structures

-- Reimplementing morphisms between
-- setoids, since both implementations
-- in the stdlib are somewhat
-- inconsistent and are overly
-- complicated for my purpose.

private
  variable
    a b c d r s t u : Level
    From : Setoid a r
    To   : Setoid b s
    More : Setoid c t
    End  : Setoid d u

infixr 0 _⟶_
record _⟶_ (From : Setoid a r) (To : Setoid b s) : Set (a ⊔ b ⊔ r ⊔ s) where
  open Setoid From renaming (Carrier to A; _≈_ to _≈₁_)
  open Setoid To renaming (Carrier to B; _≈_ to _≈₂_)

  infixl 5 _⟨$⟩_
  field
    _⟨$⟩_ : A → B
    cong : _≈₁_ =[ _⟨$⟩_ ]⇒ _≈₂_

open _⟶_ public

infix 4 _⊖_
_⊖_ : Rel (From ⟶ To) _
_⊖_ {To = To} F G = Reflexive (F ⟨$⟩_ -⟨ _≈_ ⟩- G ⟨$⟩_)
  where open Setoid To

⊖-isEquivalence : IsEquivalence (_⊖_ {From = From} {To = To})
⊖-isEquivalence {To = To} = record
  { refl = refl
  ; sym = λ F⊖G → sym F⊖G
  ; trans = λ F⊖G G⊖H → trans F⊖G G⊖H
  }
  where open Setoid To

infixr 0 _⇨_
_⇨_ : Setoid a r → Setoid b s → Setoid (a ⊔ b ⊔ r ⊔ s) (a ⊔ s)
_⇨_ From To = record
  { Carrier = From ⟶ To
  ; _≈_ = _⊖_
  ; isEquivalence = ⊖-isEquivalence
  }

id : From ⟶ From
id = record
  { _⟨$⟩_ = Fun.id
  ; cong = Fun.id
  }

infixr 9 _∘_
_∘_ : (To ⟶ More) → (From ⟶ To) → From ⟶ More
F ∘ G = record
  { _⟨$⟩_ = (F ⟨$⟩_) ∘′ (G ⟨$⟩_)
  ; cong = F .cong ∘′ G .cong
  }

∘-assoc : (F : More ⟶ End) (G : To ⟶ More) (H : From ⟶ To) → (F ∘ G) ∘ H ⊖ F ∘ (G ∘ H)
∘-assoc {End = End} _ _ _ = refl
  where open Setoid End

∘-identityˡ : (F : From ⟶ To) → id ∘ F ⊖ F
∘-identityˡ {To = To} _ = refl
  where open Setoid To

∘-identityʳ : (F : From ⟶ To) → F ∘ id ⊖ F
∘-identityʳ {To = To} _ = refl
  where open Setoid To

compose : (To ⇨ More) ⟶ (From ⇨ To) ⇨ From ⇨ More
compose  = record
  { _⟨$⟩_ = λ F → record
    { _⟨$⟩_ = F ∘_
    ; cong = λ G⊖G′ → F .cong G⊖G′
    }
  ; cong = λ F⊖F′ → F⊖F′
  }

const : To ⟶ From ⇨ To
const {To = To} = record
  { _⟨$⟩_ = λ y → record
    { _⟨$⟩_ = Fun.const y
    ; cong = Fun.const refl
    }
  ; cong = λ y≈y′ → y≈y′
  }
  where open Setoid To

infixl 8 _ˢ_
_ˢ_ : (From ⟶ To ⇨ More) → (From ⟶ To) → From ⟶ More
_ˢ_ {More = More} F G = record
  { _⟨$⟩_ = λ x → F ⟨$⟩ x ⟨$⟩ (G ⟨$⟩ x)
  ; cong = λ x≈x′ → trans (F .cong x≈x′) ((F ⟨$⟩ _) .cong (G .cong x≈x′)) }
  where open Setoid More

ap : (From ⇨ To ⇨ More) ⟶ (From ⇨ To) ⇨ From ⇨ More
ap = record
  { _⟨$⟩_ = λ F → record
    { _⟨$⟩_ = F ˢ_
    ; cong = λ G⊖G′ → (F ⟨$⟩ _) .cong G⊖G′
    }
  ; cong = λ F⊖F′ → F⊖F′
  }

flip : (From ⇨ To ⇨ More) ⟶ (To ⇨ From ⇨ More)
flip = record
  { _⟨$⟩_ = λ F → record
    { _⟨$⟩_ = λ x → record
      { _⟨$⟩_ = λ y → F ⟨$⟩ y ⟨$⟩ x
      ; cong = λ y≈y′ → F .cong y≈y′
      }
    ; cong = λ x≈x′ → (F ⟨$⟩ _) .cong x≈x′
    }
  ; cong = λ F⊖F′ → F⊖F′
  }
