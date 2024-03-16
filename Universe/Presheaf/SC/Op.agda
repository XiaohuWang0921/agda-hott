{-# OPTIONS --without-K --safe #-}

module Universe.Presheaf.SC.Op where

open import Universe.Presheaf.Base hiding (id; _∘_)
open import Universe.Presheaf.Op
open import Universe.Presheaf.SC
open import Data.ASC
open import Data.Nat.Base
open import Level hiding (_ℕ+_)
open import Data.Fin.Base as Fin hiding (_ℕ+_)
open import Data.Fin.Properties
open import Data.Fin.Subset.Base
open import Data.Fin.Subset.Properties
open import Data.Product.Base
open import Universe.Set

private
  variable
    a r : Level
    P : Presheaf a r
    m n : ℕ
    asc : ASC n
    bsc : ASC (suc n)

extend-ℕ* : SC (m ℕ* P) asc → SC P (preimages (proj₂ ∘ extract m) asc)
extend-ℕ* {P = P} sc .for {s = s} s∈ = proj P (embed (preimage-image (proj₂ ∘ extract _) s)) (sc .for s∈)
