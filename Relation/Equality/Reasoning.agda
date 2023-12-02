{-# OPTIONS --without-K --safe #-}

module Relation.Equality.Reasoning {a} {A : Set a} where

open import Relation.Equality.Base

open import Relation.Reasoning (_≡_ {A = A}) public

open Equiv refl trig public
