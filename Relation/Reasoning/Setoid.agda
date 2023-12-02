{-# OPTIONS --without-K --safe #-}

open import Universe.Setoid.Base using (Setoid)

module Relation.Reasoning.Setoid {a r} (S : Setoid a r) where

open Setoid S

open import Relation.Reasoning _≈_ public

open Equiv refl trig public
