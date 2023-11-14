{-# OPTIONS --without-K --safe #-}

module Data.Nat.Core where

open import Agda.Builtin.Nat public renaming
  ( Nat  to ℕ
  ; _==_ to _≟_
  ; _<_  to _<?_
  ; _-_  to _∸_
  )
