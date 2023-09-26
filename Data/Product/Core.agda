{-# OPTIONS --without-K --safe #-}

module Data.Product.Core where

open import Agda.Builtin.Sigma public
  renaming (fst to proj₁; snd to proj₂)
  hiding (module Σ)

module Σ = Agda.Builtin.Sigma.Σ
  renaming (fst to proj₁; snd to proj₂)
