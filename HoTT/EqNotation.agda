{-# OPTIONS --without-K --safe #-}

module HoTT.EqNotation where

open import Relation.Binary.PropositionalEquality public
  renaming
  ( trans to infixr 9 _∙_
  ; sym   to infix 10 _⋆
  )
