{-# OPTIONS --without-K --safe #-}

module Data.Fin.Properties where

open import Data.Fin.Base
open import Relation.Equality.Base
open import Data.Sum.Base as Sum
open import Data.Product.Base as Product
open import Data.Nat.Base
open import Relation.Reasoning.Setoid
open import Universe.Set

private
  instance
    ≡setoid : ∀ {a} {A : Set a} → _
    ≡setoid {A = A} = setoid A

splitAt∘inj+ : ∀ {m} n → splitAt m ∘ inj+ n ≗ inj₁
splitAt∘inj+ _ zero = refl
splitAt∘inj+ n (suc i) = Sum.map suc (λ j → j) =$= splitAt∘inj+ n i

splitAt∘ℕ+ : ∀ m {n} → splitAt m ∘ (_ℕ+_ m {n}) ≗ inj₂
splitAt∘ℕ+ 0 _ = refl
splitAt∘ℕ+ (suc m) i = Sum.map suc (λ j → j) =$= splitAt∘ℕ+ m i

join∘splitAt : ∀ m {n} → join ∘ splitAt m {n} ≗ id
join∘splitAt 0 _ = refl
join∘splitAt (suc _) zero = refl
join∘splitAt (suc m) (suc i) with splitAt m i in eq
... | inj₁ j =
  join (Sum.map suc (λ k → k) (inj₁ j)) ≡⟨⟩
  join (inj₁ (suc j)) ≡⟨⟩
  inj+ _ (suc j) ≡⟨⟩
  suc (inj+ _ j) ≡⟨⟩
  suc (join (inj₁ j)) ≡˘⟨ suc =$= join =$= eq ⟩
  suc (join (splitAt m i)) ≡⟨ suc =$= join∘splitAt m i ⟩
  suc i ∎
--   where
--     open Relation.Reasoning (_≡_ {A = Fin _})
--     open Equiv refl trig
... | inj₂ j =
  join (Sum.map suc (λ k → k) (inj₂ j)) ≡⟨⟩
  join (inj₂ j) ≡⟨⟩
  suc m ℕ+ j ≡⟨⟩
  suc (m ℕ+ j) ≡⟨⟩
  suc (join (inj₂ j)) ≡˘⟨ suc =$= join =$= eq ⟩
  suc (join (splitAt m i)) ≡⟨ suc =$= join∘splitAt m i ⟩
  suc i ∎
--   where
--     open Relation.Reasoning (_≡_ {A = Fin _})
--     open Equiv refl trig

splitAt∘join : ∀ {m n} → splitAt m {n} ∘ join ≗ id
splitAt∘join (inj₁ i) = splitAt∘inj+ _ i
splitAt∘join (inj₂ i) = splitAt∘ℕ+ _ i

combine∘extract : ∀ m {n} → uncurry combine ∘ extract m {n} ≗ id
combine∘extract (suc m) {n} i with splitAt n i in eq
... | inj₁ j =
  uncurry combine (zero {m} , j) ≡⟨⟩
  combine {suc m} zero j ≡⟨⟩
  inj+ (m * n) j ≡⟨⟩
  join (inj₁ j) ≡˘⟨ join =$= eq ⟩
  join (splitAt n i) ≡⟨ join∘splitAt n i ⟩
  i ∎
--   where
--     open Relation.Reasoning (_≡_ {A = Fin _})
--     open Equiv refl trig
... | inj₂ j with extract m j in eq'
... | h , l =
  uncurry combine (Product.map suc (λ k → k) (h , l)) ≡⟨⟩
  uncurry combine (suc h , l) ≡⟨⟩
  combine (suc h) l ≡⟨⟩
  n ℕ+ combine h l ≡⟨⟩
  n ℕ+ uncurry combine (h , l) ≡˘⟨ n ℕ+_ =$= uncurry combine =$= eq' ⟩
  n ℕ+ uncurry combine (extract m j) ≡⟨ n ℕ+_ =$= combine∘extract m j ⟩
  n ℕ+ j ≡⟨⟩
  join (inj₂ j) ≡˘⟨ join =$= eq ⟩
  join (splitAt n i) ≡⟨ join∘splitAt n i ⟩
  i ∎
--   where
--     open Relation.Reasoning (_≡_ {A = Fin _})
--     open Equiv refl trig

extract∘combine : ∀ {m n} → extract m {n} ∘₂ combine ≗₂ _,_
extract∘combine {suc m} {n} zero j =
  extract _ (combine {suc m} zero j) ≡⟨⟩
  extract _ (inj+ _ j) ≡⟨⟩
  ⟨ zero ,_ , (λ k → Product.map suc (λ l → l) (extract m k)) ⟩ (splitAt n (inj+ _ j)) ≡⟨ ⟨ _ , _ ⟩ =$= splitAt∘inj+ (m * n) j ⟩
  ⟨ zero ,_ , (λ k → Product.map suc (λ l → l) (extract m k)) ⟩ (inj₁ j) ≡⟨⟩
  zero , j ∎
--   where
--     open Relation.Reasoning (_≡_ {A = Fin (suc m) × Fin n})
--     open Equiv refl trig
extract∘combine {suc m} {n} (suc i) j =
  extract _ (combine (suc i) j) ≡⟨⟩
  extract _ (n ℕ+ combine i j) ≡⟨⟩
  ⟨ zero ,_ , (λ k → Product.map suc (λ l → l) (extract m k)) ⟩ (splitAt n (n ℕ+ combine i j)) ≡⟨ ⟨ _ , _ ⟩ =$= splitAt∘ℕ+ n (combine i j) ⟩
  ⟨ zero ,_ , (λ k → Product.map suc (λ l → l) (extract m k)) ⟩ (inj₂ (combine i j)) ≡⟨⟩
  Product.map suc (λ k → k) (extract m (combine i j)) ≡⟨ Product.map suc (λ k → k) =$= extract∘combine i j ⟩
  Product.map suc (λ k → k) (i , j) ≡⟨⟩
  suc i , j ∎
  -- where                         
  --   open Relation.Reasoning (_≡_ {A = Fin (suc m) × Fin n})
  --   open Equiv refl trig
