module Inductions where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

data Bool : Set where
  True : Bool
  False : Bool

_∨_ : Bool → Bool → Bool
True ∨ _ = True
False ∨ b = b

+-identity : ∀ (n : ℕ) → n + 0 ≡ n
+-identity zero = refl
+-identity (suc n) rewrite +-identity n = refl

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n rewrite +-suc m n = refl

+-commutativity : ∀ (m n : ℕ) → m + n ≡ n + m
+-commutativity m zero rewrite +-identity m = refl
+-commutativity m (suc n) rewrite +-suc m n | +-commutativity m n = refl
