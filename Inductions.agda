module Inductions where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡; _∎; _≡⟨⟩_)
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

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n rewrite +-suc m n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero rewrite +-identity m = refl
+-comm m (suc n) rewrite +-suc m n | +-comm m n = refl

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p rewrite +-assoc m n p = refl

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym (+-assoc m n p) ⟩
    m + n + p
  ≡⟨ cong (_+ p) (+-comm m n) ⟩
    n + m + p
  ≡⟨ +-assoc n m p ⟩
    n + (m + p)
  ∎

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite
    *-distrib-+ m n p
  | sym (+-assoc p (m * p) (n * p)) = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite
    *-distrib-+ n (m * n) p
  | *-assoc m n p = refl

*-zero : ∀ (m : ℕ) → m * 0 ≡ 0
*-zero zero = refl
*-zero (suc m) rewrite *-zero m = refl

*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-suc zero n = refl
*-suc (suc m) n rewrite *-suc m n | +-swap n m (m * n) = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero = *-zero m
*-comm m (suc n) rewrite *-suc m n | *-comm m n = refl

∸-zero : ∀ (n : ℕ) → 0 ∸ n ≡ 0
∸-zero zero = refl
∸-zero (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero p = refl
∸-+-assoc zero (suc n) p rewrite ∸-zero p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil = x1 nil
inc (x0 m) = x1 m
inc (x1 m) = x0 inc m

to : ℕ → Bin
to zero = x0 nil
to (suc n) = inc (to n)

from : Bin → ℕ
from nil = 0
from (x0 n) = 2 * from n
from (x1 n) = 1 + 2 * from n

--  Exercise

inc-suc : ∀ (x : Bin) → from (inc x) ≡ suc (from x)
inc-suc nil = refl
inc-suc (x0 x) = refl
inc-suc (x1 x) rewrite inc-suc x | +-suc (suc (from x)) (from x + 0) = refl

-- to (from x) ≡ x is false:
--   to ( from (x0 x0 nil)) ≡ x0 nil != x0 x0 nil

from-to : ∀ (n : ℕ) → from (to n) ≡ n
from-to zero = refl
from-to (suc n) rewrite inc-suc (to n) | from-to n = refl
