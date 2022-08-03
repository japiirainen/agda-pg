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

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n rewrite +-suc m n = refl

+-commutativity : ∀ (m n : ℕ) → m + n ≡ n + m
+-commutativity m zero rewrite +-identity m = refl
+-commutativity m (suc n) rewrite +-suc m n | +-commutativity m n = refl

+-associativity : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-associativity zero n p = refl
+-associativity (suc m) n p rewrite +-associativity m n p = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym (+-associativity m n p) ⟩
    m + n + p
  ≡⟨ cong (_+ p) (+-commutativity m n) ⟩
    n + m + p
  ≡⟨ +-associativity n m p ⟩
    n + (m + p)
  ∎

*-distributivity-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distributivity-+ zero n p = refl
*-distributivity-+ (suc m) n p rewrite
    *-distributivity-+ m n p
  | sym (+-associativity p (m * p) (n * p)) = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite
    *-distributivity-+ n (m * n) p
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

∸zero : ∀ (n : ℕ) → 0 ∸ n ≡ 0
∸zero zero = refl
∸zero (suc n) = refl

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil = x1 nil
inc (x0 b) = x1 b
inc (x1 b) = x0 inc b

to : ℕ → Bin
to zero = nil
to (suc n) = inc (to n)

from : Bin → ℕ
from nil = zero
from (x0 b) = 2 * from b
from (x1 b) = 1 + 2 * from b

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

inc-suc : ∀ (x : Bin) → from (inc x) ≡ suc (from x)
inc-suc nil = refl
inc-suc (x0 x) = refl
inc-suc (x1 x) rewrite
    inc-suc x
  | +-suc (suc (from x)) (from x + 0) = refl

from-to : ∀ (n : ℕ) → from (to n) ≡ n
from-to zero = refl
from-to (suc n) rewrite
    inc-suc (to n)
  | from-to n = refl
