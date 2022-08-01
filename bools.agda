module Bools where

open import Function
open import Data.Bool
open import Relation.Binary.PropositionalEquality

Idempotent : ∀ {a} → (a → a) → Set
Idempotent f = ∀ b → f (f b) ≡ f b

-- (false ∧ true ∧ true) ≡ false ∧ true
-- ∀ a b → a ∧ (a ∧ b) ≣ a ∧ b
andIdempotent : ∀ b → Idempotent (_∧_ b)
andIdempotent false b = refl
andIdempotent true b = refl

-- (false ∨ true ∨ true) ≡ false ∨ true
-- ∀ a b → a ∧ (a ∧ b) ≣ a ∧ b
orIdempotent : ∀ b → Idempotent (_∨_ b)
orIdempotent false b = refl
orIdempotent true b = refl

-- id ∘ id ≡ id
-- ∀ a → (id ∘ id) a ≡ id a
idIdempotent : ∀ a → Idempotent (id {A = a})
idIdempotent = λ a b → refl
