open import Data.Maybe
open import Data.Bool hiding (if_then_else_)
open import Relation.Binary.PropositionalEquality

data Term : Set where
  t : Term
  f : Term
  if_then_else_ : Term → Term → Term → Term
  zero : Term
  succ : Term → Term
  pred : Term → Term
  iszero : Term → Term

isNumerical : Term → Bool
isNumerical zero = true
isNumerical (succ t₁) = isNumerical t₁
isNumerical _ = false

eval₁ : Term → Maybe Term
eval₁ (if t then t₂ else t₃) = just t₂
eval₁ (if f then t₂ else t₃) = just t₃
eval₁ (if t₁ then t₂ else t₃) = do
  t₁' ← eval₁ t₁
  just (if t₁' then t₂ else t₃)
eval₁ (succ t₁) = do
  t₁' ← eval₁ t₁
  just (succ t₁')
eval₁ (pred zero) = just zero
eval₁ (pred (succ nv₁)) with isNumerical nv₁
... | true = just nv₁
... | false = nothing
eval₁ (pred t₁) = do
  t₁' ← eval₁ t₁
  just (pred t₁')
eval₁ (iszero zero) = just t
eval₁ (iszero (succ nv₁)) with isNumerical nv₁
... | true = just f
... | false = nothing
eval₁ (iszero t₁) = do
  t₁' ← eval₁ t₁
  just (iszero t₁')
eval₁ _ = nothing

eval : Term → Term
{-# TERMINATING #-}
eval t₁ = maybe eval t₁ (eval₁ t₁)

test₁ : eval (if t then succ zero else succ (succ zero)) ≡ succ zero
test₁ = refl

test₂ : eval t ≡ t
test₂ = refl

test₃ : eval (if f then t else f) ≡ f
test₃ = refl

test₄ : eval zero ≡ zero
test₄ = refl

test₅ : eval (succ (pred zero)) ≡ (succ zero)
test₅ = refl

test₆ : eval (iszero (pred (succ (succ zero)))) ≡ f
test₆ = refl
