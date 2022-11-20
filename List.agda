module List where

open import Agda.Builtin.Nat
open import Agda.Builtin.Maybe

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

_!!!_ : ∀ {A} → List A → Nat → Maybe A
[]       !!! _       = nothing
(_ ∷ xs) !!! (suc n) = xs !!! n
(x ∷ _)  !!! zero    = just x

data ListOfLength (A : Set) : Nat → Set where
  [] : ListOfLength A 0
  _∷_ : ∀ {n} → A → ListOfLength A n → ListOfLength A (suc n)

data Nat< : Nat → Set where
  zero : ∀ {n} → Nat< (suc n)
  suc : ∀ {n} → Nat< n → Nat< (suc n)

_!!_ : ∀ {A n} → ListOfLength A n → Nat< n → A
(x ∷ _) !! zero  = x
(_ ∷ xs) !! suc n = xs !! n


-- α
-- Def Innerproduct ≡ (Insert +)∘(ApplyToAll x)∘Transpose
-- Def IP ≡ (/+)∘(αx)∘Trans.
-- ÷ ⊥ → λ ∧ ∨ ̸ ¬
