module Semigroup where

open import Relation.Binary.PropositionalEquality
open import Data.Bool

record Semigroup (a : Set) : Set where
  field 
    _⊛_ : a → a → a
    -- Semigroup laws
    -- associativity basically means that perenthesis do not matter.
    associative : ∀ a b c → (a ⊛ b) ⊛ c ≡ a ⊛ (b ⊛ c)

andAssociative : ∀ a b c → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
andAssociative false b c = refl
andAssociative true b c = refl

andSemigroup : Semigroup Bool
andSemigroup = record 
  { _⊛_ = _∧_
  ; associative = andAssociative
  }

orAssociative : ∀ a b c → (a ∨ b) ∨ c ≡ a ∨ (b ∨ c)
orAssociative false b c = refl
orAssociative true b c = refl

orSemigroup : Semigroup Bool
orSemigroup = record
  { _⊛_ = _∨_
  ; associative = orAssociative
  }
