module Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Isomorphism using (_≃_; extensionality)
open import Equality using (≡-implies-≤; +-monoˡ-≤)
open import Inductions using (+-rearrange; +-comm; +-suc; +-identityʳ; +-assoc)
open import Inductions using (Bin; inc; to; from; from-to)
open import Relations using (Can; One; to-from; to-can)

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
  → B M
∀-elim L M = L M

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
    { to = λ f → ( (λ a → proj₁ (f a)) , (λ a → proj₂ (f a)) )
    ; from = λ{ (g , h) → λ a → g a , h a }
    ; from∘to = λ x → refl
    ; to∘from = λ{ (g , h) → refl }
    }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} → 
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ x) = λ a → inj₁ (x a)
⊎∀-implies-∀⊎ (inj₂ y) = λ a → inj₂ (y a)

-- the converse does not stand, consider A = {1, 2}, explanation:
-- B 1 B 2 C 1 C 2
-- ---------------
--  1   0   0   1
