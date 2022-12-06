module Utils where

import Data.Nat.Show as ℕ
open import Data.Nat.Base using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Data.String as String using (String; _≈?_)
open import Data.Unit
open import Reflection

macro
  print : Term → Term → TC ⊤
  print t hole = do
    v ← normalise t
    debugPrint "print" 0 (termErr v ∷ [])
    unify hole (con (quote tt) [])

record Show (α : Set) : Set where
  constructor show:=
  field show : α → String

open Show ⦃...⦄ public

instance
  Show-ℕ : Show ℕ
  Show-ℕ = show:= ℕ.show

  Show-× : ∀ {α β : Set} → ⦃ Show α ⦄ → ⦃ Show β ⦄ → Show (α × β)
  Show-× = show:= λ{ (x , y) → show x String.++ " , " String.++ show y }

  Show-Maybe : ∀ {α : Set} → ⦃ Show α ⦄ → Show (Maybe α)
  Show-Maybe = show:= λ where
    nothing → "nothing"
    (just x) → show x
