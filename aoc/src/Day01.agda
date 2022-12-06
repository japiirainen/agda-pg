module Day01 where

open import Function
open import Data.Maybe using (Maybe; just; nothing; from-just)
open import Data.Maybe.Effectful as Maybe using (applicative)
import Data.Nat.Show as ℕ using (readMaybe)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.List.Base using (List; []; _∷_; map; sum; take; reverse)
open import Data.List.NonEmpty as List+ using (wordsBy; toList) renaming (map to map+)
open import Data.List.Effectful as List
open import Data.String as String using (String; lines; _≈?_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Nat.Properties using (≤-decTotalOrder)

open import Data.List.Extrema.Nat using (max)

open import Data.List.Sort.MergeSort ≤-decTotalOrder using (sort)

open import Utils

Input : Set
Input = List (List ℕ)

readInput : List String → Maybe Input
readInput = traverse (traverse (ℕ.readMaybe 10) ∘ toList) ∘ wordsBy ("" ≈?_)
  where open List.TraversableA Maybe.applicative renaming (mapA to traverse)

example : Input
example = from-just $ readInput $
  "1000" ∷
  "2000" ∷
  "3000" ∷
  "" ∷
  "4000" ∷
  "" ∷
  "5000" ∷
  "6000" ∷
  "" ∷
  "7000" ∷
  "8000" ∷
  "9000" ∷
  "" ∷
  "10000" ∷
  []

solve¹ : Input → ℕ
solve¹ = max 0 ∘ map sum

_ : solve¹ example ≡ 24000
_ = refl

solve² : Input → ℕ
solve² = sum ∘ take 3 ∘ reverse ∘ sort ∘ map sum

_ : solve² example ≡ 45000
_ = refl

-- Entrypoint
sol : String → String
sol input with readInput (lines input)
... | just input = show (solve¹ input , solve² input)
... | nothing = "Invalid input"
