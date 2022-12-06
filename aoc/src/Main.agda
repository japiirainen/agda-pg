module Main where

open import Function
open import Data.Unit.Polymorphic
open import Data.String as String
open import IO.Base as IO using (IO; Main; _>>=_; _>>_)
open import IO.Finite

import Day01

run : String → (String → String) → IO ⊤
run name f = do
  input ← readFile ("input/" ++ name)
  putStrLn (name ++ ": " ++ f input)

main : Main
main = IO.run do
  run "01" Day01.sol
