{-# OPTIONS --without-K --guardedness #-}
module Main where

open import Data.Unit.Polymorphic
open import Level
open import IO
import IO.Primitive as Prim

main : Prim.IO (⊤ {0ℓ})
main = run (putStrLn "hello world!")