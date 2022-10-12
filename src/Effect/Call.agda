{-# OPTIONS --guardedness --sized-types #-}
module Effect.Call (Val : Set) where

open import Data.Unit
open import Data.List
open import Data.ITree


data Command : Set where 
    call : Val → List Val → Command 

Result : Command → Set
Result (call _ _) = Val

CallE : Effect 
CallE = record { Command = Command ; Result = Result } 