module Effect.Store (Var Val : Set) where

open import Data.Unit
open import Data.ITree

data Command : Set where 
    get : Var → Command 
    set : Var → Val → Command 
    ref : Val → Command  
    deref : Val → Command  

Result : Command → Set
Result (set _ _) = ⊤
Result (get _) = Val 
Result (ref _) = Val 
Result (deref _) = Val 

StoreE : Effect 
StoreE = record { Command = Command ; Result = Result } 