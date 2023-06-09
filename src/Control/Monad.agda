module Control.Monad where 

open import Control.Functor 
open import Level
open import Function.Base

private
    variable
        a b : Level 
        A B : Set a

record Monad (M : Set a → Set b) : Set (suc a ⊔ b) where
    field
        _>>=_ : M A → (A → M B) → M B
        pure : A → M A 
        
    functor : Functor M
    functor = record { map = λ f m → m >>= (pure ∘ f) }