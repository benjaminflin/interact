{-# OPTIONS --guardedness #-}
module Data.ITree where

open import Relation.Binary.PropositionalEquality
open import Data.Unit 
open import Level

private 
    variable
        f : Level

data ITree (E : Set → Set) (R : Set) : Set₁ 
record Tau (E : Set → Set) (R : Set) : Set₁

-- ITree: Free monad with tau
-- tau is a coinductive which allows representation of non-termination
data ITree E R where 
    ret : R → ITree E R 
    tau : Tau E R → ITree E R 
    vis : {A : Set} → (e : E A) → (k : A → ITree E R) → ITree E R

record Tau E R where
    constructor mk-tau
    coinductive
    field
        τ : ITree E R  

open Tau

private
    variable
        E : Set → Set
        A B R : Set

data EmptyE : Set → Set where

record MonadSuc (M : Set f → Set (suc f)) : Set (suc f) where
    field
        _>>=_ : {A B : Set f} → M A → (A → M B) → M B 
        return : {A : Set f} → A → M A 

MonadSucITree : MonadSuc (ITree E)
MonadSucITree = record { _>>=_ = _>>=_; return = ret } 
    where
    bind-τ : Tau E A → (A → Tau E B) → Tau E B
    _>>=_ : ITree E A → (A → ITree E B) → ITree E B  
    ret x >>= f = f x
    tau x >>= f = tau (bind-τ x λ t → mk-tau (f t))
    vis e k >>= f = vis e λ y → (k y) >>= f  
    τ (bind-τ x f) = tau (bind-τ x f) -- is this correct?

-- helper for triggering an effect
trigger : (e : E A) → ITree E A
trigger e = vis e ret 