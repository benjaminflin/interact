{-# OPTIONS --guardedness #-}
module Data.ITree where

open import Relation.Binary.PropositionalEquality
open import Data.Unit 
open import Level
open import Function
open import Category.MonadSuc
open import Data.Sum 

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

MonadSucITree : MonadSuc (ITree E)
MonadSucITree = record { _>>=_ = _>>=_; return = ret } 
    where
    bind-τ : Tau E A → (A → Tau E B) → Tau E B
    _>>=_ : ITree E A → (A → ITree E B) → ITree E B  
    ret x >>= f = f x
    tau x >>= f = tau (bind-τ x λ t → mk-tau (f t))
    vis e k >>= f = vis e λ y → (k y) >>= f  
    τ (bind-τ x f) = (τ x) >>= (tau ∘ f) 

-- helper for triggering an effect
trigger : (e : E A) → ITree E A
trigger e = vis e ret 

_⊕_ : (Set → Set) → (Set → Set) → Set → Set
(f ⊕ g) x = f x ⊎ g x 
infixr 3 _⊕_

_↝_ : (Set → Set) → (Set → Set) → Set → Set
(f ↝ g) x = f x → g x   
infixr 1 _↝_


-- Indexes Itree/Tau by terminating programs
data Terminates : ITree E R → Set₁ where
    ret' : (r : R) → Terminates {E = E} (ret r)
    tau' : {t : Tau E R} → Terminates (τ t) → Terminates (tau t)
    vis' : {A : Set} → (e : E A) → {j : A → ITree E R} → (k : (a : A) → Terminates (j a)) → Terminates (vis e j)
