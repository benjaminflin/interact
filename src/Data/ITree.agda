{-# OPTIONS --guardedness --sized-types #-}
module Data.ITree where

open import Relation.Binary.PropositionalEquality
open import Data.Unit 
open import Level
open import Function
open import Data.Sum 
open import Category.Functor
open import Category.Monad
open import Size

data ITree (i : Size) (S : Set) (T : S → Set) (R : Set) : Set
record Tau (i : Size) (S : Set) (T : S → Set) (R : Set) : Set

-- ITree: Free monad with tau
-- tau is a coinductive which allows representation of non-termination
data ITree i S T R where 
    ret : R → ITree i S T R 
    tau : Tau i S T R → ITree i S T R 
    vis : (s : S) → (k : T s → ITree i S T R) → ITree i S T R 

record Tau i S T R where
    coinductive
    constructor mk-tau
    field
        τ : {j : Size< i} → ITree j S T R

open Tau

private
    variable
        A B R S : Set
        T : S → Set
        i : Size

_>>=_ : ITree i S T A → (A → ITree i S T B) → ITree i S T B  
bind-τ : Tau i S T A → (A → ITree i S T B) → Tau i S T B
ret x >>= f = f x
vis e k >>= f = vis e λ y → (k y) >>= f  
tau x >>= f = tau (bind-τ x f)
τ (bind-τ x f) = (τ x) >>= f 

instance 
    MonadITree : RawMonad (ITree i S T) 
    MonadITree = record { _>>=_ = _>>=_; return = ret } 


-- helper for triggering an effect
trigger : (s : S) → ITree i S T (T s)
trigger s = vis s ret

iter : (A → ITree i S T (A ⊎ B)) → A → ITree i S T B
iter-τ : (A ⊎ B) → (A → ITree i S T (A ⊎ B)) → Tau i S T B
iter body a = body a >>= λ ab → tau (iter-τ ab body)   
τ (iter-τ (inj₁ a) body) = iter body a   
τ (iter-τ (inj₂ b) _) = ret b 

record Effect : Set₁ where 
    field
        Command : Set
        Result : Command → Set 

open Effect

ITree′ : Size → Effect → Set → Set 
ITree′ i e R = ITree i (Command e) (Result e) R

Tau′ : Size → Effect → Set → Set 
Tau′ i e R = Tau i (Command e) (Result e) R

ITree′′ : {i : Size} → Effect → Set → Set 
ITree′′ {i} e R = ITree′ i e R 

Tau′′ : {i : Size} → Effect → Set → Set 
Tau′′ {i} e R = Tau′ i e R 

infixr 3 _⊕_

_⊕_ : Effect → Effect → Effect   
Command (e ⊕ f) = Command e ⊎ Command f
Result (e ⊕ f) (inj₁ x) = Result e x
Result (e ⊕ f) (inj₂ y) = Result f y 


-- Indexes Itree/Tau by terminating programs
data Terminates (i : Size) : ITree i S T R → Set where
    term-ret : (r : R) → Terminates i {S = S} {T = T} (ret r)
    term-tau : {j : Size< i} → {t : Tau i S T R} → Terminates j (τ t) → Terminates i (tau t)
    term-vis : (s : S) → {j : T s → ITree i S T R} → (k : (t : T s) → Terminates i (j t)) → Terminates i (vis s j)

