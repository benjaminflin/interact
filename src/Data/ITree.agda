module Data.ITree where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.Core
open import Codata.Thunk hiding (map)
open import Control.Functor
open import Control.Monad
open import Data.Unit 
open import Data.Empty 
open import Level
open import Function
open import Data.Sum hiding (map)
open import Size

-- ITree: Free monad with tau
-- tau is a coinductive which allows representation of non-termination
data ITree {a b} (i : Size) (E : Set a → Set b) (R : Set a) : Set (suc a ⊔ b) where
    ret : R → ITree i E R  
    tau : (τ : Thunk (λ i → ITree i E R) i) → ITree i E R
    vis : ∀ {A} → (e : E A) → (k : A → ITree i E R) → ITree i E R

private
    variable
        a b : Level 
        A B R : Set a 
        E : Set a → Set b
        i : Size

bind : ITree i E A → (A → ITree i E B) → ITree i E B 
bind (ret x) f = f x
bind (tau τ) f = tau λ where .force → bind (force τ) f 
bind (vis e k) f = vis e λ y → bind (k y) f

ITree′ : (E : Set a → Set b) → (A : Set a) → Set (suc a ⊔ b) 
ITree′ E A = ∀ {i} → ITree i E A   

instance 
    MonadITree : Monad {a = b} (ITree i E) 
    MonadITree = record { _>>=_ = bind; pure = ret } 

open Monad {{...}}
open Functor {{...}}

-- helper for triggering an effect
trigger : E A → ITree i E A
trigger e = vis e ret

iter : ∀ {A : Set} → (A → ITree i E (A ⊎ B)) → A → ITree i E B
iter body a = do
    ab ← body a
    tau (λ where .force → case ab of λ where (inj₁ a) → iter body a
                                             (inj₂ b) → pure b)


Effect : (a b : Level) → Set (suc a ⊔ suc b)
Effect a b = Set a → Set b

data ∅ {a} : Effect a (suc a) where

infixr 3 _⊕_

_⊕_ : Effect a b → Effect a b → Effect a b 
(E ⊕ F) A = E A ⊎ F A   

data Finite {a b} {E : Set a → Set b} {A : Set a} (i : Size) : ITree i E A → Set (suc a ⊔ suc b) where
    fin-ret : ∀ {x} → Finite i (ret x)
    fin-tau : ∀ {τ} → Finite i (force τ) → Finite i (tau τ)
    fin-vis : ∀ {B} {e : E B} {k} → Finite i (vis e k)  

-- Relations up to tau 
data Rutt {a b} {E : Set a → Set b} {A : Set a} (i : Size) (R : Rel A a) : ITree i E A → ITree i E A → Set (suc a ⊔ suc b) where  
    rutt-ret : ∀ {x y} → R x y → Rutt i R (ret x) (ret y) 
    rutt-tau-left : ∀ {x y : Thunk (λ i → ITree i E A) ∞} → Thunk (λ i → Rutt i R (force x) (tau y)) i → Rutt i R (tau x) (tau y)
    rutt-tau-right : ∀ {x y : Thunk (λ i → ITree i E A) ∞} → Thunk (λ i → Rutt i R (tau x) (force y)) i → Rutt i R (tau x) (tau y)
    rutt-tau-both : ∀ {x y : Thunk (λ i → ITree i E A) ∞} → Thunk (λ i → Rutt i R (force x) (force y)) i → Rutt i R (tau x) (tau y)   
    rutt-vis : ∀ {B} {e : E B} {k₁ k₂} → (∀ x → Rutt i R (k₁ x) (k₂ x)) → Rutt i R (vis e k₁) (vis e k₂)

[_]_≈_ : ∀ i → ITree i E A → ITree i E A → Set _
[ i ] x ≈ y = Rutt i _≡_ x y 

≈-refl : ∀ {x : ITree i E A} → [ i ] x ≈ x
≈-refl {x = ret x} = rutt-ret refl
≈-refl {x = tau τ} = rutt-tau-both λ where .force → ≈-refl {x = force τ}
≈-refl {x = vis e k} = rutt-vis (λ x → ≈-refl) 

≈-sym : ∀ {x y : ITree i E A} → [ i ] x ≈ y → [ i ] y ≈ x 
≈-sym (rutt-ret refl) = rutt-ret refl
≈-sym (rutt-tau-left x) = rutt-tau-right λ where .force → ≈-sym (force x)
≈-sym (rutt-tau-right x) = rutt-tau-left λ where .force → ≈-sym (force x)
≈-sym (rutt-tau-both x) = rutt-tau-both λ where .force → ≈-sym (force x)
≈-sym (rutt-vis f) = rutt-vis λ y → ≈-sym (f y) 
