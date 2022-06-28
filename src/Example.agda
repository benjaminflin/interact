{-# OPTIONS --guardedness #-}
module Example where  

open import Data.ITree 
open import Category.MonadSuc
open import C.Monad (MonadSucITree {E = EmptyE})

open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Product
open import Data.Unit
open import Data.List
open import Data.Maybe
open MonadSuc MonadSucCM

example : CM (ITree EmptyE) CVal
example = malloc 1

example-test : example emptyState ≡ ret (inj₂ (mk-cstate 1 ((0 , nothing ∷ []) ∷ []) [] , ptr 0 0))
example-test = refl -- {! refl  !}



