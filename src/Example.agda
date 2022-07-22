{-# OPTIONS --guardedness --sized-types #-}
module Example where  

open import Data.ITree hiding (_>>=_)
open import C.Monad
open CRun (MonadITree′ ∅)
open import Data.Sum
open import Data.Product
open import Data.Maybe hiding (_>>=_)
open import Data.Bool
open import Data.Unit
open import Data.List
open import Relation.Binary.PropositionalEquality

example1 : CRun (ITree′′ ∅) CVal
example1 = malloc 1

example1-test : example1 emptyState ≡ ret (inj₂ (ptr false 0 0 , (mk-cstate 1 ((0 , nothing ∷ []) ∷ []) []))) -- (ptr 0 0 , (mk-cstate 1 ((0 , nothing ∷ []) ∷ []) [])))
example1-test = refl 

example2 : CRun (ITree′′ ∅) ⊤ 
example2 = do
    addr ← malloc 1  
    free addr  

example2-test : example2 emptyState ≡ ret (inj₂ (tt , mk-cstate 1 [] []))
example2-test = refl
