{-# OPTIONS --guardedness #-}
module Example where  

-- open import Data.ITree 
-- open import Category.MonadSuc
-- open import C.Monad (MonadSucITree {E = EmptyE})

-- open import Relation.Binary.PropositionalEquality
-- open import Data.Sum
-- open import Data.Product
-- open import Data.Unit
-- open import Data.List
-- open import Data.Maybe hiding (_>>=_)
-- open MonadSuc MonadSucCM

-- example1 : CM (ITree EmptyE) CVal
-- example1 = malloc 1

-- example1-test : example1 emptyState ≡ ret (inj₂ (mk-cstate 1 ((0 , nothing ∷ []) ∷ []) [] , ptr 0 0))
-- example1-test = refl 


-- example2 : CM (ITree EmptyE) ⊤ 
-- example2 = do
--     addr ← malloc 1  
--     free addr  

-- example2-test : example2 emptyState ≡ ret (inj₂ (mk-cstate 1 [] [] , tt))
-- example2-test = refl

