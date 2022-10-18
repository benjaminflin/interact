module C.Denote (Var : Set) where

open import Data.Unit
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Bool
open import Data.List renaming (map to lmap)
open import Data.Digit
open import Data.Sum 
open import Data.Product 
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.ITree hiding (_>>=_)
open import Effect.Network using (NetworkE)
open import C.AST (Var) 
open import Function
open import Category.Functor
open import Category.Monad 
open import Relation.Binary.PropositionalEquality
open import Data.List.Categorical 

import Data.Integer as Int
import Data.Integer.DivMod as Int
import Data.List.Relation.Unary.All as All

data Val : Set where 
    val : (n : ℕ) → (p : ℕ) → Val 

open import Effect.Store (Var) (Val) using (StoreE; get; set)
    renaming (deref to deref′; ref to ref′)

open import Effect.Call (Val) using (CallE; call)

itreeMonad : RawMonad (ITree′′ (StoreE ⊕ CallE))
itreeMonad = MonadITree′ (StoreE ⊕ CallE)

open RawMonad (itreeMonad)
open TraversableM (itreeMonad)

-- denote-top-level : TopLevel → ITree′′ NetworkE ⊤ 
-- denote-top-level (fn-def x x₁ x₂ x₃) = {!   !}
-- denote-top-level (fn-decl x x₁ x₂) = {!   !}
-- denote-top-level (global-def x x₁ x₂) = {!   !}

fromLiteral : Literal → PrimType → Val 
fromLiteral (ℓint x) (int-type false p) = val (x Int.modℕ (suc p)) p
fromLiteral (ℓint x) (int-type true p) = val Int.∣ x ∣ p

binop : (a b : Val) → Ops.Binop → Val
binop (val n p) (val m q) Ops.+ = val (n + m) (p ⊔ q)
binop (val n p) (val m q) Ops.- = 
    let k = p ⊔ q in val (n + ∣ suc k - (m % suc k) ∣) k
binop (val n p) (val m q) op = {!   !}


unop : (a : Val) → Ops.Unop → Val
unop (val 0 p) Ops.! = val 1 p 
unop (val _ p) Ops.! = val 0 p 
unop (val n p) Ops.~ = val (fromDigits $ lmap negate $ proj₁ $ toDigits 2 n) p 
    where
    negate : Bit → Bit 
    negate fzero = 1b 
    negate (fsuc fzero) = 0b
    
denote-expr : {t : Type} → Expr t → ITree′′ (StoreE ⊕ CallE) Val 
denote-expr {prim p} (lit x) = ret $ fromLiteral x p
denote-expr (e ⟨ o ⟩ f) = do
    v ← denote-expr e 
    w ← denote-expr f
    ret (binop v w o)
denote-expr (⟪ o ⟫ e) = do
    v ← denote-expr e 
    ret (unop v o)
denote-expr (var x) = trigger $ inj₁ $ get x
denote-expr (deref e) = trigger ∘ inj₁ ∘ deref′ =<< denote-expr e
denote-expr (ref e) = trigger ∘ inj₁ ∘ ref′ =<< denote-expr e 
denote-expr (e [ xs ]) = do
    v ← denote-expr e 
    vs ← denote-all xs 
    trigger $ inj₂ $ call v vs
    where
        denote-all : ∀ {xs} → All.All Expr xs → ITree′′ (StoreE ⊕ CallE) (List Val)
        denote-all All.[] = pure []
        denote-all (px All.∷ pxs) = do
            e ← denote-expr px
            es ← denote-all pxs 
            pure $ e ∷ es

