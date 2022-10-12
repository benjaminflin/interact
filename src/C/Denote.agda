{-# OPTIONS --guardedness --sized-types #-}
module C.Denote (Var : Set) where

open import Data.Unit
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Bool
open import Data.List 
open import Data.Sum 
open import Data.Product 
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
    val : (n : ℕ) → (p : ℕ) → (n ≡ n % (suc p)) → Val

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
fromLiteral (ℓint x) (int-type false p) = val (x Int.modℕ (suc p)) p {! !} 
fromLiteral (ℓint x) (int-type true p) = val (Int.∣ x ∣ % suc p) p (sym $ m%n%n≡m%n Int.∣ x ∣ p) 

binop : (a b : Val) → Ops.Binop → Val
binop a b op = {!   !}

unop : (a : Val) → Ops.Unop → Val
unop a op = {!   !}

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

