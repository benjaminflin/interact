{-# OPTIONS --guardedness --sized-types #-}
module C.AST (Var : Set) where

open import Data.Nat using (ℕ; _⊔_; NonZero; suc)
open import Data.Bool using (Bool; _∧_)
open import Data.Integer using (ℤ)
open import Data.Char using (Char)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe)
open import Data.Product using (_×_)
open import Data.Unit using (tt) 

data PrimType : Set where 
    int-type : (unsigned : Bool) → (p : ℕ) → PrimType


max : (p q : PrimType) → PrimType 
max (int-type u p) (int-type u' p') = int-type (u ∧ u') (p ⊔ p') 

data Type : Set where 
    prim : PrimType → Type  
    struct : List Type → Type   
    array : ℕ → Type → Type  
    ptr : Type → Type 
    void : Type
    fn : List Type → Type → Type   

data Literal : Set where
    ℓint : ℤ → Literal 

module Ops where
    data Binop : Set where
        + : Binop
        - : Binop
        * : Binop
        / : Binop
        % : Binop
        && : Binop
        || : Binop
        == : Binop
        <= : Binop
        < : Binop
        ^ : Binop
        & : Binop
        ∣ : Binop
        << : Binop
        >> : Binop

    data Unop : Set where
        ! : Unop
        ~ : Unop

private
    variable
        p q : PrimType
        t : Type
        ts : List Type

data Expr : Type → Set where  
    lit : Literal → Expr (prim p)
    _⟨_⟩_ : Expr (prim p) → Ops.Binop → Expr (prim q) → Expr (prim (max p q))
    ⟪_⟫_ : Ops.Unop → Expr (prim p) → Expr (prim p) 
    deref : Expr (ptr t) → Expr t
    ref : Expr t → Expr (ptr t)
    var : Var → Expr t
    _[_] : Expr (fn ts t) → All Expr ts → Expr t -- function call

data Stmt : Set where 
    expr : Expr t → Stmt  
    semi : Stmt → Stmt → Stmt 
    while : Expr (prim p) → Stmt → Stmt 
    continue break : Stmt 
    return : Maybe (Expr t) → Stmt  
    decl : Type → Var → Stmt   
    set : Var → Expr t → Stmt   
    ptr-set : Var → Expr t → Stmt   
    elif-chain : List (Expr t × Stmt) → Stmt → Stmt  

data TopLevel : Set where 
    fn-def : Type → Var → List (Type × Var) → Stmt → TopLevel 
    fn-decl : Type → Var → List (Type × Maybe Var) → TopLevel 
    global-def : Type → Var → Maybe (Expr t) → TopLevel 

