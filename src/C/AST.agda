module C.AST (Var : Set) where

open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)
open import Data.Char using (Char)
open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.Product using (_×_)

data PrimType : Set where 
    int8 : PrimType 
    int16 : PrimType 
    int32 : PrimType 
    int64 : PrimType 
    uint8 : PrimType 
    uint16 : PrimType 
    uint32 : PrimType 
    uint64 : PrimType 
    float : PrimType 
    double : PrimType 

data Type : Set where 
    prim : PrimType → Type  
    struct : List Type → Type   
    array : ℕ → Type → Type  
    ptr : Type → Type 
    fn : List Type → Maybe Type → Type   

data Literal : Set where
    ℓint : ℤ → Literal   
    ℓchar : Char → Literal   
    ℓstring : List Char → Literal   
    ℓdecimal : ℤ → ℕ → Literal   

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

data Expr : Set where  
    lit : Literal → Expr 
    _<_>_ : Expr → Binop → Expr → Expr 
    [_]_ : Unop → Expr → Expr 
    *_ : Expr → Expr  
    &_ : Expr → Expr  
    _[_] : Expr → List Expr → Expr -- function call

data Stmt : Set where 
    expr : Expr → Stmt  
    semi : Stmt → Stmt → Stmt 
    while : Expr → Stmt → Stmt 
    continue break : Stmt 
    return : Maybe Expr → Stmt  
    decl : Type → Var → Stmt   
    set : Var → Expr → Stmt   
    ptr-set : Var → Expr → Stmt   
    elif-chain : List (Expr × Stmt) → Stmt → Stmt  

data TopLevel : Set where 
    fn-def : Type → Var → List (Type × Var) → Stmt → TopLevel 
    fn-decl : Type → Var → List (Type × Maybe Var) → TopLevel 
    global-def : Type → Var → Maybe Expr → TopLevel 
