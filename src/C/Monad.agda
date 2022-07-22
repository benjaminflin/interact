module C.Monad where

open import Data.Nat 
open import Data.Integer using (ℤ) 
open import Data.List
open import Data.Fin using (Fin)
open import Data.Product 
open import Data.Sum 
open import Data.Unit hiding (_≟_)
open import Data.Maybe hiding (_>>=_)
import Level 
open Level hiding (suc; zero) 
open import Function
open import Data.Bool hiding (_≟_) 
open import Relation.Nullary using (does)
open import Category.Monad
open import Category.Monad.State

private 
    variable
        i f : Level
        M : Set → Set
        A : Set 

data CVal : Set where
    byte : Fin 256 → CVal 
    ptr : (stack : Bool) → (addr : ℕ) → (off : ℕ) → CVal   

record CState : Set where 
    constructor mk-cstate
    field
        heap-count : ℕ -- monotonically increases throughout execution
        heap : List (ℕ × List (Maybe CVal)) -- heap stores addresses
        stack : List (List (Maybe CVal)) -- stack addressed by index  

data CErr : Set where 
    out-of-bounds : ℕ → CErr 
    not-allocated : ℕ → CErr
    not-in-stack : ℕ → CErr   
    uninit : ℕ → ℕ → CErr    
    not-a-ptr : CVal → CErr   


open import Data.Sum.Categorical.Left (CErr) (Level.zero) hiding (monad)

CRun : (Set → Set) → Set → Set  
CRun M = StateT CState (M ∘ Sumₗ)

open CState

emptyState : CState 
emptyState = mk-cstate 0 [] []

CRunMonadState : RawMonad M → RawMonadState CState (CRun M)
CRunMonadState = StateTMonadState CState ∘ monadT

module CRun {M : Set → Set} (m : RawMonad M) where

    throw : CErr → CRun M A
    throw e _ = return (inj₁ e)
        where open RawMonad m 

    withState : CState → A → CRun M A
    withState cs x _ = return (inj₂ (x , cs))
        where open RawMonad m

    -- puts get/set and monad ops in scope
    open RawIMonadState (CRunMonadState m) public

    runC : CState → CRun M A → M (Sumₗ (A × CState))
    runC cs cr = cr cs   

    malloc : ℕ → CRun M CVal 
    malloc n = do
        cs ← get
        withState (newState cs) $ ptr false (heap-count cs) 0
        where
        newState : CState → CState  
        newState cs = record cs { 
            heap = (heap-count cs , replicate n nothing) ∷ heap cs;
            heap-count = 1 + heap-count cs } 


    -- free' : ℕ → CRun M ⊤  
    -- free' addr = do
    --     cs ← get 
    --     nh ← newHeap (heap cs)
    --     put $ record cs { heap = nh }
    --     where
    --     newHeap : List (ℕ × List (Maybe CVal)) → CRun M (List (ℕ × List (Maybe CVal)))
    --     newHeap [] = throw (not-allocated addr)
    --     newHeap ((addr' , vals) ∷ xs) with does (addr ≟ addr') 
    --     ... | true = return xs 
    --     ... | false = ((addr' , vals) ∷_) <$> newHeap xs 

-- free : CVal → CM m ⊤     
-- free (ptr false x _) = free' x
-- free (ptr true x _) = throw (not-allocated x)
-- free x = throw (not-a-ptr x)

-- maybeLookup : {a : Set} → ℕ → List a → Maybe a 
-- maybeLookup n [] = nothing  
-- maybeLookup (suc n) (x ∷ xs) = maybeLookup n xs 
-- maybeLookup zero (x ∷ xs) = just x  

-- get : CVal → CM m CVal
-- get (ptr true addr off) = do
--     cs ← getState 
--     getFromStack (stack cs)
--     where
--     getFromStack : List (List (Maybe CVal)) → CM m CVal 
--     getFromStack st with maybeLookup addr st 
--     ... | nothing = throw (not-in-stack addr) 
--     ... | just xs with maybeLookup off xs 
--     ... | just (just x) = return x
--     ... | just nothing = throw $ uninit addr off
--     ... | nothing = throw $ out-of-bounds off
-- get (ptr false addr off) = do
--     cs ← getState
--     getFromHeap (heap cs) 
--     where
--     getFromHeap : List (ℕ × List (Maybe CVal)) → CM m CVal 
--     getFromHeap [] = throw (not-allocated addr)
--     getFromHeap ((addr' , xs) ∷ hp) with does (addr ≟ addr')
--     ... | false = getFromHeap hp  
--     ... | true with maybeLookup off xs
--     ... | just (just x) = return x
--     ... | just nothing = throw $ uninit addr off 
--     ... | nothing = throw $ out-of-bounds off 
-- get x = throw (not-a-ptr x)

