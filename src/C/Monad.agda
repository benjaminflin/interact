module C.Monad where

open import Data.Nat 
open import Data.Integer using (ℤ) 
open import Data.List hiding (mapMaybe; lookup)
open import Data.Fin using (Fin)
open import Data.Product 
open import Data.Sum 
open import Data.Unit hiding (_≟_)
import Data.Maybe as Maybe
open Maybe hiding (_>>=_)
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

Addr Offset : Set
Addr = ℕ
Offset = ℕ

data CVal : Set where
    byte : Fin 256 → CVal 
    ptr : (stack : Bool) → (addr : Addr) → (off : Offset) → CVal   

record CState : Set where 
    constructor mk-cstate
    field
        heap-count : ℕ -- monotonically increases throughout execution
        heap : List (ℕ × List (Maybe CVal)) -- heap stores addresses
        stack : List (List (Maybe CVal)) -- stack addressed by index  

data CErr : Set where 
    out-of-bounds : Offset → CErr 
    not-allocated : Addr → CErr
    not-in-stack : Addr → CErr   
    uninit : Addr → Offset → CErr    
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
    open RawIMonadState (CRunMonadState m) renaming (modify to change) public

    runC : CState → CRun M A → M (Sumₗ (A × CState))
    runC cs cr = cr cs   

    put′ : CState → CRun M ⊤ 
    put′ c = put c >> return tt 

    malloc : ℕ → CRun M CVal 
    malloc n = do
        cs ← get
        withState (newState cs) $ ptr false (heap-count cs) 0
        where
        newState : CState → CState  
        newState cs = record cs { 
            heap = (heap-count cs , replicate n nothing) ∷ heap cs;
            heap-count = 1 + heap-count cs } 

    free' : ℕ → CRun M ⊤ 
    free' addr = do
        cs ← get 
        nh ← newHeap (heap cs)
        put′ record cs { heap = nh }
        where
        newHeap : List (ℕ × List (Maybe CVal)) → CRun M (List (ℕ × List (Maybe CVal)))
        newHeap [] = throw (not-allocated addr)
        newHeap ((addr' , vals) ∷ xs) with does (addr ≟ addr') 
        ... | true = return xs 
        ... | false = ((addr' , vals) ∷_) <$> newHeap xs 

    free : CVal → CRun M ⊤     
    free (ptr false x _) = free' x
    free (ptr true x _) = throw (not-allocated x)
    free x = throw (not-a-ptr x)

    maybeLookup : ℕ → List A → Maybe A
    maybeLookup n [] = nothing  
    maybeLookup (suc n) (x ∷ xs) = maybeLookup n xs 
    maybeLookup zero (x ∷ xs) = just x  

    maybeLookup′ : ℕ → List (ℕ × A) → Maybe A 
    maybeLookup′ n [] = nothing
    maybeLookup′ n ((m , v) ∷ xs) = if does (n ≟ m) then just v else maybeLookup′ n xs  

    maybeModify : ℕ → (A → A) → List A → Maybe (List A)
    maybeModify n f [] = nothing
    maybeModify zero f (x ∷ xs) = just (f x ∷ xs)
    maybeModify (suc n) f (x ∷ xs) = Maybe.map (x ∷_) (maybeModify n f xs)

    mapMaybe : CErr → Maybe A → CRun M A 
    mapMaybe e (just x) = return x
    mapMaybe e nothing = throw e

    lookup : CErr → ℕ → List A → CRun M A     
    lookup e n = mapMaybe e ∘ maybeLookup n 

    lookup′ : CErr → ℕ → List (ℕ × A) → CRun M A     
    lookup′ e n = mapMaybe e ∘ maybeLookup′ n 

    modify : CRun M (List A) → ℕ → (A → CRun M A) → List A → CRun M (List A) 
    modify e n f [] = e
    modify e zero f (x ∷ xs) = (_∷ xs) <$> f x
    modify e (suc n) f (x ∷ xs) = (x ∷_) <$> modify e n f xs

    modify′ : CRun M (List (ℕ × A)) → ℕ → (A → CRun M A) → List (ℕ × A) → CRun M (List (ℕ × A))
    modify′ e n f [] = e
    modify′ e n f (x@(m , v) ∷ xs) = 
        if does (n ≟ m) then ((_∷ xs) ∘ (m ,_)) <$> f v else (x ∷_) <$> modify′ e n f xs

    deref : CVal → CRun M CVal
    deref (ptr true addr off) = getFromStack =<< stack <$> get 
        where
        getFromStack : List (List (Maybe CVal)) → CRun M CVal
        getFromStack = 
            mapMaybe (uninit addr off) 
            <=< lookup (out-of-bounds off) off 
            <=< lookup (not-in-stack addr) addr
    deref (ptr false addr off) = getFromHeap =<< heap <$> get  
        where
        getFromHeap : List (ℕ × List (Maybe CVal)) → CRun M CVal
        getFromHeap = 
            mapMaybe (uninit addr off) 
            <=< lookup (out-of-bounds off) off 
            <=< lookup′ (not-allocated addr) addr
    deref x = throw (not-a-ptr x)

    set′ : (stack : Bool) → (addr : ℕ) → (off : ℕ) → CVal → CRun M ⊤  
    set′ false addr off val = 
        setHeap
        =<< modifyHeap 
        =<< heap <$> get
        where

        setHeap : List (ℕ × List (Maybe CVal)) → CRun M ⊤   
        setHeap nh = do
            st ← get
            put′ record st { heap = nh } 

        modifyHeap : List (ℕ × List (Maybe CVal)) → CRun M $ List (ℕ × List (Maybe CVal))  
        modifyHeap = modify′ (throw $ not-allocated addr) addr 
            (modify (throw $ out-of-bounds off) off (const $ return $ just val))

    set′ true addr off val = 
        setStack
        =<< modifyStack 
        =<< stack <$> get
        where

        setStack : List (List (Maybe CVal)) → CRun M ⊤   
        setStack ns = do
            st ← get
            put′ record st { stack = ns } 

        modifyStack : List (List (Maybe CVal)) → CRun M $ List (List (Maybe CVal))  
        modifyStack = modify (throw $ not-in-stack addr) addr 
            (modify (throw $ out-of-bounds off) off (const $ return $ just val))
    
    setVal : CVal → CVal → CRun M ⊤  
    setVal (ptr stack addr off) v = set′ stack addr off v
    setVal x v = throw (not-a-ptr x)


