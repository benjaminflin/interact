open import Category.MonadSuc 
module C.Monad {m : Set → Set₁} (ms : MonadSuc m) where

open import Data.Nat 
open import Data.Integer using (ℤ) 
open import Data.List
open import Data.Product 
open import Data.Sum 
open import Data.Unit hiding (_≟_)
open import Data.Maybe hiding (_>>=_)
open import Level hiding (suc; zero)
open import Function
open import Data.Bool using (if_then_else_; true; false)
open import Relation.Nullary using (does)


private 
    variable
        i f : Level

data IntSize : Set where
    Int8 : IntSize
    Int16 : IntSize
    Int32 : IntSize
    Int64 : IntSize

-- data CType : Set where
--     int-t : IntSize → (signed : Boolean) → CType 
--     ptr-t : CType → CType 

data CVal : Set where
    unsigned-int : IntSize → ℕ → CVal      
    int : IntSize → ℤ → CVal      
    ptr : ℕ → ℕ → CVal   

record CState : Set where 
    constructor mk-cstate
    field
        heap-count : ℕ -- monotonically increases throughout execution
        heap : List (ℕ × List (Maybe CVal)) 
        stack : List (Maybe CVal)

data CErr : Set where 
    out-of-bounds : ℕ → CErr 
    not-allocated : ℕ → CErr 
    not-a-ptr : CVal → CErr   

CM : (Set → Set₁) → Set → Set₁ 
CM m a = CState → m (CErr ⊎ (CState × a))

MonadSucCM : MonadSuc (CM m)
MonadSucCM = record { _>>=_ = _>>=_ ; return = return }
    where
    _>>=_ : {a b : Set} → CM m a → (a → CM m b) → CM m b 
    (x >>= f) cs = (MonadSuc._>>=_) ms (x cs) (λ where 
        (inj₁ e) → MonadSuc.return ms (inj₁ e) 
        (inj₂ (cs' , a)) → f a cs')
    
    return : {a : Set} → a → CM m a   
    return x cs = MonadSuc.return ms (inj₂ (cs , x))

open CState
open MonadSuc MonadSucCM

emptyState : CState 
emptyState = mk-cstate 0 [] []

throw : {a : Set} → CErr → CM m a     
throw e _ = MonadSuc.return ms $ inj₁ e

withState : {a : Set} → CState → a → CM m a 
withState cs x _ = MonadSuc.return ms $ inj₂ (cs , x)

setState : CState → CM m ⊤   
setState cs = withState cs tt 

getState : CM m CState
getState cs = MonadSuc.return ms (inj₂ (cs , cs))

runCM : {a : Set} → CState → CM m a → m (CErr ⊎ CState × a)  
runCM cs cm = cm cs

malloc : ℕ → CM m CVal 
malloc n = do
    cs ← getState
    withState (newState cs) $ ptr (heap-count cs) 0
    where
    newState : CState → CState  
    newState cs = record cs { 
        heap = (heap-count cs , replicate n nothing) ∷ heap cs;
        heap-count = 1 + heap-count cs } 

free' : ℕ → CM m ⊤  
free' addr = do
    cs ← getState 
    nh ← newHeap (heap cs)
    setState $ record cs { heap = nh }
    where
    newHeap : List (ℕ × List (Maybe CVal)) → CM m $ List (ℕ × List (Maybe CVal))
    newHeap [] = throw (not-allocated addr)
    newHeap ((addr' , vals) ∷ xs) with does (addr ≟ addr') 
    ... | true = return xs 
    ... | false = do
        nh ← newHeap xs 
        return $ (addr' , vals) ∷ nh


free : CVal → CM m ⊤     
free (ptr x _) = free' x
free x = throw (not-a-ptr x)


