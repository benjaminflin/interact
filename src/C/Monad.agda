open import Category.MonadSuc 
module C.Monad {m : Set → Set₁} (ms : MonadSuc m) where

open import Data.Nat 
open import Data.Integer using (ℤ) 
open import Data.List
open import Data.Product 
open import Data.Sum 
open import Data.Unit 
open import Data.Maybe hiding (_>>=_)
open import Level hiding (suc; zero)
open import Function


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
    ptr : ℕ → CVal   

record CState : Set where 
    field
        heap-count : ℕ -- monotonically increases throughout execution
        heap : List (ℕ × Maybe CVal) 
        heap-alloc-rec : List (ℕ × ℕ) 
        stack : List (Maybe CVal)

data CErr : Set where 
    out-of-bounds : ℕ → CErr 

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
open MonadSuc ms

malloc : ℕ → CM m CVal 
malloc n cs = 
    return (inj₂ (cs' , ptr (heap-count cs)))
    where
    heap' : ℕ → List (ℕ × Maybe CVal) 
    heap' zero = heap cs 
    heap' (suc k) = (k + (heap-count cs) , nothing) ∷ heap' k   
    cs' = record cs { 
        heap-count = n + heap-count cs; 
        heap-alloc-rec = (heap-count cs , n) ∷ heap-alloc-rec cs;
        heap = heap' n } 

free : ℕ → CM m ⊤  
free n cs = return {!   !} 
