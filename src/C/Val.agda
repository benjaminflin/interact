module C.Val where

open import Data.Nat
open import Data.Product
open import Data.List

Addr Offset : Set
Addr = ℕ × ℕ
Offset = ℕ

data Val : Set where
    bytes : ∀ (n : ℕ) → (p : ℕ) → Val
    seq : List Val → Val
    ptr : (addr : Addr) → (off : Offset) → Val   