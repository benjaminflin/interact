module Data.Binary where

import Data.Nat as Nat
import Data.Fin as Fin
open import Data.Nat.DivMod using (_%_; _/_; m%n<n)
open import Data.Nat.Properties using (m*n≡0⇒m≡0∨n≡0)
open import Data.Sum
open import Data.Digit hiding (0b; 1b)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Product
open import Relation.Binary.PropositionalEquality 
open import Function
import Data.Vec as Vec
import Data.List as List

open Nat using (ℕ; _^_)
open Fin using (Fin)
open Vec using (Vec; []; _∷_) 

open import Algebra

record Binary (size : ℕ) : Set where 
    constructor b
    field
        bytes : Vec (Fin 256) size

private
    variable
        n : ℕ

transportℕOp′ : Op₂ ℕ → Op₂ (Fin 256)
transportℕOp′ _·_ x y = Fin.fromℕ< (m%n<n (Fin.toℕ x · Fin.toℕ y) 255)

transportFinOp : Op₂ (Fin 256) → Op₂ (Binary n) 
transportFinOp _·_ (b xs) (b ys) = b (Vec.zipWith (_·_) xs ys)

_+_ : Op₂ (Binary n)
_+_ = transportFinOp (transportℕOp′ Nat._+_)

_*_ : Op₂ (Binary n)
_*_ = transportFinOp (transportℕOp′ Nat._*_)

pattern 0b = Fin.zero 
pattern 1b = Fin.suc Fin.zero 

xorDigit : Op₂ Bit 
xorDigit 0b 0b = 0b
xorDigit 1b 1b = 0b
xorDigit _ _ = 1b

andDigit : Op₂ Bit
andDigit 1b 1b = 1b
andDigit _ _ = 0b

orDigit : Op₂ Bit
orDigit 0b 0b = 0b
orDigit _ _ = 1b

expand′ : Fin 256 → Vec Bit 8
expand′ f = Vec.map (nth-bit (Fin.toℕ f) ∘ Fin.toℕ) (Vec.allFin 8)
    where
        2ⁿ≢0 : ∀ n → (2 ^ n) ≢ 0 
        2ⁿ≢0 Nat.zero = λ ()
        2ⁿ≢0 (Nat.suc n) pf with ih ← 2ⁿ≢0 n with (inj₂ x) ← m*n≡0⇒m≡0∨n≡0 2 {2 ^ n} pf = ih x

        nth-bit : ℕ → ℕ → Bit 
        nth-bit n k = Fin.fromℕ< (m%n<n (_/_ n (2 ^ k) {fromWitnessFalse (2ⁿ≢0 k)}) 1)

expand : Vec (Fin 256) n → Vec Bit (n Nat.* 8) 
expand xs = xs Vec.>>= expand′

contract′ : Vec Bit 8 → Fin 256  
contract′ xs = 
    Vec.foldr 
        (λ _ → Fin 256) 
        combine
        0b 
        (Vec.zip (Vec.map Fin.toℕ (Vec.allFin 8)) xs)
    where
        rshift : Bit → ℕ → ℕ
        rshift bit n = (Fin.toℕ bit) Nat.* (2 ^ n)

        combine : ℕ × Bit → Fin 256 → Fin 256  
        combine (n , bit) acc = Fin.fromℕ< $ m%n<n (Fin.toℕ acc Nat.+ rshift bit n) 255

contract : Vec Bit (n Nat.* 8) → Vec (Fin 256) n
contract {n} = Vec.map contract′ ∘ proj₁ ∘ Vec.group n 8 

expand′∘contract′≡id : ∀ xs → expand′ (contract′ xs) ≡ xs
expand′∘contract′≡id (0b ∷ 0b ∷ 0b ∷ 0b ∷ 0b ∷ 0b ∷ 0b ∷ 0b ∷ []) = refl
expand′∘contract′≡id (1b ∷ 1b ∷ 1b ∷ 0b ∷ 0b ∷ 0b ∷ 0b ∷ 0b ∷ []) = refl
expand′∘contract′≡id (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ x₇ ∷ []) = {!   !}

transportBitOp′ : Op₂ Bit → Op₂ (Fin 256)   
transportBitOp′ _·_ f₁ f₂ = contract′ $ Vec.zipWith (_·_) (expand′ f₁) (expand′ f₂)

_⊕_ : Op₂ (Binary n)  
_⊕_ = transportFinOp (transportBitOp′ xorDigit) 

_&_ : Op₂ (Binary n)  
_&_ = transportFinOp (transportBitOp′ andDigit) 

_∣_ : Op₂ (Binary n)
_∣_ = transportFinOp (transportBitOp′ orDigit) 

