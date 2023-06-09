module Control.Functor where

open import Level
open import Function.Base
open import Relation.Binary.PropositionalEquality

private
    variable
        a b : Level 
        A B : Set a
    
record Functor (F : Set a → Set b) : Set (suc a ⊔ b) where
    field
        map : (A → B) → F A → F B 

    _⟨$⟩_ : (A → B) → F A → F B 
    _⟨$⟩_ = map 


record LawfulFunctor (F : Set a → Set b) : Set (suc a ⊔ b) where
    field
        functor : Functor F 
    open Functor 
    field
        map-id : ∀ (x : F A) → map functor id x ≡ id x
        map-comp : ∀ {C : Set a} (f : A → B) (g : B → C) (x : F A) → map functor (g ∘ f) x ≡ (map functor g ∘ map functor f) x
