module Category.MonadSuc where

open import Level
private
    variable
        f : Level

record MonadSuc (M : Set f → Set (suc f)) : Set (suc f) where
    field
        _>>=_ : {A B : Set f} → M A → (A → M B) → M B 
        return : {A : Set f} → A → M A 

    _>>_ : {A B : Set f} → M A → M B → M B 
    a >> b = a >>= λ _ → b  