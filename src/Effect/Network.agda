module Effect.Network where

open import Data.ITree  
open import Data.List
open import Data.Fin
open import Data.Nat
open import Data.Unit
open import Data.String
open import Data.Maybe

Socket Context Addr Mux Sec Typ : Set
Socket = ℕ 
Context = ℕ 
Addr = ℕ 
Mux = ℕ
Sec = ℕ
Typ = ℕ

data SocketType : Set where 
    pub sub : SocketType

record Tag : Set where
    field
        mux : Mux
        sec : Sec
        typ : Typ

data Command : Set where
    set-addr : Addr → Command   
    register : (encode decode : List (Fin 256) → List (Fin 256)) → Typ → Command
    new-ctx : Command  
    socket : Context → SocketType → Command 
    send : Socket → List (Fin 256) → Tag → Command
    recv : Socket → Command 

Result : Command → Set
Result (recv _) = Maybe (List (Fin 256))
Result (socket _ _) = Socket 
Result new-ctx = Context 
Result _ = ⊤

NetworkE : Effect
NetworkE = record { Command = Command ; Result = Result } 