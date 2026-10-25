import Solcore.Frontend.RustHull.AccountState
import Solcore.Frontend.RustHull.Semantics

/-! Account storage observations independent of lowering and machine execution.
Executable code identities belong to the representation and do not occur here. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.StorageSemantics
open Core

abbrev World := List AccountState.Account
abbrev Words := List (Word × Word)

def readWord (key : Word) : Words → Word
  | [] => Word.zero
  | (stored, value) :: rest => if key == stored then value else readWord key rest

def writeWord (key value : Word) : Words → Words
  | [] => [(key, value)]
  | (stored, old) :: rest =>
      if key == stored then (key, value) :: rest else (stored, old) :: writeWord key value rest

def lookup (address : Word) : World → Option AccountState.Account
  | [] => none
  | account :: rest => if address == account.address then some account else lookup address rest

def put (address : Word) (account : AccountState.Account) : World → World
  | [] => [{account with address := address}]
  | head :: rest => if address == head.address then {account with address := address} :: rest
      else head :: put address account rest

def get (world : World) (address : Word) (complete : Bool) : Except Word AccountState.Account :=
  match lookup address world with
  | some account => .ok account
  | none => if complete then .ok {address := address} else .error (Word.ofNatModulo 7)

def storage (account : AccountState.Account) (transient : Bool) : Words :=
  if transient then account.transient else account.storage

def update (account : AccountState.Account) (transient : Bool) (key value : Word) : AccountState.Account :=
  if transient then {account with transient := writeWord key value account.transient}
  else {account with storage := writeWord key value account.storage}

def readStorage (world : World) (address : Word) (complete : Bool) (key : Word)
    (transient : Bool := false) : Except Word Word := do
  return readWord key (storage (← get world address complete) transient)

def writeStorage (world : World) (address : Word) (complete : Bool) (key value : Word)
    (transient : Bool := false) : Except Word World := do
  let account ← get world address complete
  return put address (update account transient key value) world

def clearTransaction (account : AccountState.Account) : AccountState.Account :=
  {account with transient := [], created := false, destroyed := false}

def finalize : World → Words → World × Words
  | [], balances => ([], balances)
  | account :: rest, balances =>
      if account.created && account.destroyed then
        finalize rest (writeWord account.address Word.zero balances)
      else
        let (world, balances) := finalize rest balances
        (clearTransaction account :: world, balances)


structure State where
  world : World := []
  address : Word := Word.zero
  complete : Bool := false
  isStatic : Bool := false
  exit : Word := Word.zero
  returnOffset : Word := Word.zero
  returnSize : Word := Word.zero
  deriving Repr

def load (state : State) (key : Word) (transient : Bool) : Semantics.Result Semantics.Value × State :=
  match readStorage state.world state.address state.complete key transient with
  | .ok value => (.value (.word value), state)
  | .error reason => (.fault (.language reason), state)

def store (state : State) (key value : Word) (transient : Bool) : Semantics.Result Semantics.Value × State :=
  if state.isStatic then
    (.fault (.language Word.maximum), {state with
      exit := Word.ofNatModulo 3
      returnOffset := Word.zero
      returnSize := Word.zero})
  else
    match writeStorage state.world state.address state.complete key value transient with
    | .ok world => (.value .unit, {state with world := world})
    | .error reason => (.fault (.language reason), state)

def builtin (name : String) (_type : Ty) (arguments : List Semantics.Value)
    (state : State) : Option (Semantics.Result Semantics.Value × State) :=
  match name, arguments with
  | "sload", [.word key] => some (load state key false)
  | "tload", [.word key] => some (load state key true)
  | "sstore", [.word key, .word value] => some (store state key value false)
  | "tstore", [.word key, .word value] => some (store state key value true)
  | _, _ => none

def effects : Semantics.ExternalSemantics State where
  builtin := fun name type arguments initial result final =>
    builtin name type arguments initial = some (result, final)
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.StorageSemantics
