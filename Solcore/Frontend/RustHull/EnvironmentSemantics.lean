import Solcore.Frontend.RustHull.MemorySemantics

/-! Immutable message, transaction and block observations for independent Hull
execution. Missing optional information remains distinct from a supplied zero. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.EnvironmentSemantics
open Core

inductive Direct where
  | address | caller | callvalue | calldataSize | returnDataSize
  deriving DecidableEq, Repr

def Direct.name : Direct → String
  | .address => "address" | .caller => "caller" | .callvalue => "callvalue"
  | .calldataSize => "calldatasize" | .returnDataSize => "returndatasize"

def Direct.slot : Direct → String
  | .calldataSize => "calldataSize" | .returnDataSize => "returnDataSize"
  | operation => operation.name

inductive AmbientWord where
  | origin | gasprice | coinbase | timestamp | number | prevrandao
  | gaslimit | chainid | basefee | blobbasefee
  deriving DecidableEq, Repr

def AmbientWord.name : AmbientWord → String
  | .origin => "origin" | .gasprice => "gasprice" | .coinbase => "coinbase"
  | .timestamp => "timestamp" | .number => "number" | .prevrandao => "prevrandao"
  | .gaslimit => "gaslimit" | .chainid => "chainid" | .basefee => "basefee" | .blobbasefee => "blobbasefee"

def AmbientWord.isAddress : AmbientWord → Bool
  | .origin | .coinbase => true | _ => false

inductive Operation where
  | direct (operation : Direct) | ambient (operation : AmbientWord)
  | gas | codeSize | calldataLoad | blockHash | blobHash
  deriving DecidableEq, Repr

def Operation.name : Operation → String
  | .direct operation => operation.name | .ambient operation => operation.name
  | .gas => "gas" | .codeSize => "codesize" | .calldataLoad => "calldataload"
  | .blockHash => "blockhash" | .blobHash => "blobhash"

def Operation.arity : Operation → Nat
  | .calldataLoad | .blockHash | .blobHash => 1 | _ => 0

structure State where
  direct : Direct → Word := fun _ => Word.zero
  ambient : AmbientWord → Option Word := fun _ => none
  gas : Option Word := none
  codeSize : Word := Word.zero
  codeKnown : Bool := false
  calldata : MemorySemantics.Entries := []
  blockHashes : Option MemorySemantics.Entries := none
  blobHashes : Option MemorySemantics.Entries := none

def available (reason : Nat) : Option Word → Semantics.Result Semantics.Value
  | none => .fault (.language (Word.ofNatModulo reason))
  | some value => .value (.word value)

def address (value : Word) : Word := value.bitAnd (Word.ofNatModulo (2 ^ 160 - 1))

def ambientWord (state : State) (operation : AmbientWord) : Semantics.Result Semantics.Value :=
  available 14 ((state.ambient operation).map fun value => if operation.isAddress then address value else value)

def blockHash (state : State) (index : Word) : Semantics.Result Semantics.Value :=
  match state.ambient .number, state.blockHashes with
  | some current, some hashes =>
      .value (.word (if current > index then
        if current.sub index > Word.ofNatModulo 256 then Word.zero else MemorySemantics.lookup index hashes
        else Word.zero))
  | _, _ => .fault (.language (Word.ofNatModulo 14))

def blobHash (state : State) (index : Word) : Semantics.Result Semantics.Value :=
  available 14 (state.blobHashes.map (MemorySemantics.lookup index))

def observe (state : State) (operation : Operation) (arguments : List Semantics.Value) :
    Option (Semantics.Result Semantics.Value) :=
  match operation, arguments with
  | .direct operation, [] => some (.value (.word (state.direct operation)))
  | .ambient operation, [] => some (ambientWord state operation)
  | .gas, [] => some (available 9 state.gas)
  | .codeSize, [] => some (if state.codeKnown then .value (.word state.codeSize)
      else .fault (.language (Word.ofNatModulo 15)))
  | .calldataLoad, [.word index] => some (.value (.word (MemorySemantics.readWord state.calldata index)))
  | .blockHash, [.word index] => some (blockHash state index)
  | .blobHash, [.word index] => some (blobHash state index)
  | _, _ => none

def operations : List Operation :=
  [.direct .address, .direct .caller, .direct .callvalue, .direct .calldataSize, .direct .returnDataSize,
    .ambient .origin, .ambient .gasprice, .ambient .coinbase, .ambient .timestamp,
    .ambient .number, .ambient .prevrandao, .ambient .gaslimit, .ambient .chainid,
    .ambient .basefee, .ambient .blobbasefee, .gas, .codeSize, .calldataLoad, .blockHash, .blobHash]

def builtin (name : String) (_type : Ty) (arguments : List Semantics.Value)
    (state : State) : Option (Semantics.Result Semantics.Value × State) := do
  let operation ← operations.find? (fun operation => operation.name == name)
  let result ← observe state operation arguments
  some (result, state)

def effects : Semantics.ExternalSemantics State where
  builtin := fun name type arguments initial result final =>
    builtin name type arguments initial = some (result, final)
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.EnvironmentSemantics
