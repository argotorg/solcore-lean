import Solcore.Frontend.RustHull.StorageSemantics
import Solcore.Frontend.RustHull.MemoryCopySemantics
import Solcore.Frontend.RustHull.KeccakSemantics

/-! Account observations read the independent world and balance ledger.
Copying code changes caller memory; code hashing uses isolated scratch memory.
The byte packer is the shared pure representation function, without evaluation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountObservationSemantics
open Core

inductive Operation where
  | balance | selfbalance | size | copy | hash
  deriving DecidableEq, Repr

def Operation.name : Operation → String
  | .balance => "balance" | .selfbalance => "selfbalance"
  | .size => "extcodesize" | .copy => "extcodecopy" | .hash => "extcodehash"

def address (target : Word) : Word := target.bitAnd (Word.ofNatModulo (2 ^ 160 - 1))
def codeSize (bytes : List UInt8) : Word := Word.ofNatModulo bytes.length
abbrev packed := Memory.packBytes

def emptyAccount (account : AccountState.Account) (bytes : List UInt8) (balance : Word) : Bool :=
  if account.nonce == Word.zero then
    if codeSize bytes == Word.zero then balance == Word.zero else false
  else false

def failure (reason : Word) : Semantics.Result Semantics.Value := .fault (.language reason)
def unknownCode : Semantics.Result Semantics.Value := failure (Word.ofNatModulo 15)

inductive Builtin (world : StorageSemantics.World) (complete : Bool) (balances : StorageSemantics.Words)
    (current : Word) : String → Ty → List Semantics.Value →
    MemorySemantics.State → Semantics.Result Semantics.Value → MemorySemantics.State → Prop where
  | balance (type : Ty) (target : Word) (memory : MemorySemantics.State) :
      Builtin world complete balances current "balance" type [.word target] memory
        (.value (.word (StorageSemantics.readWord (address target) balances))) memory
  | selfbalance (type : Ty) (memory : MemorySemantics.State) :
      Builtin world complete balances current "selfbalance" type [] memory
        (.value (.word (StorageSemantics.readWord current balances))) memory
  | sizeFailure {type : Ty} {target reason : Word} {memory : MemorySemantics.State}
      (found : StorageSemantics.get world (address target) complete = .error reason) :
      Builtin world complete balances current "extcodesize" type [.word target] memory (failure reason) memory
  | sizeUnknown {type : Ty} {target : Word} {memory : MemorySemantics.State} {account : AccountState.Account}
      (found : StorageSemantics.get world (address target) complete = .ok account) (unknown : account.code = none) :
      Builtin world complete balances current "extcodesize" type [.word target] memory unknownCode memory
  | sizeKnown {type : Ty} {target : Word} {memory : MemorySemantics.State} {account : AccountState.Account} {bytes : List UInt8}
      (found : StorageSemantics.get world (address target) complete = .ok account) (known : account.code = some bytes) :
      Builtin world complete balances current "extcodesize" type [.word target] memory (.value (.word (codeSize bytes))) memory
  | copyFailure {type : Ty} {target destination source length reason : Word} {memory : MemorySemantics.State}
      (found : StorageSemantics.get world (address target) complete = .error reason) :
      Builtin world complete balances current "extcodecopy" type [.word target, .word destination, .word source, .word length]
        memory (failure reason) memory
  | copyUnknown {type : Ty} {target destination source length : Word} {memory : MemorySemantics.State} {account : AccountState.Account}
      (found : StorageSemantics.get world (address target) complete = .ok account) (unknown : account.code = none) :
      Builtin world complete balances current "extcodecopy" type [.word target, .word destination, .word source, .word length]
        memory unknownCode memory
  | copyKnown {type : Ty} {target destination source length : Word} {memory finalMemory : MemorySemantics.State}
      {account : AccountState.Account} {bytes : List UInt8} {result : Semantics.Result Semantics.Value}
      (found : StorageSemantics.get world (address target) complete = .ok account) (known : account.code = some bytes)
      (copied : MemoryCopySemantics.From (packed bytes) destination source length memory result finalMemory) :
      Builtin world complete balances current "extcodecopy" type [.word target, .word destination, .word source, .word length]
        memory result finalMemory
  | hashFailure {type : Ty} {target reason : Word} {memory : MemorySemantics.State}
      (found : StorageSemantics.get world (address target) complete = .error reason) :
      Builtin world complete balances current "extcodehash" type [.word target] memory (failure reason) memory
  | hashUnknown {type : Ty} {target : Word} {memory : MemorySemantics.State} {account : AccountState.Account}
      (found : StorageSemantics.get world (address target) complete = .ok account) (unknown : account.code = none) :
      Builtin world complete balances current "extcodehash" type [.word target] memory unknownCode memory
  | hashEmpty {type : Ty} {target : Word} {memory : MemorySemantics.State} {account : AccountState.Account} {bytes : List UInt8}
      (found : StorageSemantics.get world (address target) complete = .ok account) (known : account.code = some bytes)
      (empty : emptyAccount account bytes (StorageSemantics.readWord (address target) balances) = true) :
      Builtin world complete balances current "extcodehash" type [.word target] memory (.value (.word Word.zero)) memory
  | hashKnown {type : Ty} {target : Word} {memory scratchFinal : MemorySemantics.State}
      {account : AccountState.Account} {bytes : List UInt8} {result : Semantics.Result Semantics.Value}
      (found : StorageSemantics.get world (address target) complete = .ok account) (known : account.code = some bytes)
      (nonempty : emptyAccount account bytes (StorageSemantics.readWord (address target) balances) = false)
      (hashed : KeccakSemantics.Hash Word.zero (codeSize bytes) ⟨packed bytes, Word.zero⟩ result scratchFinal) :
      Builtin world complete balances current "extcodehash" type [.word target] memory result memory

theorem Builtin.named {world : StorageSemantics.World} {complete : Bool} {balances : StorageSemantics.Words}
    {current : Word} {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Builtin world complete balances current name type arguments initial result final) :
    ∃ operation : Operation, operation.name = name := by
  cases evaluated
  all_goals first
    | exact ⟨.balance, rfl⟩
    | exact ⟨.selfbalance, rfl⟩
    | exact ⟨.size, rfl⟩
    | exact ⟨.copy, rfl⟩
    | exact ⟨.hash, rfl⟩

end Solcore.Frontend.RustHull.AccountObservationSemantics
