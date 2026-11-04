import Solcore.Frontend.RustHull.Semantics.World
import Solcore.Frontend.RustHull.Semantics.Memory
import Solcore.Frontend.RustHull.Semantics.Digests

/-!
# Hull account dispatch and call transport

Account dispatch with its checkpoint, and caller-frame transport. Main declarations:
`AccountCallSemantics.Request`, `AccountCallSemantics.Response`, `AccountCallSemantics.Shared`,
`AccountCallSemantics.Mode`, `CallTransportSemantics.State`.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.AccountCallSemantics
/-! Account dispatch and its checkpoint are independent of Core closures.
Requests carry the copied calldata of a child frame. The child relation is
instantiated by finite source call trees, while an absent account in a complete
world can return without executing a child frame. Precompiled accounts answer
from their request alone. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallSemantics
open Core

structure Request where
  target : Word
  caller : Word
  value : Word
  isStatic : Bool
  depth : Word
  gas : Word
  calldata : MemorySemantics.Entries
  calldataSize : Word
  deriving Repr

structure Response where
  success : Bool
  data : MemorySemantics.Entries
  size : Word
  deriving Repr

structure Shared where
  world : StorageSemantics.World := []
  balances : StorageSemantics.Words := []
  logs : MemorySemantics.Entries := []
  logSize : Word := Word.zero
  complete : Bool := false
  deriving Repr

inductive Mode where
  | ordinary | callCode | delegateCall
  deriving DecidableEq, BEq, Repr

def Mode.number : Mode → Nat
  | .ordinary => 0 | .callCode => 1 | .delegateCall => 2

def emptyResponse (success : Bool) : Response := ⟨success, [], Word.zero⟩

def isPrecompile (target : Word) : Bool :=
  target == Word.ofNatModulo 256 || (target > Word.zero && Word.ofNatModulo 5 > target)

/-- The caller's funds are checked before this transfer. The self-transfer and
zero-value cases leave the mathematical balance mapping unchanged. -/
def transfer (source target value : Word) (balances : StorageSemantics.Words) : Except Word StorageSemantics.Words :=
  if value == Word.zero then .ok balances
  else if source == target then .ok balances
  else
    let sourceBalance := StorageSemantics.readWord source balances
    let targetBalance := StorageSemantics.readWord target balances
    if targetBalance > Word.maximum.sub value then .error (Word.ofNatModulo 12)
    else .ok (StorageSemantics.writeWord target (targetBalance.add value)
      (StorageSemantics.writeWord source (sourceBalance.sub value) balances))

def transferFor (mode : Mode) (source : Word) (request : Request) (state : Shared) : Except Word Shared :=
  if mode == .ordinary then
    (transfer source request.target request.value state.balances).map fun balances => {state with balances := balances}
  else .ok state

abbrev Children := Mode → Word → Request → Shared → Semantics.Result Response → Shared → Prop

/-- A base charge plus a charge per started 32-byte input word, computed over
natural numbers so that neither the product nor the sum wraps. -/
def linearCost (base perWord : Nat) (length : Word) : Nat :=
  base + perWord * ((length.val + 31) / 32)

/-- Identity, at address 4, charges 15 gas plus 3 per started input word and
returns a byte copy of its complete input. SHA-256, at address 2, charges 60
gas plus 12 per started input word and returns the 32-byte digest of its
complete input. RIPEMD-160, at address 3, charges 600 gas plus 120 per started
input word and returns its 20-byte digest left-padded to 32 bytes. Forwarded
gas below the charge fails the call without return data. An input range beyond
addressable memory is a memory fault. Precompiled addresses without a rule here
have no source derivation. -/
inductive Precompile (request : Request) : Semantics.Result Response → Prop where
  | identityOverflow
      (identity : request.target = Word.ofNatModulo 4)
      (invalid : MemorySemantics.touchSize? Word.zero Word.zero request.calldataSize = none) :
      Precompile request (.fault (.language (Word.ofNatModulo 6)))
  | identityUnderfunded {size : Word}
      (identity : request.target = Word.ofNatModulo 4)
      (valid : MemorySemantics.touchSize? Word.zero Word.zero request.calldataSize = some size)
      (short : request.gas.val < linearCost 15 3 request.calldataSize) :
      Precompile request (.value (emptyResponse false))
  | identity {size : Word} {output : MemorySemantics.Entries}
      (identity : request.target = Word.ofNatModulo 4)
      (valid : MemorySemantics.touchSize? Word.zero Word.zero request.calldataSize = some size)
      (funded : linearCost 15 3 request.calldataSize ≤ request.gas.val)
      (copied : MemoryCopySemantics.Copy request.calldata Word.zero Word.zero request.calldataSize [] output) :
      Precompile request (.value ⟨true, output, request.calldataSize⟩)
  | sha256Overflow
      (sha256 : request.target = Word.ofNatModulo 2)
      (invalid : MemorySemantics.touchSize? Word.zero Word.zero request.calldataSize = none) :
      Precompile request (.fault (.language (Word.ofNatModulo 6)))
  | sha256Underfunded {size : Word}
      (sha256 : request.target = Word.ofNatModulo 2)
      (valid : MemorySemantics.touchSize? Word.zero Word.zero request.calldataSize = some size)
      (short : request.gas.val < linearCost 60 12 request.calldataSize) :
      Precompile request (.value (emptyResponse false))
  | sha256 {size digest : Word}
      (sha256 : request.target = Word.ofNatModulo 2)
      (valid : MemorySemantics.touchSize? Word.zero Word.zero request.calldataSize = some size)
      (funded : linearCost 60 12 request.calldataSize ≤ request.gas.val)
      (digested : Sha256Semantics.Digest request.calldata Word.zero request.calldataSize digest) :
      Precompile request (.value ⟨true, [(Word.zero, digest)], Word.ofNatModulo 32⟩)
  | ripemd160Overflow
      (ripemd160 : request.target = Word.ofNatModulo 3)
      (invalid : MemorySemantics.touchSize? Word.zero Word.zero request.calldataSize = none) :
      Precompile request (.fault (.language (Word.ofNatModulo 6)))
  | ripemd160Underfunded {size : Word}
      (ripemd160 : request.target = Word.ofNatModulo 3)
      (valid : MemorySemantics.touchSize? Word.zero Word.zero request.calldataSize = some size)
      (short : request.gas.val < linearCost 600 120 request.calldataSize) :
      Precompile request (.value (emptyResponse false))
  | ripemd160 {size digest : Word}
      (ripemd160 : request.target = Word.ofNatModulo 3)
      (valid : MemorySemantics.touchSize? Word.zero Word.zero request.calldataSize = some size)
      (funded : linearCost 600 120 request.calldataSize ≤ request.gas.val)
      (digested : Ripemd160Semantics.Digest request.calldata Word.zero request.calldataSize digest) :
      Precompile request (.value ⟨true, [(Word.zero, digest)], Word.ofNatModulo 32⟩)

theorem Precompile.precompiled {request : Request} {result : Semantics.Result Response}
    (computed : Precompile request result) : isPrecompile request.target = true := by
  cases computed with
  | identityOverflow identity | identityUnderfunded identity | identity identity => rw [identity]; decide
  | sha256Overflow sha256 | sha256Underfunded sha256 | sha256 sha256 => rw [sha256]; decide
  | ripemd160Overflow ripemd160 | ripemd160Underfunded ripemd160 | ripemd160 ripemd160 =>
    rw [ripemd160]; decide

/-- A child-free dispatch is justified by absence in the source world. This
also establishes that its real default record has executable identity zero;
no identity is inferred merely from empty bytecode. A precompiled account
neither executes account code nor changes shared state. -/
inductive Run (children : Children) (mode : Mode) (source : Word) (request : Request) :
    Shared → Semantics.Result Response → Shared → Prop where
  | precompile {state : Shared} {result : Semantics.Result Response}
      (executed : Precompile request result) :
      Run children mode source request state result state
  | empty {state : Shared}
      (ordinaryAccount : isPrecompile request.target = false)
      (absent : StorageSemantics.lookup request.target state.world = none)
      (complete : state.complete = true) :
      Run children mode source request state (.value (emptyResponse true)) state
  | unavailable {state : Shared}
      (ordinaryAccount : isPrecompile request.target = false)
      (absent : StorageSemantics.lookup request.target state.world = none)
      (incomplete : state.complete = false) :
      Run children mode source request state (.fault (.language (Word.ofNatModulo 7))) state
  | child {state result final}
      (executed : children mode source request state result final) :
      Run children mode source request state result final

/-- Shared state is restored after a false child response or a language fault.
The unsuccessful response still carries its revert bytes to the caller. -/
inductive Dispatch (children : Children) (mode : Mode) (source : Word) (request : Request) :
    Shared → Semantics.Result Response → Shared → Prop where
  | insufficient {state : Shared}
      (checked : mode ≠ .delegateCall)
      (shortfall : request.value > StorageSemantics.readWord source state.balances) :
      Dispatch children mode source request state (.value (emptyResponse false)) state
  | transferFault {state : Shared} {reason : Word}
      (funds : mode = .delegateCall ∨ ¬ request.value > StorageSemantics.readWord source state.balances)
      (failed : transferFor mode source request state = .error reason) :
      Dispatch children mode source request state (.fault (.language reason)) state
  | succeeded {state transferred final : Shared} {response : Response}
      (funds : mode = .delegateCall ∨ ¬ request.value > StorageSemantics.readWord source state.balances)
      (moved : transferFor mode source request state = .ok transferred)
      (executed : Run children mode source request transferred (.value response) final)
      (success : response.success = true) :
      Dispatch children mode source request state (.value response) final
  | refused {state transferred attempted : Shared} {response : Response}
      (funds : mode = .delegateCall ∨ ¬ request.value > StorageSemantics.readWord source state.balances)
      (moved : transferFor mode source request state = .ok transferred)
      (executed : Run children mode source request transferred (.value response) attempted)
      (failure : response.success = false) :
      Dispatch children mode source request state (.value response) state
  | fault {state transferred attempted : Shared} {fault : Semantics.Fault}
      (funds : mode = .delegateCall ∨ ¬ request.value > StorageSemantics.readWord source state.balances)
      (moved : transferFor mode source request state = .ok transferred)
      (executed : Run children mode source request transferred (.fault fault) attempted) :
      Dispatch children mode source request state (.fault fault) state

def noChildren : Children := fun _ _ _ _ _ _ => False

end Solcore.Frontend.RustHull.AccountCallSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CallTransportSemantics
/-! Caller-frame transport is independent of account dispatch. Memory ranges
are touched in order; return data is cleared before depth and handler checks.
The child receives a separate input snapshot, and its complete response remains
available even when only a prefix is copied into caller memory. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CallTransportSemantics
open Core

abbrev Request := AccountCallSemantics.Request
abbrev Response := AccountCallSemantics.Response

structure State where
  memory : MemorySemantics.State := {}
  returnData : MemorySemantics.Entries := []
  returnDataSize : Word := Word.zero

structure Arguments where
  caller : Word := Word.zero
  depth : Word := Word.zero
  isStatic : Bool := false
  gas : Word := Word.zero
  target : Word := Word.zero
  value : Word := Word.zero
  inputOffset : Word := Word.zero
  inputLength : Word := Word.zero
  outputOffset : Word := Word.zero
  outputLength : Word := Word.zero

def request (arguments : Arguments) (input : MemorySemantics.Entries) : Request := {
  target := arguments.target.bitAnd (Word.ofNatModulo (2 ^ 160 - 1))
  caller := arguments.caller.bitAnd (Word.ofNatModulo (2 ^ 160 - 1))
  value := arguments.value
  isStatic := arguments.isStatic
  depth := arguments.depth.add (Word.ofNatModulo 1)
  gas := arguments.gas
  calldata := input
  calldataSize := arguments.inputLength
}

def copiedLength (arguments : Arguments) (response : Response) : Word :=
  if response.size > arguments.outputLength then arguments.outputLength else response.size

def finishResult (response : Response) : Semantics.Result Semantics.Value → Semantics.Result Semantics.Value
  | .value _ => .value (.word (Word.ofNatModulo (if response.success then 1 else 0)))
  | .fault fault => .fault fault

def clear (state : State) : State := {state with returnData := [], returnDataSize := Word.zero}

def unavailable : Semantics.Result Semantics.Value := .fault (.language (Word.ofNatModulo 7))

inductive Dispatch {Shared : Type}
    (callback : Request → Shared → Semantics.Result Response → Shared → Prop)
    (available : Bool) (arguments : Arguments) :
    State → Shared → Semantics.Result Semantics.Value → State → Shared → Prop where
  | depth (initial : State) (shared : Shared) (exceeded : arguments.depth > Word.ofNatModulo 1023) :
      Dispatch callback available arguments initial shared (.value (.word Word.zero)) initial shared
  | unavailable {initial : State} {input : MemorySemantics.State} (shared : Shared)
      (allowed : ¬arguments.depth > Word.ofNatModulo 1023)
      (copied : MemoryCopySemantics.From initial.memory.words Word.zero arguments.inputOffset arguments.inputLength
        {} (.value .unit) input)
      (missing : available = false) :
      Dispatch callback available arguments initial shared unavailable initial shared
  | fault {initial : State} {input : MemorySemantics.State} {shared finalShared : Shared}
      {fault : Semantics.Fault}
      (allowed : ¬arguments.depth > Word.ofNatModulo 1023)
      (copied : MemoryCopySemantics.From initial.memory.words Word.zero arguments.inputOffset arguments.inputLength
        {} (.value .unit) input)
      (present : available = true)
      (called : callback (request arguments input.words) shared (.fault fault) finalShared) :
      Dispatch callback available arguments initial shared (.fault fault) initial finalShared
  | returned {initial : State} {input memory : MemorySemantics.State} {shared finalShared : Shared}
      {response : Response} {result : Semantics.Result Semantics.Value}
      (allowed : ¬arguments.depth > Word.ofNatModulo 1023)
      (copied : MemoryCopySemantics.From initial.memory.words Word.zero arguments.inputOffset arguments.inputLength
        {} (.value .unit) input)
      (present : available = true)
      (called : callback (request arguments input.words) shared (.value response) finalShared)
      (returned : MemoryCopySemantics.From response.data arguments.outputOffset Word.zero (copiedLength arguments response)
        initial.memory result memory) :
      Dispatch callback available arguments initial shared (finishResult response result)
        ⟨memory, response.data, response.size⟩ finalShared

inductive Execute {Shared : Type}
    (callback : Request → Shared → Semantics.Result Response → Shared → Prop)
    (available : Bool) (arguments : Arguments) :
    State → Shared → Semantics.Result Semantics.Value → State → Shared → Prop where
  | inputOverflow (initial : State) (shared : Shared)
      (invalid : MemorySemantics.touchSize? initial.memory.size arguments.inputOffset arguments.inputLength = none) :
      Execute callback available arguments initial shared MemorySemantics.overflow initial shared
  | outputOverflow (initial : State) (shared : Shared) {inputSize : Word}
      (input : MemorySemantics.touchSize? initial.memory.size arguments.inputOffset arguments.inputLength = some inputSize)
      (invalid : MemorySemantics.touchSize? inputSize arguments.outputOffset arguments.outputLength = none) :
      Execute callback available arguments initial shared MemorySemantics.overflow
        {initial with memory := {initial.memory with size := inputSize}} shared
  | ready {initial final : State} {shared finalShared : Shared} {inputSize outputSize : Word}
      {result : Semantics.Result Semantics.Value}
      (input : MemorySemantics.touchSize? initial.memory.size arguments.inputOffset arguments.inputLength = some inputSize)
      (output : MemorySemantics.touchSize? inputSize arguments.outputOffset arguments.outputLength = some outputSize)
      (dispatched : Dispatch callback available arguments
        (clear {initial with memory := {initial.memory with size := outputSize}}) shared result final finalShared) :
      Execute callback available arguments initial shared result final finalShared

end Solcore.Frontend.RustHull.CallTransportSemantics
end
