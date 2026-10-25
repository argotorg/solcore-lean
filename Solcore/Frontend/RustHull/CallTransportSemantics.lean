import Solcore.Frontend.RustHull.AccountCallSemantics
import Solcore.Frontend.RustHull.MemoryCopySemantics

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
