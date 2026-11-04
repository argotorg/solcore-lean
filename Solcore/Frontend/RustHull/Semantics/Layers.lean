import Solcore.Frontend.RustHull.Semantics.Memory
import Solcore.Frontend.RustHull.Semantics.World
import Solcore.Frontend.RustHull.Semantics.Digests
import Solcore.Frontend.RustHull.Semantics.Accounts

/-!
# Hull effect layers

The stacked runtime languages: memory and storage, then environment, logs, termination, copies,
hashing, accounts, code, return data and calls. Each layer adds its operations to the one below.
Main declarations: `RuntimeEffectsSemantics.State`, `RuntimeCallEffectsSemantics.State`.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeEffectsSemantics
/-! Independent memory and account-storage effects in one Hull state. The
source observations contain account data and mathematical memory words only. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeEffectsSemantics

structure State where
  memory : MemorySemantics.State := {}
  storage : StorageSemantics.State := {}
  deriving Repr

def builtin (name : String) (type : Ty) (arguments : List Semantics.Value)
    (state : State) : Option (Semantics.Result Semantics.Value × State) :=
  match MemorySemantics.builtin name type arguments state.memory with
  | some (result, memory) => some (result, {state with memory := memory})
  | none => (StorageSemantics.builtin name type arguments state.storage).map
      fun (result, storage) => (result, {state with storage := storage})

def effects : Semantics.ExternalSemantics State where
  builtin := fun name type arguments initial result final =>
    builtin name type arguments initial = some (result, final)
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.RuntimeEffectsSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.TerminationSemantics
/-! Independent message termination. A valid range expands memory, records the
exit and propagates the termination sentinel. An overflowing range faults before
any termination register changes; an empty range leaves memory size unchanged. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.TerminationSemantics
open Core

inductive Operation where
  | returned | reverted | stopped | invalid
  deriving DecidableEq, Repr

def Operation.name : Operation → String
  | .returned => "return" | .reverted => "revert" | .stopped => "stop" | .invalid => "invalid"

def Operation.kind : Operation → Nat
  | .returned | .stopped => 1 | .reverted => 2 | .invalid => 3

def Operation.arity : Operation → Nat
  | .returned | .reverted => 2 | .stopped | .invalid => 0

def terminate (state : RuntimeEffectsSemantics.State) (kind : Nat) (offset length : Word) :
    Semantics.Result Semantics.Value × RuntimeEffectsSemantics.State :=
  match MemorySemantics.touchSize? state.memory.size offset length with
  | none => (MemorySemantics.overflow, state)
  | some size => (.fault (.language Word.maximum), {
      memory := {state.memory with size := size}
      storage := {state.storage with exit := Word.ofNatModulo kind, returnOffset := offset, returnSize := length}})

def builtin (name : String) (_type : Ty) (arguments : List Semantics.Value)
    (state : RuntimeEffectsSemantics.State) :
    Option (Semantics.Result Semantics.Value × RuntimeEffectsSemantics.State) :=
  if name = "return" then
    match arguments with
    | [.word offset, .word length] => some (terminate state 1 offset length)
    | _ => none
  else if name = "revert" then
    match arguments with
    | [.word offset, .word length] => some (terminate state 2 offset length)
    | _ => none
  else if name = "stop" then
    match arguments with
    | [] => some (terminate state 1 Word.zero Word.zero)
    | _ => none
  else if name = "invalid" then
    match arguments with
    | [] => some (terminate state 3 Word.zero Word.zero)
    | _ => none
  else none

def effects : Semantics.ExternalSemantics RuntimeEffectsSemantics.State where
  builtin := fun name type arguments initial result final =>
    builtin name type arguments initial = some (result, final)
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.TerminationSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ReturnDataSemantics
/-! Return-data copying checks its complete source range before touching memory.
An invalid source range terminates the message even for a zero-length copy;
a valid range follows the ordinary packed-input copy and its destination faults. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ReturnDataSemantics
open Core

inductive Execute (entries : MemorySemantics.Entries) (size destination source length : Word) :
    RuntimeEffectsSemantics.State → Semantics.Result Semantics.Value → RuntimeEffectsSemantics.State → Prop where
  | sourceOverflow (initial : RuntimeEffectsSemantics.State) (invalid : source > size) :
      Execute entries size destination source length initial
        (TerminationSemantics.terminate initial 3 Word.zero Word.zero).1
        (TerminationSemantics.terminate initial 3 Word.zero Word.zero).2
  | lengthOverflow (initial : RuntimeEffectsSemantics.State)
      (sourceValid : ¬ source > size) (invalid : length > size.sub source) :
      Execute entries size destination source length initial
        (TerminationSemantics.terminate initial 3 Word.zero Word.zero).1
        (TerminationSemantics.terminate initial 3 Word.zero Word.zero).2
  | copied {initial : RuntimeEffectsSemantics.State} {memory : MemorySemantics.State}
      {result : Semantics.Result Semantics.Value}
      (sourceValid : ¬ source > size) (lengthValid : ¬ length > size.sub source)
      (executed : MemoryCopySemantics.From entries destination source length initial.memory result memory) :
      Execute entries size destination source length initial result {initial with memory := memory}

inductive Builtin (entries : MemorySemantics.Entries) (size : Word) : String → Ty → List Semantics.Value →
    RuntimeEffectsSemantics.State → Semantics.Result Semantics.Value → RuntimeEffectsSemantics.State → Prop where
  | copy {type : Ty} {destination source length : Word}
      {initial final : RuntimeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
      (executed : Execute entries size destination source length initial result final) :
      Builtin entries size "returndatacopy" type [.word destination, .word source, .word length] initial result final

theorem Builtin.named {entries : MemorySemantics.Entries} {size : Word} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : RuntimeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (called : Builtin entries size name type arguments initial result final) : name = "returndatacopy" := by
  cases called
  rfl

end Solcore.Frontend.RustHull.ReturnDataSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeEnvironmentEffectsSemantics
/-! Independent Hull effects with memory, account storage and immutable
message/block observations. An environment read leaves both state components
unchanged, including when optional information is unavailable. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeEnvironmentEffectsSemantics

structure State where
  runtime : RuntimeEffectsSemantics.State := {}
  environment : EnvironmentSemantics.State := {}

def builtin (name : String) (type : Ty) (arguments : List Semantics.Value)
    (state : State) : Option (Semantics.Result Semantics.Value × State) :=
  match RuntimeEffectsSemantics.builtin name type arguments state.runtime with
  | some (result, runtime) => some (result, {state with runtime := runtime})
  | none => (EnvironmentSemantics.builtin name type arguments state.environment).map
      fun (result, environment) => (result, {state with environment := environment})

def effects : Semantics.ExternalSemantics State where
  builtin := fun name type arguments initial result final =>
    builtin name type arguments initial = some (result, final)
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.RuntimeEnvironmentEffectsSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeLogEffectsSemantics
/-! Memory, storage, environment observations and event capture share one
runtime state. Only the event stream and cursor add new source state. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeLogEffectsSemantics

structure State where
  runtime : RuntimeEnvironmentEffectsSemantics.State := {}
  words : LogsSemantics.Words := []
  cursor : Core.Word := Core.Word.zero

def logsState (state : State) : LogsSemantics.State :=
  ⟨state.runtime.runtime.memory, state.words, state.cursor, state.runtime.runtime.storage.address,
    state.runtime.runtime.storage.isStatic, state.runtime.runtime.storage.exit,
    state.runtime.runtime.storage.returnOffset, state.runtime.runtime.storage.returnSize⟩

def withLogs (state : State) (logs : LogsSemantics.State) : State where
  runtime := {state.runtime with runtime := {
    memory := logs.memory
    storage := {state.runtime.runtime.storage with address := logs.address, isStatic := logs.isStatic, exit := logs.exit, returnOffset := logs.returnOffset, returnSize := logs.returnSize}}}
  words := logs.words
  cursor := logs.cursor

inductive Builtin : String → Ty → List Semantics.Value → State → Semantics.Result Semantics.Value → State → Prop where
  | runtime {name type arguments state result final}
      (computed : RuntimeEnvironmentEffectsSemantics.builtin name type arguments state.runtime = some (result, final)) :
      Builtin name type arguments state result {state with runtime := final}
  | logs {name type arguments state result final}
      (computed : LogsSemantics.Builtin name type arguments (logsState state) result final) :
      Builtin name type arguments state result (withLogs state final)

def effects : Semantics.ExternalSemantics State where
  builtin := Builtin
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.RuntimeLogEffectsSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeFullEffectsSemantics
/-! Explicit message termination joins event capture and existing runtime
operations without introducing another copy of the source state. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeFullEffectsSemantics

abbrev State := RuntimeLogEffectsSemantics.State

def withRuntime (state : State) (runtime : RuntimeEffectsSemantics.State) : State :=
  {state with runtime := {state.runtime with runtime := runtime}}

inductive Builtin : String → Ty → List Semantics.Value → State → Semantics.Result Semantics.Value → State → Prop where
  | runtime {name type arguments state result final}
      (computed : RuntimeLogEffectsSemantics.Builtin name type arguments state result final) :
      Builtin name type arguments state result final
  | termination {name type arguments state result final}
      (computed : TerminationSemantics.builtin name type arguments state.runtime.runtime = some (result, final)) :
      Builtin name type arguments state result (withRuntime state final)

def effects : Semantics.ExternalSemantics State where
  builtin := Builtin
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.RuntimeFullEffectsSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCopyEffectsSemantics
/-! Copy operations use the same memory and immutable calldata observations
as the surrounding source execution. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCopyEffectsSemantics

abbrev State := RuntimeFullEffectsSemantics.State

def withMemory (state : State) (memory : MemorySemantics.State) : State :=
  {state with runtime := {state.runtime with runtime := {state.runtime.runtime with memory := memory}}}

inductive Builtin : String → Ty → List Semantics.Value → State → Semantics.Result Semantics.Value → State → Prop where
  | runtime {name type arguments state result final}
      (computed : RuntimeFullEffectsSemantics.Builtin name type arguments state result final) :
      Builtin name type arguments state result final
  | copy {name type arguments state result final}
      (computed : MemoryCopySemantics.Builtin state.runtime.environment.calldata name type arguments
        state.runtime.runtime.memory result final) :
      Builtin name type arguments state result (withMemory state final)

def effects : Semantics.ExternalSemantics State where
  builtin := Builtin
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.RuntimeCopyEffectsSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeHashEffectsSemantics
/-! Hashing observes source memory and updates its touched extent while the
surrounding world, event stream and message observations remain available. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeHashEffectsSemantics

abbrev State := RuntimeCopyEffectsSemantics.State
abbrev withMemory := RuntimeCopyEffectsSemantics.withMemory

inductive Builtin : String → Ty → List Semantics.Value → State → Semantics.Result Semantics.Value → State → Prop where
  | runtime {name type arguments state result final}
      (computed : RuntimeCopyEffectsSemantics.Builtin name type arguments state result final) :
      Builtin name type arguments state result final
  | hash {name type arguments state result final}
      (computed : KeccakSemantics.Builtin name type arguments state.runtime.runtime.memory result final) :
      Builtin name type arguments state result (withMemory state final)

def effects : Semantics.ExternalSemantics State where
  builtin := Builtin
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.RuntimeHashEffectsSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeAccountEffectsSemantics
/-! Account observations share the running memory, world and message context.
The independent balance ledger records the existing runtime balance cell. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeAccountEffectsSemantics

structure State where
  runtime : RuntimeHashEffectsSemantics.State := {}
  balances : StorageSemantics.Words := []

def withMemory (state : State) (memory : MemorySemantics.State) : State :=
  {state with runtime := RuntimeCopyEffectsSemantics.withMemory state.runtime memory}

inductive Builtin : String → Ty → List Semantics.Value → State → Semantics.Result Semantics.Value → State → Prop where
  | runtime {name type arguments state result final}
      (computed : RuntimeHashEffectsSemantics.Builtin name type arguments state.runtime result final) :
      Builtin name type arguments state result {state with runtime := final}
  | observation {name type arguments state result final}
      (computed : AccountObservationSemantics.Builtin state.runtime.runtime.runtime.storage.world
        state.runtime.runtime.runtime.storage.complete state.balances state.runtime.runtime.runtime.storage.address
        name type arguments state.runtime.runtime.runtime.memory result final) :
      Builtin name type arguments state result (withMemory state final)

def effects : Semantics.ExternalSemantics State where
  builtin := Builtin
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.RuntimeAccountEffectsSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCodeEffectsSemantics
/-! A linked code image is fixed during a frame. Copying it updates the same
memory used by account observations and the other runtime operations. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCodeEffectsSemantics

abbrev State := RuntimeAccountEffectsSemantics.State

inductive Builtin (image : Option (List UInt8)) : String → Ty → List Semantics.Value →
    State → Semantics.Result Semantics.Value → State → Prop where
  | runtime {name : String} {type : Ty} {arguments : List Semantics.Value}
      {initial final : State} {result : Semantics.Result Semantics.Value}
      (computed : RuntimeAccountEffectsSemantics.Builtin name type arguments initial result final) :
      Builtin image name type arguments initial result final
  | copy {name : String} {type : Ty} {arguments : List Semantics.Value}
      {initial : State} {memory : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
      (computed : CodeImageSemantics.Builtin image name type arguments
        initial.runtime.runtime.runtime.memory result memory) :
      Builtin image name type arguments initial result (RuntimeAccountEffectsSemantics.withMemory initial memory)

def effects (image : Option (List UInt8)) : Semantics.ExternalSemantics State where
  builtin := Builtin image
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.RuntimeCodeEffectsSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeReturnDataEffectsSemantics
/-! Return data belongs to the caller frame. Its size is the existing message
observation, so copying and later calls share one source value for that size. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeReturnDataEffectsSemantics

structure State where
  runtime : RuntimeCodeEffectsSemantics.State := {}
  returnData : MemorySemantics.Entries := []

def size (state : State) : Core.Word :=
  state.runtime.runtime.runtime.environment.direct .returnDataSize

def withRuntime (state : State) (runtime : RuntimeEffectsSemantics.State) : State :=
  {state with runtime := {state.runtime with runtime := RuntimeFullEffectsSemantics.withRuntime state.runtime.runtime runtime}}

inductive Builtin (image : Option (List UInt8)) : String → Ty → List Semantics.Value →
    State → Semantics.Result Semantics.Value → State → Prop where
  | runtime {name type arguments state result final}
      (computed : RuntimeCodeEffectsSemantics.Builtin image name type arguments state.runtime result final) :
      Builtin image name type arguments state result {state with runtime := final}
  | copy {name type arguments state result final}
      (computed : ReturnDataSemantics.Builtin state.returnData (size state) name type arguments
        state.runtime.runtime.runtime.runtime result final) :
      Builtin image name type arguments state result (withRuntime state final)
  | guard {name type arguments state result}
      (computed : MemoryGuardSemantics.Builtin name type arguments result) :
      Builtin image name type arguments state result state

def effects (image : Option (List UInt8)) : Semantics.ExternalSemantics State where
  builtin := Builtin image
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

private theorem environment_builtin_unchanged {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : EnvironmentSemantics.State} {result : Semantics.Result Semantics.Value}
    (called : EnvironmentSemantics.builtin name type arguments initial = some (result, final)) : final = initial := by
  unfold EnvironmentSemantics.builtin at called
  cases selected : EnvironmentSemantics.operations.find? (fun operation => operation.name == name) with
  | none => simp [selected] at called
  | some operation =>
      cases observed : EnvironmentSemantics.observe initial operation arguments with
      | none => simp [selected, observed] at called
      | some value =>
          simp [selected, observed] at called
          exact called.2.symm

private theorem environment_unchanged {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : RuntimeEnvironmentEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (called : RuntimeEnvironmentEffectsSemantics.builtin name type arguments initial = some (result, final)) :
    final.environment = initial.environment := by
  unfold RuntimeEnvironmentEffectsSemantics.builtin at called
  split at called
  · cases Option.some.inj called
    rfl
  · cases observed : EnvironmentSemantics.builtin name type arguments initial.environment with
    | none => simp [observed] at called
    | some value =>
        rcases value with ⟨value, environment⟩
        simp only [observed, Option.map_some, Option.some.injEq, Prod.mk.injEq] at called
        rcases called with ⟨rfl, rfl⟩
        exact environment_builtin_unchanged observed

theorem runtime_environment {image : Option (List UInt8)} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : RuntimeCodeEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (called : RuntimeCodeEffectsSemantics.Builtin image name type arguments initial result final) :
    final.runtime.runtime.environment = initial.runtime.runtime.environment := by
  cases called with
  | copy _ => rfl
  | runtime called =>
      cases called with
      | observation _ => rfl
      | runtime called =>
          cases called with
          | hash _ => rfl
          | runtime called =>
              cases called with
              | copy _ => rfl
              | runtime called =>
                  cases called with
                  | termination _ => rfl
                  | runtime called =>
                      cases called with
                      | logs _ => rfl
                      | runtime called => exact environment_unchanged called

end Solcore.Frontend.RustHull.RuntimeReturnDataEffectsSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCallStateSemantics
/-! A caller adds its message depth to the established source state. Shared
account resources and frame-local return data are projections of that state,
so nested calls do not introduce duplicate memory, balance, or log fields. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics

structure State where
  runtime : RuntimeReturnDataEffectsSemantics.State := {}
  callDepth : Core.Word := Core.Word.zero

def shared (state : State) : AccountCallSemantics.Shared :=
  let runtime := state.runtime.runtime.runtime.runtime.runtime
  {world := runtime.storage.world, balances := state.runtime.runtime.balances
   logs := state.runtime.runtime.runtime.words, logSize := state.runtime.runtime.runtime.cursor
   complete := runtime.storage.complete}

def withShared (state : State) (shared : AccountCallSemantics.Shared) : State :=
  let account := state.runtime.runtime
  let logs := account.runtime
  let environment := logs.runtime
  let runtime := environment.runtime
  let updated := {runtime with storage := {runtime.storage with world := shared.world, complete := shared.complete}}
  let logs := {logs with runtime := {environment with runtime := updated}, words := shared.logs, cursor := shared.logSize}
  {state with runtime := {state.runtime with runtime := {account with runtime := logs, balances := shared.balances}}}

def withReturned (state : State) (memory : MemorySemantics.State)
    (data : MemorySemantics.Entries) (size : Core.Word) : State :=
  let account := state.runtime.runtime
  let logs := account.runtime
  let environment := logs.runtime
  let runtime := {environment.runtime with memory := memory}
  let observations := environment.environment
  let observations := {observations with direct := fun operation =>
    if operation = .returnDataSize then size else observations.direct operation}
  let logs := {logs with runtime := {environment with runtime := runtime, environment := observations}}
  {state with runtime := {runtime := {account with runtime := logs}, returnData := data}}

theorem shared_withShared (state : State) (value : AccountCallSemantics.Shared) : shared (withShared state value) = value := by
  cases value
  rfl

theorem shared_withReturned (state : State) (memory : MemorySemantics.State)
    (data : MemorySemantics.Entries) (size : Core.Word) : shared (withReturned state memory data size) = shared state := rfl

end Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics
/-! Ordinary and static message calls compose account dispatch with caller
transport. Child execution is an explicit source relation; the first public
instance uses noChildren, and finite call trees can supply recursively checked
source frames without changing the Hull expression rules. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics
open Core

inductive Operation where
  | ordinary | staticCall
  deriving DecidableEq, BEq, Repr

def Operation.name : Operation → String
  | .ordinary => "call" | .staticCall => "staticcall"

def transport (state : State) : CallTransportSemantics.State :=
  ⟨state.runtime.runtime.runtime.runtime.runtime.memory, state.runtime.returnData,
    RuntimeReturnDataEffectsSemantics.size state.runtime⟩

def withTransport (state : State) (next : CallTransportSemantics.State)
    (shared : AccountCallSemantics.Shared) : State :=
  withReturned (withShared state shared) next.memory next.returnData next.returnDataSize

def arguments (operation : Operation) (state : State)
    (gas target value inputOffset inputLength outputOffset outputLength : Word) : CallTransportSemantics.Arguments :=
  let runtime := state.runtime.runtime.runtime.runtime.runtime
  {caller := runtime.storage.address, depth := state.callDepth
   isStatic := if operation = .staticCall then true else runtime.storage.isStatic
   gas := if operation = .ordinary ∧ value ≠ Word.zero then gas.add (Word.ofNatModulo 2300) else gas
   target := target, value := value, inputOffset := inputOffset, inputLength := inputLength
   outputOffset := outputOffset, outputLength := outputLength}

def invalid (state : State) : Semantics.Result Semantics.Value × State :=
  let stopped := TerminationSemantics.terminate state.runtime.runtime.runtime.runtime.runtime 3 Word.zero Word.zero
  (stopped.1, {state with runtime := RuntimeReturnDataEffectsSemantics.withRuntime state.runtime stopped.2})

inductive Call (children : State → AccountCallSemantics.Children) (operation : Operation)
    (gas target value inputOffset inputLength outputOffset outputLength : Word) :
    State → Semantics.Result Semantics.Value → State → Prop where
  | staticValue (state : State)
      (ordinary : operation = .ordinary)
      (isStatic : state.runtime.runtime.runtime.runtime.runtime.storage.isStatic = true)
      (nonzero : value ≠ Word.zero) :
      Call children operation gas target value inputOffset inputLength outputOffset outputLength
        state (invalid state).1 (invalid state).2
  | gasOverflow (state : State)
      (ordinary : operation = .ordinary)
      (notStatic : state.runtime.runtime.runtime.runtime.runtime.storage.isStatic = false)
      (nonzero : value ≠ Word.zero)
      (overflow : gas > Word.ofNatModulo (wordModulus - 2301)) :
      Call children operation gas target value inputOffset inputLength outputOffset outputLength
        state (.fault (.language (Word.ofNatModulo 13))) state
  | invoked {state : State} {next : CallTransportSemantics.State} {nextShared : AccountCallSemantics.Shared}
      {result : Semantics.Result Semantics.Value}
      (permitted : operation = .staticCall ∨ value = Word.zero ∨
        state.runtime.runtime.runtime.runtime.runtime.storage.isStatic = false)
      (stipend : operation = .ordinary → value ≠ Word.zero →
        ¬gas > Word.ofNatModulo (wordModulus - 2301))
      (executed : CallTransportSemantics.Execute
        (AccountCallSemantics.Dispatch (children state) .ordinary state.runtime.runtime.runtime.runtime.runtime.storage.address)
        true (arguments operation state gas target value inputOffset inputLength outputOffset outputLength)
        (transport state) (shared state) result next nextShared) :
      Call children operation gas target value inputOffset inputLength outputOffset outputLength
        state result (withTransport state next nextShared)

inductive Builtin (children : State → AccountCallSemantics.Children) (image : Option (List UInt8)) :
    String → Ty → List Semantics.Value → State → Semantics.Result Semantics.Value → State → Prop where
  | runtime {name type arguments state result final}
      (computed : RuntimeReturnDataEffectsSemantics.Builtin image name type arguments state.runtime result final) :
      Builtin children image name type arguments state result {state with runtime := final}
  | call {type state result final gas target value inputOffset inputLength outputOffset outputLength}
      (computed : Call children .ordinary gas target value inputOffset inputLength outputOffset outputLength state result final) :
      Builtin children image "call" type [.word gas, .word target, .word value, .word inputOffset,
        .word inputLength, .word outputOffset, .word outputLength] state result final
  | staticCall {type state result final gas target inputOffset inputLength outputOffset outputLength}
      (computed : Call children .staticCall gas target Word.zero inputOffset inputLength outputOffset outputLength state result final) :
      Builtin children image "staticcall" type [.word gas, .word target, .word inputOffset,
        .word inputLength, .word outputOffset, .word outputLength] state result final

def effectsWith (children : State → AccountCallSemantics.Children) (image : Option (List UInt8)) :
    Semantics.ExternalSemantics State where
  builtin := Builtin children image
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

/-- Height zero permits local account outcomes, including an empty-account
call, while ruling out execution of another Hull frame. -/
def effects (image : Option (List UInt8)) : Semantics.ExternalSemantics State :=
  effectsWith (fun _ => AccountCallSemantics.noChildren) image

theorem runtime_balances {image : Option (List UInt8)} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : RuntimeReturnDataEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (called : RuntimeReturnDataEffectsSemantics.Builtin image name type arguments initial result final) :
    final.runtime.balances = initial.runtime.balances := by
  cases called with
  | guard _ => rfl
  | copy _ => rfl
  | runtime called =>
      cases called with
      | copy _ => rfl
      | runtime called =>
          cases called <;> rfl

end Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeControlEffectsSemantics
/-! Independent memory, storage, and message termination share the same source
state. Termination changes the memory size and message exit registers together. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeControlEffectsSemantics

abbrev State := RuntimeEffectsSemantics.State

def builtin (name : String) (type : Ty) (arguments : List Semantics.Value)
    (state : State) : Option (Semantics.Result Semantics.Value × State) :=
  match RuntimeEffectsSemantics.builtin name type arguments state with
  | some output => some output
  | none => TerminationSemantics.builtin name type arguments state

def effects : Semantics.ExternalSemantics State where
  builtin := fun name type arguments initial result final =>
    builtin name type arguments initial = some (result, final)
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.RuntimeControlEffectsSemantics
end
