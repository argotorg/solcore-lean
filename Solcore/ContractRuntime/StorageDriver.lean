import Solcore.Core.Syntax
import Solcore.Core.HostMachine
import Solcore.ContractRuntime.RuntimeScalars
import Solcore.ContractRuntime.Internal.ScalarLaws
import Solcore.ContractRuntime.Frames
import Solcore.ContractRuntime.WorldState
import Solcore.ContractRuntime.Driver
import Solcore.Core.Machine
import Solcore.ContractRuntime.Internal.FrameLaws
import Solcore.Core.Host

/-!
# Storage-backed host handling

The handler that real contract execution uses. `HostStorageDriver.InputData` and
`HostStorageDriver.ExecutionInputs` are its immutable inputs, and `HostStorageDriver.Context` its
state. `HostStorageDriver.handleRequest` answers each request, and `HostStorageDriver.run` and
`CheckedHostCoreProgram.runWithStorage` run checked code. `ContractCallFailure` says why a call
could not start. `WordReturnedFrameCompletion` is a frame that returned a Word.
-/

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsContractCallFailure
/-! Internal failure reasons for dispatching one checked contract-word call. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- Failures that occur before a child contract produces a terminal outcome. -/
inductive ContractCallFailure where
  | invalidAddress
  | unavailable
  | depthExceeded
  | insufficientBalance
  | balanceOverflow
  | nonceOverflow
  | addressCollision
  deriving Repr, BEq, DecidableEq

namespace ContractCallFailure

/-- Stable internal code injected into the typed call-failure response branch. -/
def code : ContractCallFailure → Core.Word
  | .invalidAddress => ⟨0, by decide⟩
  | .unavailable => ⟨1, by decide⟩
  | .depthExceeded => ⟨2, by decide⟩
  | .insufficientBalance => ⟨3, by decide⟩
  | .balanceOverflow => ⟨4, by decide⟩
  | .nonceOverflow => ⟨5, by decide⟩
  | .addressCollision => ⟨6, by decide⟩

/-- Convert a dispatch failure into the dedicated Core call-result branch. -/
def result (failure : ContractCallFailure) : Core.ContractCallWordResult :=
  .failed failure.code

end ContractCallFailure

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsHostStorageInputData
/-! Bounded raw input bytes shared by one handled execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostStorageDriver

/-- Immutable input bytes whose exact length is representable by a Core Word. -/
structure InputData where
  bytes : Bytes
  size_lt_wordModulus : bytes.size < Core.wordModulus

namespace InputData

/-- Exact byte length, represented without truncation as a Core Word. -/
def sizeWord (input : InputData) : Core.Word :=
  ⟨input.bytes.size, input.size_lt_wordModulus⟩

/-- Read one byte at the exact natural index represented by `offset`. -/
def byte? (input : InputData) (offset : Core.Word) : Option Core.Word :=
  match input.bytes.data[offset.val]? with
  | none => none
  | some byte =>
      some ⟨byte.toNat,
        Nat.lt_trans byte.toFin.isLt (by decide)⟩

/-- Decode one complete 32-byte big-endian window at an exact natural offset. -/
def wordBE? (input : InputData) (offset : Core.Word) : Option Core.Word :=
  if offset.val + 32 ≤ input.bytes.size then
    decodeWordBytesBE?
      (input.bytes.extract offset.val (offset.val + 32))
  else
    none

end InputData

end Solcore.ContractRuntime.HostStorageDriver
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsContractWordCallInput
/-! Exact fixed-width input derivation for the internal contract-word call. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostStorageDriver.InputData

/-- Represent one call input Word by its exact canonical 32-byte encoding. -/
def ofWord (word : Core.Word) : InputData := {
  bytes := encodeWordBytesBE word
  size_lt_wordModulus := by
    rw [encodeWordBytesBE_size]
    decide
}

end Solcore.ContractRuntime.HostStorageDriver.InputData
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsHostStorageExecutionInputs
/-! Immutable inputs shared by one combined handled storage execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostStorageDriver

/-- Run-fixed inputs kept outside the mutable working-storage context. -/
structure ExecutionInputs where
  codeAddress : Address
  callValue : Core.Word
  callerAddress : Address
  inputData : InputData
  currentAddress : Address

end Solcore.ContractRuntime.HostStorageDriver
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsHostStorageContext
/-! Mutable context threaded by handled storage execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostStorageDriver

universe u v

abbrev Context
    (RollbackState : Type u) (TraceState : Type v) :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount
    RollbackState TraceState

end Solcore.ContractRuntime.HostStorageDriver

/-!
## Consolidated module: `Solcore.ContractRuntime.HostStorageContextRebase`
-/

/-! Proof-preserving replacement of one storage context's working world. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostStorageDriver.Context

universe u v

/--
Install a selected working world while retaining the frame checkpoint, effects,
and storage selector. The caller supplies the refreshed selected Account.
-/
def rebaseWorking
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState)
    (storageAccount : Account)
    (storageAccount_present :
      world.account? context.context.storageAddress = some storageAccount) :
    HostStorageDriver.Context RollbackState TraceState := {
  context := {
    storageAddress := context.context.storageAddress
    values := {
      checkpoint := context.context.values.checkpoint
      working := (world, context.context.values.working.2)
    }
  }
  storageAccount := storageAccount
  storageAccount_present := storageAccount_present
}

/--
Install a selected working world and effect journal while retaining the frame
checkpoint and storage selector. The caller supplies the refreshed selected
Account.
-/
def rebaseWorkingWithEffects
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (storageAccount : Account)
    (storageAccount_present :
      world.account? context.context.storageAddress = some storageAccount) :
    HostStorageDriver.Context RollbackState TraceState := {
  context := {
    storageAddress := context.context.storageAddress
    values := {
      checkpoint := context.context.values.checkpoint
      working := (world, effects)
    }
  }
  storageAccount := storageAccount
  storageAccount_present := storageAccount_present
}

end Solcore.ContractRuntime.HostStorageDriver.Context
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsHostStorageHandler
/-! Canonical host handler for storage and immutable execution inputs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostStorageDriver

universe u v

/--
Total response function used by the legacy storage policy. The `emitLogWord`
arm exists only because `HostHandler.handle` is request-total; `handler` marks
that request unsupported, so `HostDriver.run` never invokes the arm. Observable
execution must use `TransactionHostStorageDriver`.
-/
def handleRequest
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (request : Core.HostRequest) :
    Context RollbackState TraceState × request.Response :=
  match request with
  | .storageRead slot => (context, context.readStorage slot)
  | .storageWrite slot value => (context.writeStorage slot value, ())
  | .storageAddress =>
      (context, addressToWord context.context.storageAddress)
  | .codeAddress => (context, addressToWord inputs.codeAddress)
  | .callValue => (context, inputs.callValue)
  | .callerAddress => (context, addressToWord inputs.callerAddress)
  | .inputDataByte? offset => (context, inputs.inputData.byte? offset)
  | .inputDataSize => (context, inputs.inputData.sizeWord)
  | .inputDataWordBE? offset => (context, inputs.inputData.wordBE? offset)
  | .currentAddress => (context, addressToWord inputs.currentAddress)
  | .callContractWord _ _ =>
      (context, ContractCallFailure.depthExceeded.result)
  | .callContractWordWithValue _ _ _ =>
      (context, ContractCallFailure.depthExceeded.result)
  | .createContractWord _ _ _ =>
      (context, ContractCallFailure.depthExceeded.result)
  | .emitLogWord _ _ => (context, ())

/-- Current combined handler indexed by the complete run-fixed input. -/
def handler
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs) :
    HostHandler (Context RollbackState TraceState) where
  supports
    | .emitLogWord _ _ => false
    | _ => true
  handle := handleRequest inputs

/-- Handle one suspension using the complete run-fixed input. -/
def handleSuspension
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    Context RollbackState TraceState × Core.State :=
  (handler inputs).handleSuspension context suspension

end Solcore.ContractRuntime.HostStorageDriver
end

section
-- leanmerge: from Solcore.ContractRuntime.HostStorageAccountPresence
/-! Presence evidence retained while another selected Account is being handled. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- One exact present Account witness at an arbitrary world-state address. -/
structure PresentAccountAt (world : WorldState) (address : Address) where
  account : Account
  present : world.account? address = some account

namespace HostStorageDriver.Context

universe u v

/-- Every storage context supplies presence at its own selected address. -/
def selectedPresence
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState) :
    PresentAccountAt context.context.values.working.1
      context.context.storageAddress :=
  ⟨context.storageAccount, context.storageAccount_present⟩

/-- Rebase from one arbitrary presence witness at the retained selector. -/
def rebaseFromPresence
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState)
    (presence : PresentAccountAt world context.context.storageAddress) :
    HostStorageDriver.Context RollbackState TraceState :=
  context.rebaseWorking world presence.account presence.present

end HostStorageDriver.Context

namespace PresentAccountAt

universe u v

/--
One low-level handled request preserves Account presence at every observed
address, including both the selected address and every different address.
-/
def afterHandleRequest
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (request : Core.HostRequest)
    (address : Address)
    (presence :
      PresentAccountAt context.context.values.working.1 address) :
    PresentAccountAt
      (HostStorageDriver.handleRequest inputs context request).1.context.values.working.1
      address := by
  cases request with
  | storageWrite slot value =>
      by_cases same : address = context.context.storageAddress
      · refine ⟨(context.writeStorage slot value).storageAccount, ?_⟩
        simpa [HostStorageDriver.handleRequest, same] using
          (context.writeStorage slot value).storageAccount_present
      · refine ⟨presence.account, ?_⟩
        simpa [HostStorageDriver.handleRequest] using
          (FrameCheckpointedWorkingPairWithPresentStorageAccount.workingAccount?_writeStorage_other
            context slot value address same).trans presence.present
  | storageRead slot =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | storageAddress =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | codeAddress =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | callValue =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | callerAddress =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | inputDataByte? offset =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | inputDataSize =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | inputDataWordBE? offset =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | currentAddress =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | callContractWord target input =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | callContractWordWithValue target value input =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | createContractWord templateId value input =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩
  | emitLogWord topic payload =>
      exact ⟨presence.account, by
        simpa [HostStorageDriver.handleRequest] using presence.present⟩

end PresentAccountAt

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsHostStorageDriver
/-! Canonical driver for storage-backed host execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

namespace HostStorageDriver

/-- Run the current handler using one immutable execution input. -/
def run
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    HostDriverResult (Context RollbackState TraceState) :=
  HostDriver.run (handler inputs) context fuel state

end HostStorageDriver

namespace CheckedHostCoreProgram

/-- Start checked code with one immutable execution input. -/
def runWithStorage
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    HostDriverResult
      (HostStorageDriver.Context RollbackState TraceState) :=
  HostStorageDriver.run context inputs fuel
    (Core.State.initial code.program.body Core.hostEnvironment)

end CheckedHostCoreProgram

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.HostStorageDriverProperties`
-/

/-! Execution and preservation laws for the canonical storage host driver. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.HostStorageDriverSafetyProperties`
-/

/-! Type and fault safety for the canonical storage host driver. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.HostStorageDriverFuelProperties`
-/

/-! Whole-run fuel accounting indexed by immutable execution inputs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

namespace HostStorageDriver

/-- Handled transition segments under one exact immutable input. -/
abbrev HandledSteps
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs) :=
  HostDriver.HandledSteps
    (@handler RollbackState TraceState inputs)

/-- Fuel soundness indexed by one exact immutable input. -/
def FuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (result : HostDriverResult (Context RollbackState TraceState))
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (startContext : Context RollbackState TraceState)
    (start : Core.State) : Prop :=
  result.FuelSoundWith
    (@handler RollbackState TraceState inputs)
    fuel startContext start

end HostStorageDriver

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsWordReturnedFrameCompletion
/-! Successful handled Word completion and canonical returned-frame view. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v w

/-- Exact successful data extracted from a storage-backed handled Word result. -/
structure WordReturnedFrameCompletion
    (RollbackState : Type u) (TraceState : Type v) where
  context : HostStorageDriver.Context RollbackState TraceState
  word : Core.Word
  store : Core.Store

namespace WordReturnedFrameCompletion

/-- Canonical 32-byte big-endian return data for the completed Word. -/
def returnData
    {RollbackState : Type u} {TraceState : Type v}
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    Bytes :=
  encodeWordBytesBE completion.word

/-- Reconstruct the exact successful raw handled result. -/
def toHostDriverResult
    {RollbackState : Type u} {TraceState : Type v}
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    HostDriverResult (HostStorageDriver.Context RollbackState TraceState) :=
  ⟨completion.context, .done (.word completion.word) completion.store⟩

/-- Build the canonical returned frame without inventing a trap reason. -/
def toFrameContinuationContext
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    FrameContinuationContext RollbackState TraceState TrapReason :=
  FrameContinuationContext.fromCheckpointedWorkingPair
    completion.context.context.values
    (.returned completion.returnData)

end WordReturnedFrameCompletion

namespace HostDriverResult

/-- Extract exactly a completed Word, retaining its context and Core Store. -/
def toWordReturnedFrameCompletion?
    {RollbackState : Type u} {TraceState : Type v}
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState)) :
    Option (WordReturnedFrameCompletion RollbackState TraceState) :=
  match result with
  | ⟨context, .done (.word word) store⟩ =>
      some ⟨context, word, store⟩
  | _ => none

end HostDriverResult

end Solcore.ContractRuntime
end
