import Solcore.ContractRuntime.FrameContinuationContextFromCheckpointedWorkingPair
import Solcore.ContractRuntime.HostStorageDriver
import Solcore.ContractRuntime.RuntimeScalars
import Solcore.ContractRuntime.FrameResolutionResult
import Solcore.ContractRuntime.RuntimeScalars.WordBytesProperties
import Solcore.ContractRuntime.HostDriver

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

/-!
## Consolidated module: `Solcore.ContractRuntime.WordReturnedFrameCompletionProperties`
-/

/-! Exact raw, byte, frame, and resolution laws for Word completion. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v w

namespace HostDriverResult

@[simp] theorem toWordReturnedFrameCompletion?_done_word
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (word : Core.Word) (store : Core.Store) :
    (HostDriverResult.mk context
      (.done (.word word) store)).toWordReturnedFrameCompletion? =
      some ⟨context, word, store⟩ :=
  rfl

theorem toWordReturnedFrameCompletion?_done_eq_none_iff
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (value : Core.Value) (store : Core.Store) :
    (HostDriverResult.mk context
      (.done value store)).toWordReturnedFrameCompletion? = none ↔
      ∀ word, value ≠ .word word := by
  cases value <;> simp [toWordReturnedFrameCompletion?]

@[simp] theorem toWordReturnedFrameCompletion?_outOfFuel
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (state : Core.State) :
    (HostDriverResult.mk context
      (.outOfFuel state)).toWordReturnedFrameCompletion? = none :=
  rfl

@[simp] theorem toWordReturnedFrameCompletion?_fault
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (error : Core.MachineFault) (state : Core.State) :
    (HostDriverResult.mk context
      (.fault error state)).toWordReturnedFrameCompletion? = none :=
  rfl

@[simp] theorem toWordReturnedFrameCompletion?_unsupported
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (suspension : Core.HostSuspension) (remainingFuel : Nat) :
    (HostDriverResult.mk context
      (.unsupported suspension remainingFuel)).toWordReturnedFrameCompletion? =
        none :=
  rfl

/-- Successful projection is exactly inverse to reconstructing the raw result. -/
theorem toWordReturnedFrameCompletion?_eq_some_iff
    {RollbackState : Type u} {TraceState : Type v}
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    result.toWordReturnedFrameCompletion? = some completion ↔
      result = completion.toHostDriverResult := by
  cases result with
  | mk context outcome =>
      cases outcome with
      | done value store =>
          cases value <;> cases completion <;>
            simp [toWordReturnedFrameCompletion?,
              WordReturnedFrameCompletion.toHostDriverResult]
      | outOfFuel state =>
          cases completion
          simp [toWordReturnedFrameCompletion?,
            WordReturnedFrameCompletion.toHostDriverResult]
      | fault error state =>
          cases completion
          simp [toWordReturnedFrameCompletion?,
            WordReturnedFrameCompletion.toHostDriverResult]
      | unsupported suspension remainingFuel =>
          cases completion
          simp [toWordReturnedFrameCompletion?,
            WordReturnedFrameCompletion.toHostDriverResult]

end HostDriverResult

namespace WordReturnedFrameCompletion

@[simp] theorem mk_context
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (word : Core.Word) (store : Core.Store) :
    (WordReturnedFrameCompletion.mk context word store).context = context :=
  rfl

@[simp] theorem mk_word
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (word : Core.Word) (store : Core.Store) :
    (WordReturnedFrameCompletion.mk context word store).word = word :=
  rfl

@[simp] theorem mk_store
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (word : Core.Word) (store : Core.Store) :
    (WordReturnedFrameCompletion.mk context word store).store = store :=
  rfl

@[simp] theorem toWordReturnedFrameCompletion?_toHostDriverResult
    {RollbackState : Type u} {TraceState : Type v}
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    completion.toHostDriverResult.toWordReturnedFrameCompletion? =
      some completion := by
  cases completion
  rfl

@[simp] theorem returnData_size
    {RollbackState : Type u} {TraceState : Type v}
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    completion.returnData.size = 32 := by
  exact encodeWordBytesBE_size completion.word

@[simp] theorem decodeWordBytesBE?_returnData
    {RollbackState : Type u} {TraceState : Type v}
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    decodeWordBytesBE? completion.returnData = some completion.word := by
  exact decodeWordBytesBE?_encodeWordBytesBE completion.word

@[simp] theorem stateCheckpoint_toFrameContinuationContext
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    (completion.toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason).stateCheckpoint =
      completion.context.context.values.checkpoint.state :=
  rfl

@[simp] theorem effectCheckpoint_toFrameContinuationContext
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    (completion.toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason).effectCheckpoint =
      completion.context.context.values.checkpoint.effects :=
  rfl

@[simp] theorem effectWorking_toFrameContinuationContext
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    (completion.toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason).effectWorking =
      completion.context.context.values.working.2 :=
  rfl

@[simp] theorem result_toFrameContinuationContext
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    (completion.toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason).result =
      ⟨completion.context.context.values.working.1,
        .returned completion.returnData⟩ :=
  rfl

@[simp] theorem resolve_toFrameContinuationContext
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    (completion.toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason).resolve =
      .returned completion.context.context.values.working.1
        completion.context.context.values.working.2 completion.returnData :=
  rfl

/-- Core-local Store is retained by the carrier but is not serialized. -/
theorem toFrameContinuationContext_store_independent
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (word : Core.Word) (leftStore rightStore : Core.Store) :
    ((⟨context, word, leftStore⟩ :
        WordReturnedFrameCompletion RollbackState TraceState).toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason) =
    ((⟨context, word, rightStore⟩ :
        WordReturnedFrameCompletion RollbackState TraceState).toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason) :=
  rfl

end WordReturnedFrameCompletion

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.WordReturnedFrameCompletionSafetyProperties`
-/

/-! Typed branch exclusion and terminal resumption for Word completion. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostDriverResult

universe u v

/-- A typed Word projection fails only at exhaustion or a policy boundary. -/
theorem toWordReturnedFrameCompletion?_eq_none_iff_of_hasType
    {RollbackState : Type u} {TraceState : Type v}
    {definitions : Core.DataEnvironment}
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (typing : result.outcome.HasType .word definitions) :
    result.toWordReturnedFrameCompletion? = none ↔
      (∃ context state,
        result = ⟨context, .outOfFuel state⟩) ∨
      ∃ context suspension remainingFuel,
        result = ⟨context, .unsupported suspension remainingFuel⟩ := by
  cases result with
  | mk context outcome =>
      cases outcome with
      | done value store =>
          obtain ⟨world, _storeTyping, valueTyping⟩ := typing
          obtain ⟨word, rfl⟩ := valueTyping.word_shape
          simp
      | outOfFuel state =>
          simp
      | fault error state =>
          exact False.elim typing
      | unsupported suspension remainingFuel => simp

/-- A successful projection is unchanged by any later fuel offer. -/
theorem toWordReturnedFrameCompletion?_resumeWithFuel_of_some
    {RollbackState : Type u} {TraceState : Type v}
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (handler :
      HostHandler (HostStorageDriver.Context RollbackState TraceState))
    (additional : Nat)
    (completion : WordReturnedFrameCompletion RollbackState TraceState)
    (completed :
      result.toWordReturnedFrameCompletion? = some completion) :
    toWordReturnedFrameCompletion?
        (result.resumeWithFuel handler additional) = some completion := by
  rw [(toWordReturnedFrameCompletion?_eq_some_iff
    result completion).mp completed]
  rfl

end Solcore.ContractRuntime.HostDriverResult
