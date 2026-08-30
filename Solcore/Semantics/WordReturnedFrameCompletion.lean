import Solcore.Semantics.FrameContinuationContextFromCheckpointedWorkingPair
import Solcore.Semantics.HostStorageDriver
import Solcore.Semantics.RuntimeScalars

/-! Successful handled Word completion and canonical returned-frame view. -/

set_option autoImplicit false

namespace Solcore.Semantics

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

end Solcore.Semantics
