import Solcore.Semantics.CheckedHostCoreWordProgram
import Solcore.Semantics.HostStorageDriver
import Solcore.Semantics.WordReturnedFrameCompletion

/-! Storage-backed execution specialized to checked Word-result programs. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace CheckedHostCoreWordProgram

/-- Run checked Word-result code with one immutable storage-host input. -/
def runWithStorage
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreWordProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    HostDriverResult
      (HostStorageDriver.Context RollbackState TraceState) :=
  code.code.runWithStorage context inputs fuel

/-- Project the successful Word branch while keeping raw execution separate. -/
def runWithStorageReturnedFrameCompletion?
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreWordProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    Option (WordReturnedFrameCompletion RollbackState TraceState) :=
  (code.runWithStorage context inputs fuel).toWordReturnedFrameCompletion?

end CheckedHostCoreWordProgram

end Solcore.Semantics
