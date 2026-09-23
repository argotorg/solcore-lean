import Solcore.ContractRuntime.FrameOutcomeTrapReasonMap
import Solcore.ContractRuntime.FrameRunResult

/-! Working-state-preserving mapping of frame-run trap-reason types. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameRunResult

universe u v

/-- Preserve the working state while mapping only the result's trapped reason. -/
def mapTrapReason
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (result : FrameRunResult TrapReason) :
    FrameRunResult MappedTrapReason :=
  ⟨result.working, result.outcome.mapTrapReason mapReason⟩

end Solcore.ContractRuntime.FrameRunResult
