import Solcore.Semantics.FrameOutcomeTrapReasonMap
import Solcore.Semantics.FrameRunResult

/-! Working-state-preserving mapping of frame-run trap-reason types. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameRunResult

universe u v

/-- Preserve the working state while mapping only the result's trapped reason. -/
def mapTrapReason
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (result : FrameRunResult TrapReason) :
    FrameRunResult MappedTrapReason :=
  ⟨result.working, result.outcome.mapTrapReason mapReason⟩

end Solcore.Semantics.FrameRunResult
