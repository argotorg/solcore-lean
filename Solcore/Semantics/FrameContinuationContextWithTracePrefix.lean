import Solcore.Semantics.FrameResolutionResult
import Solcore.Semantics.FrameTracePrefix

/-! A frame continuation context carrying an ordered trace-prefix invariant. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v w

/-- A continuation context whose checkpoint trace prefixes its working trace. -/
structure FrameContinuationContextWithTracePrefix
    (RollbackState : Type u) (Event : Type v)
    (TrapReason : Type w)
    extends FrameContinuationContext
      RollbackState (FrameTrace Event) TrapReason where
  tracePrefix :
    FrameTrace.IsPrefixOf effectCheckpoint.trace effectWorking.trace

end Solcore.Semantics
