import Solcore.Semantics.FrameContinuationContextWithTracePrefix
import Solcore.Semantics.FrameContinuationContextTrapReasonMap

/-! Trap-reason mapping for continuation contexts with trace-prefix evidence. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameContinuationContextWithTracePrefix

universe u v w x

/-- Map only the base context's trap reason, retaining exact prefix evidence. -/
def mapTrapReason
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context :
      FrameContinuationContextWithTracePrefix RollbackState Event TrapReason) :
    FrameContinuationContextWithTracePrefix
      RollbackState Event MappedTrapReason :=
  {
    toFrameContinuationContext :=
      context.toFrameContinuationContext.mapTrapReason mapReason
    tracePrefix := context.tracePrefix
  }

end Solcore.Semantics.FrameContinuationContextWithTracePrefix
