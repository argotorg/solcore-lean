import Solcore.SourceSemantics.CoreLowering.ProtectedStateScopeReturn
import Solcore.SourceSemantics.CoreLowering.ProtectedStateMarkedAllocation
import Solcore.SourceSemantics.CoreLowering.ProtectedStateAllocationReadiness

/-! Match prefixes use a real marked allocation producer and retain a future
scope restoration receipt. Compatibility wrappers have a constant observation;
they forget the added witness after executing the same prefix proof. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.MatchPrefix
open Core Frontend SourceInference

/-- Restore the constant witness used by the original unguarded APIs. -/
def unitBindings : Bindings OrdinaryAllocation.unitProtocol where
  prepend _ _ _ _ := ()
  prepend_related _ _ _ _ := True.intro
  prepend_records _ _ _ _ := rfl
  restore _ := ()
  restore_related _ := True.intro
  restore_records _ := rfl

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.MatchPrefix
