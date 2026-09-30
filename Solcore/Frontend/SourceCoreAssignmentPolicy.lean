import Solcore.Frontend.SourceCoreLoops
import Solcore.Frontend.SourceCoreAssignments
import Solcore.Frontend.SourceCoreAssignmentFaultSites

/-! Attach absent-operand diagnostics to the compound/unary CPS callbacks.
Equal assignment continues through the entry profile's own target projector. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreAssignmentPolicy

def attach (policy : SourceCoreLoops.Policy) (sites : SourceCoreAssignmentFaultSites.Table) :
    SourceCoreLoops.Policy := { policy with
  assignValue := some fun expression fuel source scope site assignment operator rhs outputType next reasonAt =>
    SourceCoreAssignments.assignValueWithReasons expression fuel source scope assignment operator rhs outputType
      next (sites.reasonAt site assignment.target.root (.value operator)) reasonAt
  assignBitNot := some fun source scope site assignment outputType next =>
    SourceCoreAssignments.assignBitNot source scope assignment outputType next
      (sites.reasonAt site assignment.target.root .bitNot)
}

end Solcore.Frontend.SourceCoreAssignmentPolicy
