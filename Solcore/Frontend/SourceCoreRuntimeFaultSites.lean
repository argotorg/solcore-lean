import Solcore.Frontend.SourceCoreAssignmentFaultSites

/-! Assemble single-function read, assignment and boundary diagnostics without
introducing an import cycle in the ordinary read-site table. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreRuntimeFaultSites

structure Prepared where
  table : SourceCoreFaultSites.Table
  assignments : SourceCoreAssignmentFaultSites.Table
  deriving Repr

inductive Error where
  | sites (error : SourceCoreFaultSites.Error)
  | assignments (error : SourceCoreAssignmentFaultSites.Error)
  deriving Repr, DecidableEq

def prepare (source : SourceInference.TypedSource) (resultType : TypeSystem.Ty) : Except Error Prepared := do
  let table ← (SourceCoreFaultSites.prepare source resultType).mapError Error.sites
  let assignments ← (SourceCoreAssignmentFaultSites.prepare source (table.reads.length + 2)).mapError Error.assignments
  pure { table := { table with additional := assignments.diagnostics }, assignments }

end Solcore.Frontend.SourceCoreRuntimeFaultSites
