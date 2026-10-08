import Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticPlan

/-! The actual operand table interprets the prepared assignment residual.
Missing/default and uninitialized receipts still concern each real generated
Head. Only genuine table diagnostics are included in the supplied fault model. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticPlan.Plan.LocalReceipts
open Core Frontend SourceInference

variable {source : TypedSource} {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The emitted prepared residual follows from real local Errors and the
original table inclusion, preserving the independent Source origin typing. -/
theorem prepared
    (typed : AssignmentDiagnosticOrigins.OperandsTyped source)
    (issued : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (errors : Plan.LocalReceipts (factory := AssignmentDiagnosticOrigins.Factory.unchanged .reachable source
      (GenericAssignmentDiagnostics.token table)) registry faults)
    (included : ∀ reason token, GenericAssignmentDiagnostics.OperandRep table reason token → faults reason token) :
    Plan.LocalReceipts (factory := AssignmentDiagnosticOrigins.Factory.prepared typed issued) registry faults := by
  refine ⟨?_, errors.unary⟩
  intro values context certificate scope administrative definitions assignment operator rhs head site _origin same
    sourceTyped rightTyped profile
  have actual := errors.assignment head site True.intro same sourceTyped rightTyped profile
  exact ⟨actual.missing, actual.uninitialized, included⟩

end Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticPlan.Plan.LocalReceipts
