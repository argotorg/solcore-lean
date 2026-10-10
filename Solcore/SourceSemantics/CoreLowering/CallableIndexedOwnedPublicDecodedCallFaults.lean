import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedAssignmentFaults
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSecondCallGateRejection

/-! A concrete receiving-table view for assignment and physical call-arity
errors. Existing assignment diagnostics retain their raw types and operators;
the call case retains both physical counts. Source traces retain their reached
heaps. First-guard stage failures keep their separate scoped interpretation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedCallFaults
open Core Frontend SourceInference GeneralHeap CompatiblePayload

inductive ErrorView : Dynamic.SemanticFault → SourceTypedRuntime.RuntimeError → Prop where
  | assignment {reason : Dynamic.SemanticFault} {error : SourceTypedRuntime.RuntimeError}
      (view : CallableIndexedOwnedPublicDecodedAssignmentFaults.ErrorView reason error) :
      ErrorView reason error
  | arity (expected actual : Nat) :
      ErrorView (.argumentArityMismatch expected actual) (.argumentArityMismatch expected actual)

def faults (table : SourceCoreFaultSites.Table) : FunctionCalls.FaultRep :=
  fun reason token => ∃ diagnostic,
    table.diagnostic? token = some diagnostic ∧ ErrorView reason diagnostic.error

def stagedSemanticFaults (table : SourceCoreFaultSites.Table) : RecursiveStageMeaning.FaultRep :=
  fun failure token => match failure with
    | .semantic reason => faults table reason token
    | .stage .. => False

theorem of_decoded {table : SourceCoreFaultSites.Table} {reason : Dynamic.SemanticFault}
    {token : Word} {diagnostic : SourceCoreFaultSites.Diagnostic}
    (decoded : table.diagnostic? token = some diagnostic)
    (view : ErrorView reason diagnostic.error) : faults table reason token :=
  ⟨diagnostic, decoded, view⟩

/-- The existing literal assignment view is forwarded at the same table. -/
theorem of_assignment {table : SourceCoreFaultSites.Table} {reason : Dynamic.SemanticFault}
    {token : Word}
    (represented : CallableIndexedOwnedPublicDecodedAssignmentFaults.faults table reason token) :
    faults table reason token := by
  obtain ⟨diagnostic, decoded, view⟩ := represented
  exact ⟨diagnostic, decoded, .assignment view⟩

/-- The actual arity row supplies the diagnostic and both exact counts. -/
theorem of_arity {table : SourceCoreFaultSites.Table} {reason : Dynamic.SemanticFault}
    {token : Word}
    (represented : CallableIndexedOwnedPreparedSecondCallGateRejection.arityFaults table reason token) :
    faults table reason token := by
  obtain ⟨expected, actual, diagnostic, sameReason, decoded, sameError⟩ := represented
  cases sameReason
  refine ⟨diagnostic, decoded, ?_⟩
  rw [sameError]
  exact .arity expected actual

/-- Forward the exact semantic tag used by the second call gate. -/
theorem of_staged_arity {table : SourceCoreFaultSites.Table}
    {failure : Staging.Recursive.Failure} {token : Word}
    (represented : CallableIndexedOwnedPreparedSecondCallGateRejection.stagedArityFaults
      table failure token) : stagedSemanticFaults table failure token := by
  cases failure with
  | semantic reason => exact of_arity represented
  | stage origin call reason => exact represented

section Results
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
  {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty} {type : Ty}
  {table : SourceCoreFaultSites.Table}

theorem arity_result {outcome : Dynamic.ExpressionOutcome} {value : Value}
    (represented : FunctionCalls.ResultRepresents model mapping world sourceType type
      (CallableIndexedOwnedPreparedSecondCallGateRejection.arityFaults table) outcome value) :
    FunctionCalls.ResultRepresents model mapping world sourceType type (faults table) outcome value := by
  cases represented with
  | value represented => exact .value represented
  | fault represented => exact .fault (of_arity represented)

theorem staged_arity_result {outcome : Staging.Recursive.Outcome} {value : Value}
    (represented : RecursiveStageMeaning.ResultRepresentsFor model mapping world sourceType type
      (CallableIndexedOwnedPreparedSecondCallGateRejection.stagedArityFaults table) outcome value) :
    RecursiveStageMeaning.ResultRepresentsFor model mapping world sourceType type
      (stagedSemanticFaults table) outcome value := by
  cases represented with
  | value represented => exact .value represented
  | fault represented => exact .fault (of_staged_arity represented)

end Results
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedCallFaults
