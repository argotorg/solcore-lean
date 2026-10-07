import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission

/-! Bit-not assignment retains its real resolution snapshot and writes the
latest root. The genuine Source trace supplies deep heap typing at that exact
written state; native administrative effects authenticate row history only. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSnapshotAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

/-- Resolution and the actual snapshot write preserve Source typing through
the already proved Source semantics. No expression execution law is assumed. -/
theorem after_snapshot {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    {context : SourceSemantics.Context}
    (admitted : Admission bridge context first)
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {assignment : AssignmentResolution} {updatedRoot : Dynamic.Value}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typing : SourceBitNotAssignmentValid source context assignment)
    (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      environment initial.heap assignment.target updatedRoot reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    Admission bridge context last ∧ Dynamic.HeapTypesExtend initial.heap reached.heap := by
  have expressionPreserves : Dynamic.ExpressionExecutionPreserves program context evidence source environment := by
    intro before after id value type covered agreed heapTyped typed evaluated
    exact wellFormed.wholeLanguagePreservation.expression context evidence source environment
      before after id value type runtime covered agreed heapTyped typed evaluated
  obtain ⟨heapTyped, extension⟩ := trace.bitNotPreserves expressionPreserves covers locals admitted.heap typing
  exact ⟨⟨heapTyped,
    StableRows.after_administrative (bridge.pool first) (bridge.pool last) admitted.rows frame⟩, extension⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSnapshotAdmission
