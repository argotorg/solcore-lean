import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission

/-! Actual for-item execution supplies admission at its live final context and
at the original context used after binder restoration. Stable row histories
come from the same reached pool and its real administrative receipt. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedForItemsAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

/-- Source typing and this exact successful trace establish both legitimate
heap contexts. The original prefix's reached state is retained verbatim. -/
theorem after_items {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    {context staticFinalContext runtimeFinalContext : SourceSemantics.Context}
    (admitted : Admission bridge context first)
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment finalEnvironment : Dynamic.Environment} {items : List ForItemForm}
    {control : SourceSemantics.ControlContext}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typing : ForItemsHaveType source control context items staticFinalContext)
    (trace : Dynamic.ForItemsExecute program context evidence source environment initial.heap
      items runtimeFinalContext finalEnvironment reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    runtimeFinalContext = staticFinalContext ∧ Admission bridge context last ∧
      Admission bridge staticFinalContext last ∧ Dynamic.HeapTypesExtend initial.heap reached.heap ∧
        Dynamic.EnvironmentAgrees reached.heap staticFinalContext.locals finalEnvironment := by
  obtain ⟨same, heapTyped, extension, finalLocals⟩ :=
    trace.preserved wellFormed runtime covers locals admitted.heap typing
  have fields := Dynamic.ForItemsHaveType.runtimeContextFields typing
  have finalTyped := heapTyped.transportClosed fields.signatures runtime.closed
    (fields.targetClosed runtime.closed) runtime.variables_closed
    (fields.targetResidualVariablesOpen runtime.residual_variables_open)
  have rows := StableRows.after_administrative (bridge.pool first) (bridge.pool last) admitted.rows frame
  exact ⟨same, ⟨heapTyped, rows⟩, ⟨finalTyped, rows⟩, extension, finalLocals⟩

/-- Keep the actual Source prefix size independent from every native suffix
budget while establishing admission at the exact reached state. -/
theorem after_items_sized {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    {context staticFinalContext runtimeFinalContext : SourceSemantics.Context}
    (admitted : Admission bridge context first)
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment finalEnvironment : Dynamic.Environment} {items : List ForItemForm}
    {control : SourceSemantics.ControlContext} {size : Nat}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typing : ForItemsHaveType source control context items staticFinalContext)
    (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment initial.heap
      items runtimeFinalContext finalEnvironment reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    runtimeFinalContext = staticFinalContext ∧ Admission bridge context last ∧
      Admission bridge staticFinalContext last ∧ Dynamic.HeapTypesExtend initial.heap reached.heap ∧
        Dynamic.EnvironmentAgrees reached.heap staticFinalContext.locals finalEnvironment :=
  after_items bridge first last admitted wellFormed runtime covers locals typing trace.sound frame

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedForItemsAdmission
