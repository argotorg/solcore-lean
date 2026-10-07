import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCaptureExecutionValidity
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryPrefix

/-! Authentic closure frames and the actual parameter prefix supply Source
admission at the body boundary. The full original source, dictionary, raw
parameter types and reached allocation remain intact; no body execution law
or native type projection supplies these receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaSourceAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues

variable {program : Program} {function : Dynamic.Closure}

theorem runtime_of_frame (frame : Dynamic.ClosureFrame program function) :
    Dynamic.SourceRuntimeValid program function.context function.source :=
  ⟨frame.signatures, frame.code.graph, frame.code.owner, frame.code.closed,
    frame.code.variables_closed, frame.code.residual_variables_open, frame.code.requirement_ledger⟩

theorem runtime_at_parameters (frame : Dynamic.ClosureFrame program function)
    {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context) :
    Dynamic.SourceRuntimeValid program context function.source ∧ function.evidence.Covers context := by
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields extended
  exact ⟨(runtime_of_frame frame).transport fields, fields.covers frame.evidence_covers⟩

/-- Inverting the same original lambda occurrence recovers body typing at the
actual parameter context. The whole body and its control summary are retained. -/
theorem body_typed_at_parameters (frame : Dynamic.ClosureFrame program function)
    {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context) :
    ∃ finalContext facts,
      StatementsHaveType function.source { returnType := function.resultType } context function.body finalContext facts ∧
      BodyCompletes function.resultType facts := by
  obtain ⟨id, node, contains, form, raw, typing⟩ := frame.code.occurrence
  rw [form] at typing
  generalize rawEq : TypeSystem.Ty.function
    (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body))) function.resultType = rawType at typing
  generalize planEq : ExpressionRequirementPlan.ordinary [] = plan at typing
  cases typing with
  | lambda unique staticExtension bodyTyped completes =>
    have same := Dynamic.MonoBindersExtend.functional extended staticExtension
    subst same
    exact ⟨_, _, bodyTyped, completes⟩

section ActualParameters
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {actual : Environment} (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {location : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
    captured code history inputs functions registry arguments nativeArguments before store location current ghost)

/-- Source heap typing follows the genuine allocation in the same prefix.
The Source argument types are supplied before native projection. -/
theorem heap_typed_at_parameters (frame : Dynamic.ClosureFrame program function)
    (beforeTyped : Dynamic.HeapWellTyped function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types) :
    Dynamic.HeapWellTyped inputs.context entry.entry.heap := by
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq inputs.extended
  have actualArguments : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes] using argumentsTyped
  have reached := Dynamic.BindersAllocate.preservesHeapTyping beforeTyped actualArguments entry.entry.allocation
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended
  exact reached.transportClosed fields.signatures frame.code.closed (fields.targetClosed frame.code.closed)
    frame.code.variables_closed (fields.targetResidualVariablesOpen frame.code.residual_variables_open)

/-- All Source admission fields describe the same original body and actual
parameter heap/environment returned by the prefix. -/
theorem admission_at_parameters (frame : Dynamic.ClosureFrame program function)
    (beforeTyped : Dynamic.HeapWellTyped function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types) :
    Dynamic.SourceRuntimeValid program inputs.context function.source ∧
      function.evidence.Covers inputs.context ∧
      Dynamic.HeapWellTyped inputs.context entry.entry.heap ∧
      Dynamic.EnvironmentAgrees entry.entry.heap inputs.context.locals entry.entry.environment ∧
      ∃ finalContext facts,
        StatementsHaveType function.source { returnType := function.resultType } inputs.context function.body finalContext facts ∧
        BodyCompletes function.resultType facts := by
  have runtime := runtime_at_parameters frame inputs.extended
  exact ⟨runtime.1, runtime.2,
    heap_typed_at_parameters captured code history inputs functions entry frame beforeTyped argumentsTyped,
    entry.entry.locals, body_typed_at_parameters frame inputs.extended⟩

end ActualParameters
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaSourceAdmission
