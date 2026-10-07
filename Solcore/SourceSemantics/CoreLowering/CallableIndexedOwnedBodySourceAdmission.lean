import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodInvocationBounds
import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation

/-! Original whole-program body certificates supply Source admission at the
actual parameter allocation. Raw Source argument types, the full dictionary
and the original statement roots remain independent of Core projections. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodySourceAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

variable {program : Program} {body : Dynamic.BodyInstance}
  {inputTypes : List TypeSystem.Ty} {staticContext : SourceSemantics.Context} {facts : BodyFacts}
  (certificate : Dynamic.BodyInstanceTypingCertificate program body inputTypes staticContext facts)

include certificate

/-- The actual monomorphic parameter context agrees with the original static
certificate, even when the two receipts expose different type-list variables. -/
theorem parameter_context_eq {types : List TypeSystem.Ty} {context : SourceSemantics.Context}
    (extended : MonoBindersExtend body.source.owner body.context body.source.inputs types context) :
    context = staticContext :=
  Dynamic.MonoBindersExtend.functional extended certificate.typing.inputs_extend

/-- Source runtime validity and the full dictionary follow the same actual
parameter extension; no native function typing supplies these fields. -/
theorem runtime_at_parameters {types : List TypeSystem.Ty} {context : SourceSemantics.Context}
    {dictionary : Dynamic.EvidenceEnvironment} (covers : dictionary.Covers body.context)
    (extended : MonoBindersExtend body.source.owner body.context body.source.inputs types context) :
    Dynamic.SourceRuntimeValid program context body.source ∧ dictionary.Covers context := by
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields extended
  exact ⟨certificate.sourceRuntimeValid.transport fields, fields.covers covers⟩

/-- The original complete body typing applies to the exact ordered roots and
actual parameter context. Its original completion summary is retained. -/
theorem body_typed_at_parameters {types : List TypeSystem.Ty} {context : SourceSemantics.Context}
    {statements : List StatementId}
    (extended : MonoBindersExtend body.source.owner body.context body.source.inputs types context)
    (roots : Dynamic.StatementRoots body.source.roots statements) :
    ∃ finalContext,
      StatementsHaveType body.source { returnType := body.resultType } context statements finalContext facts ∧
      BodyCompletes body.resultType facts := by
  obtain ⟨finalContext, typed, _noExpressions, completes⟩ := certificate.typing.body_typed
  have same := parameter_context_eq certificate extended
  subst context
  exact ⟨finalContext, roots.filterMap_eq ▸ typed, completes⟩

/-- The reached heap is the actual Source allocation. The initial Source
heap and raw argument typing are authenticated before any Core projection. -/
theorem heap_typed_at_parameters {types : List TypeSystem.Ty} {context : SourceSemantics.Context}
    {before reached : Dynamic.Heap} {arguments : List Dynamic.Value} {environment : Dynamic.Environment}
    (extended : MonoBindersExtend body.source.owner body.context body.source.inputs types context)
    (allocated : Dynamic.BindersAllocate [] before body.source.inputs arguments environment reached)
    (beforeTyped : Dynamic.HeapWellTyped body.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes body.context before arguments inputTypes) :
    Dynamic.HeapWellTyped context reached := by
  have rawArguments : Dynamic.ValuesHaveTypes body.context before arguments
      (body.source.inputs.map (fun binder => binder.scheme.body)) := by
    simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq certificate.typing.inputs_extend] using argumentsTyped
  have actualHeap := allocated.preservesHeapTyping beforeTyped rawArguments
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields extended
  exact actualHeap.transportClosed fields.signatures certificate.type_parameters_empty
    (fields.targetClosed certificate.type_parameters_empty) certificate.type_variables_empty
    (fields.targetResidualVariablesOpen certificate.residual_type_variables_open)

/-- This admission describes the same body, dictionary, parameter heap and
Source environment produced by the real allocation. It contains no body law. -/
theorem admission_at_parameters {types : List TypeSystem.Ty} {context : SourceSemantics.Context}
    {dictionary : Dynamic.EvidenceEnvironment} {statements : List StatementId}
    {before reached : Dynamic.Heap} {arguments : List Dynamic.Value} {environment : Dynamic.Environment}
    (covers : dictionary.Covers body.context)
    (extended : MonoBindersExtend body.source.owner body.context body.source.inputs types context)
    (roots : Dynamic.StatementRoots body.source.roots statements)
    (allocated : Dynamic.BindersAllocate [] before body.source.inputs arguments environment reached)
    (beforeTyped : Dynamic.HeapWellTyped body.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes body.context before arguments inputTypes) :
    Dynamic.SourceRuntimeValid program context body.source ∧ dictionary.Covers context ∧
      Dynamic.HeapWellTyped context reached ∧ Dynamic.EnvironmentAgrees reached context.locals environment ∧
      ∃ finalContext,
        StatementsHaveType body.source { returnType := body.resultType } context statements finalContext facts ∧
        BodyCompletes body.resultType facts := by
  have runtime := runtime_at_parameters certificate covers extended
  have initialLocals : Dynamic.EnvironmentAgrees before body.context.locals [] := by
    rw [certificate.locals_empty]
    exact .nil
  have mono := FunctionCallBody.mono_binders extended
  exact ⟨runtime.1, runtime.2,
    heap_typed_at_parameters certificate extended allocated beforeTyped argumentsTyped,
    allocated.preservesEnvironmentAgreement mono.1 mono.2 initialLocals,
    body_typed_at_parameters certificate extended roots⟩


/-- A genuine method frame transports the admission to its exact compiled
closure-shaped view. The actual allocation and full dictionary stay original. -/
theorem admission_at_frame_parameters {function : Dynamic.Closure}
    (frame : CallableCoercionMethodFrame.Frame body function)
    {types : List TypeSystem.Ty} {context : SourceSemantics.Context}
    {before reached : Dynamic.Heap} {arguments : List Dynamic.Value} {environment : Dynamic.Environment}
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (allocated : Dynamic.BindersAllocate [] before function.parameters arguments environment reached)
    (beforeTyped : Dynamic.HeapWellTyped function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputTypes) :
    Dynamic.SourceRuntimeValid program context function.source ∧ function.evidence.Covers context ∧
      Dynamic.HeapWellTyped context reached ∧ Dynamic.EnvironmentAgrees reached context.locals environment ∧
      ∃ finalContext,
        StatementsHaveType function.source { returnType := function.resultType } context function.body finalContext facts ∧
        BodyCompletes function.resultType facts := by
  have actualExtension : MonoBindersExtend body.source.owner body.context body.source.inputs types context := by
    simpa only [frame.source, frame.context, frame.parameters] using extended
  have actualAllocation : Dynamic.BindersAllocate [] before body.source.inputs arguments environment reached :=
    frame.parameters ▸ allocated
  have actualHeap : Dynamic.HeapWellTyped body.context before := by simpa only [frame.context] using beforeTyped
  have actualArguments : Dynamic.ValuesHaveTypes body.context before arguments inputTypes := by
    simpa only [frame.context] using argumentsTyped
  have admission := admission_at_parameters certificate frame.covers actualExtension frame.roots actualAllocation
    actualHeap actualArguments
  simpa only [frame.source, frame.result] using admission


omit certificate
section SelectedFactories
variable {function : Dynamic.Closure} {types : List TypeSystem.Ty} {context : SourceSemantics.Context}
  {before reached : Dynamic.Heap} {arguments : List Dynamic.Value} {environment : Dynamic.Environment}
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (allocated : Dynamic.BindersAllocate [] before function.parameters arguments environment reached)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments types)
include extended allocated beforeTyped argumentsTyped

/-- The actual named Source instantiation and whole-program validity derive
its complete body certificate internally at the actual parameter allocation. -/
theorem admission_at_named_parameters {instantiation : DeclarationInstantiation}
    (wellFormed : ProgramWellFormed program)
    (frame : NamedCalls.SourceFrame program instantiation body function) :
    Dynamic.SourceRuntimeValid program context function.source ∧ function.evidence.Covers context ∧
      Dynamic.HeapWellTyped context reached ∧ Dynamic.EnvironmentAgrees reached context.locals environment ∧
      ∃ actualFacts finalContext,
        StatementsHaveType function.source { returnType := function.resultType } context function.body finalContext actualFacts ∧
        BodyCompletes function.resultType actualFacts := by
  obtain ⟨sourceTypes, lexicalContext, actualFacts, certified⟩ := frame.instantiated.certificate wellFormed
  have actualExtension : MonoBindersExtend body.source.owner body.context body.source.inputs types context := by
    simpa only [frame.source, frame.context, frame.parameters] using extended
  have sameTypes : types = sourceTypes :=
    (Dynamic.MonoBindersExtend.bodyTypes_eq actualExtension).symm.trans
      (Dynamic.MonoBindersExtend.bodyTypes_eq certified.typing.inputs_extend)
  have view : CallableCoercionMethodFrame.Frame body function :=
    ⟨frame.source, frame.context, frame.parameters, frame.result, frame.captured, frame.roots, frame.covers⟩
  obtain ⟨runtime, covers, heapTyped, locals, finalContext, typed, completes⟩ :=
    admission_at_frame_parameters certified.toBodyInstanceTypingCertificate view extended allocated beforeTyped
      (sameTypes ▸ argumentsTyped)
  exact ⟨runtime, covers, heapTyped, locals, actualFacts, finalContext, typed, completes⟩

/-- The actual operator method selector supplies its original body certificate.
The full selected dictionary and Source substitution remain part of the view. -/
theorem admission_at_selected_method_parameters {callerContext : SourceSemantics.Context}
    {callerEvidence : Dynamic.EvidenceEnvironment} {traitName methodName : String} {requirements : List RequirementId}
    (wellFormed : ProgramWellFormed program)
    (selected : Dynamic.OperatorMethodSelected program callerContext callerEvidence traitName methodName requirements
      body function.evidence)
    (frame : CallableCoercionMethodFrame.Frame body function) :
    Dynamic.SourceRuntimeValid program context function.source ∧ function.evidence.Covers context ∧
      Dynamic.HeapWellTyped context reached ∧ Dynamic.EnvironmentAgrees reached context.locals environment ∧
      ∃ actualFacts finalContext,
        StatementsHaveType function.source { returnType := function.resultType } context function.body finalContext actualFacts ∧
        BodyCompletes function.resultType actualFacts := by
  obtain ⟨sourceTypes, lexicalContext, actualFacts, certified, _validity⟩ :=
    CallablePreparedMethodSelection.selected_typed selected wellFormed
  have actualExtension : MonoBindersExtend body.source.owner body.context body.source.inputs types context := by
    simpa only [frame.source, frame.context, frame.parameters] using extended
  have sameTypes : types = sourceTypes :=
    (Dynamic.MonoBindersExtend.bodyTypes_eq actualExtension).symm.trans
      (Dynamic.MonoBindersExtend.bodyTypes_eq certified.typing.inputs_extend)
  obtain ⟨runtime, covers, heapTyped, locals, finalContext, typed, completes⟩ :=
    admission_at_frame_parameters certified frame extended allocated beforeTyped (sameTypes ▸ argumentsTyped)
  exact ⟨runtime, covers, heapTyped, locals, actualFacts, finalContext, typed, completes⟩
end SelectedFactories

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodySourceAdmission
