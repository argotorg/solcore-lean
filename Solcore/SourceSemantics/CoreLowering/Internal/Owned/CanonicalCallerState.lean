import Solcore.SourceSemantics.CoreLowering.Internal.Owned.InvocationBounds
import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.FunctionCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedNamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeIndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaTyping
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateForPost

/-!
# Owned callables: canonical and physical caller state

The caller protocol, canonical and physical state, capture validity, lambda entries and body bounds.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodySourceAdmission
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCaptureValidity
/-! Raw Source capture validity accompanies the owned closure relation at its
actual heap. Formation obtains it from the original lexical environment; later
effects transport it using the same Source heap metadata extension. Projected
native typing does not supply Source cell declarations or generalized storage. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCaptureValidity
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues CallableIndexedLambdaValues

/-- The actual Source lambda captures copies of its caller's lexical
environment; the heap only grows. No child or body execution premise is
needed. -/
theorem captures_of_formation
    {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {statements : List StatementId} {requirements : List RequirementId}
    {coercions : List CoercionStep} {function : Dynamic.Closure}
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (evaluated : Dynamic.ExpressionFormEvaluates program context evidence source environment before
      (.lambda parameters result statements) requirements coercions (.closure function) after) :
    Dynamic.HeapMetadataExtend before after ∧ FunctionValues.SourceCapturesValid after (.closure function) := by
  cases evaluated with
  | lambda _ snapshot => exact ⟨snapshot.metadata_extends, snapshot.agrees locals⟩

/-- Source typing at the actual callee heap exposes the complete raw capture
scope, including generalized descriptors, independently of the native carrier. -/
theorem captures_of_source_typed
    {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {function : Dynamic.Closure} {parameter result : TypeSystem.Ty}
    (typed : Dynamic.ValueHasType context heap (.closure function) (.function parameter result)) :
    FunctionValues.SourceCapturesValid heap (.closure function) :=
  typed.closure_function_inv.2.2.2.2.2

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (Header compiled program)} {keys : List (Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
  {function : Dynamic.Closure} {native : Value} {type : Ty} {heap : Dynamic.Heap}

/-- These two receipts refer to the same complete Source closure. Ownership,
code, evidence and native captures stay in the original relation. -/
structure Valid where
  related : Represents headers keys registry faults mapping world sourceType (.closure function) native type
  captures : FunctionValues.SourceCapturesValid heap (.closure function)

theorem Valid.of_formation
    (related : Represents headers keys registry faults mapping world sourceType (.closure function) native type)
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before : Dynamic.Heap}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {requirements : List RequirementId} {coercions : List CoercionStep}
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (evaluated : Dynamic.ExpressionFormEvaluates program context evidence source environment before
      (.lambda parameters result statements) requirements coercions (.closure function) heap) :
    Valid (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := mapping) (world := world) (sourceType := sourceType) (function := function)
      (native := native) (type := type) (heap := heap) :=
  ⟨related, (captures_of_formation locals evaluated).2⟩

theorem Valid.of_source_typed
    (related : Represents headers keys registry faults mapping world sourceType (.closure function) native type)
    {context : SourceSemantics.Context} {parameter result : TypeSystem.Ty}
    (typed : Dynamic.ValueHasType context heap (.closure function) (.function parameter result)) :
    Valid (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := mapping) (world := world) (sourceType := sourceType) (function := function)
      (native := native) (type := type) (heap := heap) :=
  ⟨related, captures_of_source_typed typed⟩

theorem Valid.extend
    (valid : Valid (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := mapping) (world := world) (sourceType := sourceType) (function := function)
      (native := native) (type := type) (heap := heap))
    {futureMap : LocationMap} {futureWorld : StoreTyping} {futureHeap : Dynamic.Heap}
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (metadata : Dynamic.HeapMetadataExtend heap futureHeap) :
    Valid (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := futureMap) (world := futureWorld) (sourceType := sourceType) (function := function)
      (native := native) (type := type) (heap := futureHeap) := by
  refine ⟨?_, valid.captures.extend metadata⟩
  cases valid.related with
  | builtin prior => cases prior
  | lambda owner captured code history body origin globals referenceIndex typed =>
    exact .lambda owner (captured.extend maps worlds) code history body origin globals referenceIndex (typed.weaken worlds)

/-- Real Source validity and authentic static body support together imply
Source value typing. The entire original capture environment remains present. -/
theorem Valid.source_hasType
    (valid : Valid (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := mapping) (world := world) (sourceType := sourceType) (function := function)
      (native := native) (type := type) (heap := heap))
    {context : SourceSemantics.Context} (signatures : context.signatures = program.signatures) :
    Dynamic.ValueHasType context heap (.closure function) sourceType := by
  cases valid.related with
  | builtin prior => cases prior
  | lambda owner captured code history body origin globals referenceIndex typed =>
    have frame := body.2.2.receipt.body.frame
    exact .closure (frame.signatures.trans signatures.symm) frame.code frame.evidence_covers valid.captures

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCaptureValidity
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCaptureExecutionValidity
/-! A successful callee expression obtains raw Source capture validity from the
already proved whole Source preservation theorem. Its admission premises are
static Source typing and actual initial heap validity, with no child or body
execution law supplied by a compiler caller. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCaptureExecutionValidity
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues CallableIndexedOwnedCaptureValidity

variable {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : ExpressionId} {function : Dynamic.Closure} {parameter result : TypeSystem.Ty}

/-- Every successful Source callee form, including generalized local reads,
returns capture agreement at the actual callee heap under Source admission. -/
theorem captures_of_expression
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (typed : ExpressionHasType source context id (.function parameter result))
    (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment before
      id (.closure function) after) :
    FunctionValues.SourceCapturesValid after (.closure function) ∧
      Dynamic.HeapWellTyped context after ∧ Dynamic.HeapMetadataExtend before after := by
  have reached := wellFormed.wholeLanguagePreservation.expression context evidence source environment
    before after id (.closure function) (.function parameter result)
    runtime covers locals heapTyped typed evaluated
  exact ⟨captures_of_source_typed reached.value_typed, reached.heap_typed, reached.heap_extends⟩

/-- The Source preservation receipt is paired with the same actual owned
callee relation returned by Core correspondence, rather than a new carrier. -/
theorem valid_of_expression
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (Header compiled program)} {keys : List (Key compiled program)}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {native : Value} {type : Ty}
    (related : Represents headers keys registry faults mapping world sourceType (.closure function) native type)
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (typed : ExpressionHasType source context id (.function parameter result))
    (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment before
      id (.closure function) after) :
    Valid (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := mapping) (world := world) (sourceType := sourceType) (function := function)
      (native := native) (type := type) (heap := after) ∧
      Dynamic.HeapWellTyped context after ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨captures, reachedTyped, metadata⟩ :=
    captures_of_expression wellFormed runtime covers locals heapTyped typed evaluated
  exact ⟨⟨related, captures⟩, reachedTyped, metadata⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCaptureExecutionValidity
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaSourceAdmission
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
  have reached := Dynamic.BindersAllocate.preservesHeapTyping (beforeTyped.copy entry.entry.copy)
    (actualArguments.mono entry.entry.copy.metadata_extends) entry.entry.allocation
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaEntryBodyContracts
/-! The original raw lambda parameter receipts determine every operational
body field. The authentic ClosureFrame
is the sole extra field needed to reconstruct a Source call after reflection.
No StaticOrigin, escaped token, or completed body law is stored here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaEntryBodyContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)

/-- The function and input context already come from this exact Code. -/
structure BodyFields
    (code : Code compiled.indexed function scope captured.administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code) : Prop where
  frame : Dynamic.ClosureFrame program function

/-- Complete meaning at one actual Source-produced parameter receipt. The
body callback retains the original exit and the same actual reached pool. -/
def SourceAt
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩)
    (size : Nat) : Prop :=
  ∀ {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
    RecursiveNamedCallBounds.BodyTrace program size function inputs.context
      entry.entry.environment entry.entry.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.entry.actualBody entry.entry.store
        (code.receipt.body.rename entry.entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.entry.mapping finalMap ∧ WorldExtends entry.entry.world finalWorld ∧
      AdministrativePreserved entry.entry.mapping entry.entry.store finalMap finalStore ∧
      Dynamic.HeapMetadataExtend entry.entry.heap after ∧
      TypedMixedNamedBody.ReachedExit compiled.compatible.checked compiled.indexed.layouts.definitions
        finalMap finalWorld captured.administrative program function inputs.context
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
        entry.entry.environment entry.entry.heap after outcome ∧
      ProtectedStateTransition.Transition (protocol headers keys) reached
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          finalMap, finalWorld, after, finalStore, entry.entry.canonical⟩

/-- The native prefix is retained at its original strict grade. Source grade
and body outcome are reconstructed independently at that same entry. -/
def NativeAt
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (size : Nat) : Prop :=
  ∀ {value : Value} {finalStore : Store},
    EvaluationSize size entry.actual entry.store (code.receipt.body.rename entry.embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize function inputs.context
        entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧
      Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit compiled.compatible.checked compiled.indexed.layouts.definitions
        finalMap finalWorld captured.administrative program function inputs.context
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
        entry.environment entry.heap after outcome ∧
      ProtectedStateTransition.Transition (protocol headers keys) reached
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          finalMap, finalWorld, after, finalStore, entry.canonical⟩

/-- This intermediate contract is supplied by strict same-family body IH in
the final consumer; no uniform completed body law is asserted here. -/
def SourceContinuation (budget : Nat) : Prop :=
  ∀ (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment), added.length = code.receipt.loweredParameters.length →
  ∀ copied : Environment, entry.entry.canonical = added ++ copied →
    (∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?) →
  ∀ reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩,
    RecursiveNamedCatalogInvocationBounds.Below budget
      (SourceAt (faults := faults) captured code history inputs functions owner caller entry reached)

def NativeContinuation (budget : Nat) : Prop :=
  ∀ (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current),
  ∀ reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩,
    RecursiveNamedCatalogInvocationBounds.Below budget
      (NativeAt (faults := faults) captured code history inputs functions owner caller entry reached)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaEntryBodyContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaInvocationBounds
/-! Anonymous invocation uses the real selected pool row, its original caller
history and the full stored captures. Actual frame installation and marked
parameter allocation produce the reached pool consumed by the body. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames CallableIndexedOwnedFunctionState
open RecursiveNamedCatalogInvocationBounds (Below)

/-- The original static lambda body is aligned with its exact invocation
context, complete capture scope and emitted code. No execution is a field. -/
structure BodyOrigin {compiled : SourceCoreUnifiedCompilation.Compiled}
    {program : Program} {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} (code : Code compiled.indexed function scope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where
  origin : CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults
  frame : Dynamic.ClosureFrame program function
  function_eq : origin.function = function
  context_eq : origin.context = inputs.context
  administrative_eq : origin.administrative = administrative
  scope_eq : origin.scope = code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope
  frame_eq : origin.frameLayout = compiled.indexed.ancestry.layout.frame
  globals_eq : origin.globals = compiled.indexed.base.globals.length
  output_eq : origin.output = code.receipt.resultCore
  code_eq : origin.code = code.receipt.body

private theorem binders_context_eq {owner : Resolved.DeclarationId} {before left right : SourceSemantics.Context}
    {parameters : List TypedBinder} {leftTypes rightTypes : List TypeSystem.Ty}
    (first : MonoBindersExtend owner before parameters leftTypes left)
    (second : MonoBindersExtend owner before parameters rightTypes right) : left = right := by
  have same := first.bodyTypes_eq.symm.trans second.bodyTypes_eq
  subst rightTypes
  exact first.functional second

/-- The actual named lambda profile supplies every static alignment receipt. -/
def BodyOrigin.named {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (body : CallableIndexedLambdaNamedRuntimeBodyMeaning.Body (values := .initial compiled.compatible.checked)
      headers code program registry faults)
    (escaped : faults .controlEscapedFunction code.compilation.internalReason) :
    BodyOrigin (program := program) code inputs registry faults :=
  ⟨CallableRuntimeBodyStaticOrigins.lambda_named code body escaped, body.frame, rfl,
    binders_context_eq body.extended inputs.extended, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Ranked nested support retains the same dynamic function, evidence and
captured scope as its original body profile. -/
def BodyOrigin.nested {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {caller : CallableIndexedOwnedFunctionValues.Header compiled program} {rank : Nat}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (body : CallableIndexedLambdaNestedRuntimeBodyMeaning.Body (values := .initial compiled.compatible.checked)
      headers caller registry faults rank code)
    (escaped : faults .controlEscapedFunction code.compilation.internalReason) :
    BodyOrigin (program := program) code inputs registry faults :=
  ⟨CallableRuntimeBodyStaticOrigins.lambda_nested code body escaped, body.body.frame, rfl,
    binders_context_eq body.body.extended inputs.extended, rfl, rfl, rfl, rfl, rfl, rfl⟩

section Prefix
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)

include captured code history inputs functions represented caller heaps locals reference currentCarried allowed in
/-- The actual installed pool feeds the real marked prefix. The entire original
entry and capture spine accompany its reached pool. -/
theorem parameters_with_state :
    ∃ entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked) captured code history inputs functions registry arguments nativeArguments
      before store owner.key.frameLocation (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost,
    ∃ added copied : Environment, added.length = code.receipt.loweredParameters.length ∧
      entry.entry.canonical = added ++ copied ∧
      (∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?) ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩ := by
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  have read : store.read? owner.key.frameLocation =
      some (encode compiled.indexed.ancestry.layout.frame authority.current) := by
    simpa only [physical] using authority.frame.read
  have unmapped : owner.key.frameLocation ∉ mapping := by simpa only [physical] using authority.unmapped
  have nextHistory := ordinary_complete compiled.indexed.ancestry.graph history.carried currentCarried allowed
  let next := SourceCoreCallableIndexedDispatch.selectedFrame compiled.indexed.ancestry.graph.table
    code.descriptor.id history.native authority.current
  let producer := CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
  let installed := install caller owner.position (.stable nextHistory)
  let initial : State headers keys ⟨scope, mapping, world, before,
      store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame next), captured.canonical⟩ := installed
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary owner.key.frameLocation next :=
    CallableIndexedOwnedAllocationProducer.readyAt_of_stable_read
    (headers := headers) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    owner.position nextHistory
  obtain ⟨entry, added, copied, length, spine, slots, reached, parameterRelated⟩ :=
    CallableIndexedLambdaEntryPrefix.Stateful.entry_exists_for_with_spine (values := .initial compiled.compatible.checked) captured code history inputs functions
      (protocol headers keys) producer (administrativeTransport headers keys) (rebinds headers keys) represented heaps
      locals reference read currentCarried unmapped allowed initial readyAt
  have installedRelated : Relates caller initial := install_related caller owner.position (.stable nextHistory)
  exact ⟨entry, added, copied, length, spine, slots, reached, installedRelated.trans parameterRelated⟩

include captured code history inputs functions represented caller heaps locals reference currentCarried allowed in
/-- The original native lambda completion selects a strict body child and its
actual parameter pool. Its final store is the original frame restoration. -/
theorem body_prefix_with_state {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) result finalStore) :
    ∃ reached : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked) captured code history inputs functions registry arguments before store
        owner.key.frameLocation (caller.rows owner.position).authority.current,
    ∃ child bodyStore, child < size ∧ EvaluationSize child reached.actual reached.store
      (code.receipt.body.rename reached.embedding) result bodyStore ∧
      finalStore = bodyStore.set owner.key.frameLocation
        (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current) ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          reached.mapping, reached.world, reached.heap, reached.store, reached.canonical⟩ := by
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  have read : store.read? owner.key.frameLocation =
      some (encode compiled.indexed.ancestry.layout.frame authority.current) := by
    simpa only [physical] using authority.frame.read
  have unmapped : owner.key.frameLocation ∉ mapping := by simpa only [physical] using authority.unmapped
  have nextHistory := ordinary_complete compiled.indexed.ancestry.graph history.carried currentCarried allowed
  let next := SourceCoreCallableIndexedDispatch.selectedFrame compiled.indexed.ancestry.graph.table
    code.descriptor.id history.native authority.current
  let producer := CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
  let installed := install caller owner.position (.stable nextHistory)
  let initial : State headers keys ⟨scope, mapping, world, before,
      store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame next), captured.canonical⟩ := installed
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary owner.key.frameLocation next :=
    CallableIndexedOwnedAllocationProducer.readyAt_of_stable_read
    (headers := headers) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    owner.position nextHistory
  obtain ⟨reached, child, bodyStore, smaller, bodyCompleted, restored, post, parameterRelated⟩ :=
    CallableIndexedLambdaEntryBounds.Stateful.body_prefix_for (values := .initial compiled.compatible.checked) captured code history inputs functions
      represented heaps locals reference read currentCarried unmapped allowed
      (protocol headers keys) producer (administrativeTransport headers keys) (rebinds headers keys) initial readyAt
      completed
  have installedRelated : Relates caller initial := install_related caller owner.position (.stable nextHistory)
  exact ⟨reached, child, bodyStore, smaller, bodyCompleted, restored, post, installedRelated.trans parameterRelated⟩

include captured code history inputs functions represented caller heaps locals reference currentCarried allowed in
/-- Stored payload application adds its genuine strict apply edge while
retaining the same full captured environment and reached prefix pool. -/
theorem application_prefix_with_state {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments]
      store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ reached : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked) captured code history inputs functions registry arguments before store
        owner.key.frameLocation (caller.rows owner.position).authority.current,
    ∃ child bodyStore, child < size ∧ EvaluationSize child reached.actual reached.store
      (code.receipt.body.rename reached.embedding) result bodyStore ∧
      finalStore = bodyStore.set owner.key.frameLocation
        (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current) ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          reached.mapping, reached.world, reached.heap, reached.store, reached.canonical⟩ := by
  obtain ⟨bodySize, smaller, applied⟩ := completed.apply_body (.second (.first (.var rfl))) (.var rfl)
  obtain ⟨reached, child, bodyStore, childLess, evaluated, restored, transition⟩ :=
    body_prefix_with_state captured code history inputs functions represented owner caller heaps locals reference currentCarried allowed applied
  exact ⟨reached, child, bodyStore, Nat.lt_trans childLess smaller, evaluated, restored, transition⟩

variable {faults : FunctionCalls.FaultRep}
  (body : BodyOrigin (program := program) code inputs registry faults)

/-- Only original Source closure rules select this strict body child. The
independent monomorphic parameter receipt fixes its actual call context. -/
private theorem source_body {size : Nat} {callContext : SourceSemantics.Context}
    {callerEvidence : Dynamic.EvidenceEnvironment} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (arity : function.parameters.length = arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome program size callContext callerEvidence function.evidence before
      (.closure function) arguments outcome after) :
    ∃ child copies copied environment heap,
      Dynamic.EnvironmentCopies function.source function.captured before copies copied ∧
      Dynamic.BindersAllocate copies copied function.parameters arguments environment heap ∧
      RecursiveNamedCallBounds.BodyTrace program child function inputs.context environment heap outcome after ∧ child < size := by
  cases trace with
  | value executed =>
    cases executed with
    | closure _ _ extended copy allocated executed returned =>
      have same := binders_context_eq extended inputs.extended
      subst same
      subst returned
      exact ⟨_, _, _, _, _, copy, allocated, .returned executed, SourceExecutionSize.child_lt_stepSize (by simp)⟩
    | closureUnit _ _ resultUnit extended copy allocated executed fellThrough =>
      have same := binders_context_eq extended inputs.extended
      subst same
      obtain ⟨_, rfl⟩ := fellThrough
      exact ⟨_, _, _, _, _, copy, allocated, .unit resultUnit executed, SourceExecutionSize.child_lt_stepSize (by simp)⟩
  | fault failed =>
    cases failed with
    | notCallable invalid => exact False.elim (invalid trivial)
    | closureArity mismatch => exact False.elim (mismatch arity)
    | closureBody _ _ extended copy allocated failed =>
      have same := binders_context_eq extended inputs.extended
      subst same
      exact ⟨_, _, _, _, _, copy, allocated, .fault failed, SourceExecutionSize.child_lt_stepSize (by simp)⟩
    | closureControlEscape _ _ extended copy allocated executed escaped =>
      have same := binders_context_eq extended inputs.extended
      subst same
      exact ⟨_, _, _, _, _, copy, allocated, .escaped executed escaped, SourceExecutionSize.child_lt_stepSize (by simp)⟩

include inputs in
/-- Native reflection reconstructs the original four closure exit receipts at
its independent Source grade, using the authentic full parameter allocation. -/
private theorem call_of_body_with_frame (frame : Dynamic.ClosureFrame program function) {size : Nat} {callContext : SourceSemantics.Context}
    {callerEvidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {heap after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    {copies : Dynamic.Environment} {copied : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies function.source function.captured before copies copied)
    (allocated : Dynamic.BindersAllocate copies copied function.parameters arguments environment heap)
    (trace : RecursiveNamedCallBounds.BodyTrace program size function inputs.context environment heap outcome after) :
    RecursiveNamedCallBounds.CallOutcome program (SourceExecutionSize.stepSize [size]) callContext callerEvidence function.evidence before
      (.closure function) arguments outcome after := by
  cases trace with
  | returned executed => exact .value (.closure rfl frame inputs.extended copy allocated executed rfl)
  | unit same executed => exact .value (.closureUnit rfl frame same inputs.extended copy allocated executed ⟨_, rfl⟩)
  | fault failed => exact .fault (.closureBody rfl frame inputs.extended copy allocated failed)
  | escaped executed escape => exact .fault (.closureControlEscape rfl frame inputs.extended copy allocated executed escape)


include body in
/-- Native reflection reconstructs the original four closure exit receipts at
its independent Source grade, using the authentic full parameter allocation. -/
private theorem call_of_body {size : Nat} {callContext : SourceSemantics.Context}
    {callerEvidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {heap after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    {copies : Dynamic.Environment} {copied : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies function.source function.captured before copies copied)
    (allocated : Dynamic.BindersAllocate copies copied function.parameters arguments environment heap)
    (trace : RecursiveNamedCallBounds.BodyTrace program size function inputs.context environment heap outcome after) :
    RecursiveNamedCallBounds.CallOutcome program (SourceExecutionSize.stepSize [size]) callContext callerEvidence function.evidence before
      (.closure function) arguments outcome after := by
  exact call_of_body_with_frame captured code inputs body.frame copy allocated trace

/-- The source-produced entry is packaged without changing its reached pool,
captured canonical spine or selected physical frame. -/
def source_entry
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    CallableRuntimeBodyOrigins.Stateful.Entry (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) body.origin functions where
  mapping := entry.entry.mapping
  world := entry.entry.world
  environment := entry.entry.environment
  canonical := entry.entry.canonical
  actual := entry.entry.actualBody
  heap := entry.entry.heap
  store := entry.entry.store
  embedding := entry.entry.embedding
  actualContext := CallableIndexedParameterTyped.prefixContext code.receipt.loweredParameters entry.entry.copiedContext
  frameLocation := owner.key.frameLocation
  native := entry.next
  environments := by simpa only [body.administrative_eq, body.scope_eq, CallableIndexedAmbient.ambientDefinitions] using entry.entry.environments
  heaps := entry.entry.heaps
  locals := by simpa only [body.context_eq] using entry.entry.locals
  lookups := entry.entry.lookups
  actualTyped := entry.entry.actualTyped
  reference := by simpa only [body.scope_eq, body.globals_eq, body.frame_eq] using entry.entry.reference
  read := by simpa only [body.frame_eq] using entry.entry.read
  unmapped := entry.entry.unmapped
  initial := reached
  gate := ⟨owner.position, _, _, rfl, entry.nextHistory⟩

/-- The measured native prefix has its own actual environment and pool. Its
packaging preserves those witnesses rather than selecting an older entry. -/
def native_entry
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableRuntimeBodyOrigins.Stateful.Entry (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) body.origin functions where
  mapping := entry.mapping
  world := entry.world
  environment := entry.environment
  canonical := entry.canonical
  actual := entry.actual
  heap := entry.heap
  store := entry.store
  embedding := entry.embedding
  actualContext := entry.actualContext
  frameLocation := owner.key.frameLocation
  native := entry.next
  environments := by simpa only [body.administrative_eq, body.scope_eq, CallableIndexedAmbient.ambientDefinitions] using entry.environments
  heaps := entry.heaps
  locals := by simpa only [body.context_eq] using entry.locals
  lookups := entry.lookups
  actualTyped := entry.actualTyped
  reference := by simpa only [body.scope_eq, body.globals_eq, body.frame_eq] using entry.reference
  read := by simpa only [body.frame_eq] using entry.read
  unmapped := entry.unmapped
  initial := reached
  gate := ⟨owner.position, _, _, rfl, entry.nextHistory⟩


/-- The strict source body callback sees the real complete parameter entry,
its authentic canonical spine and the actual reached pool. -/
def SourceContinuation (budget : Nat) : Prop :=
  ∀ (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment), added.length = code.receipt.loweredParameters.length →
  ∀ copied : Environment, entry.entry.canonical = added ++ copied →
    (∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?) →
  ∀ reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩,
    Below budget (CallableRuntimeBodyEntryContracts.PreservesAt
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (protocol := protocol headers keys)
      (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin := body.origin) functions program
      (source_entry captured code history inputs functions owner caller body entry reached))

/-- The original native prefix already retains its full canonical spine.
The callback consumes that exact prefix and its actual reached pool. -/
def NativeContinuation (budget : Nat) : Prop :=
  ∀ (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩),
    Below budget (CallableRuntimeBodyEntryContracts.ReflectsAt
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (protocol := protocol headers keys)
      (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin := body.origin) functions program
      (native_entry captured code history inputs functions owner caller body entry reached))

include inputs represented heaps locals reference currentCarried allowed in
/-- The original strict Source child is proved by the shared actual body
family, then the saved caller frame is restored in that exact reached pool. -/
theorem invocation_preserves_bounded_at_with_continuation (budget : Nat)
    (bodyMeaning : CallableIndexedOwnedLambdaEntryBodyContracts.SourceContinuation (arguments := arguments) (nativeArguments := nativeArguments)
      (registry := registry) (faults := faults) captured code history inputs functions owner caller budget)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome program size callContext callerEvidence function.evidence before
      (.closure function) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: capturedActual)
        store (code.body.rename captured.embedding.lift.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  have arity : function.parameters.length = arguments.length := by
    rw [CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code, List.length_map]
    exact represented.length.1
  obtain ⟨child, copies, copied, environment, bound, copy, allocated, bodyTrace, smaller⟩ :=
    source_body captured code inputs arity trace
  obtain ⟨entry, added, copiedCanonical, length, spine, slots, parameterState, parameterRelated⟩ :=
    parameters_with_state captured code history inputs functions represented owner caller heaps locals reference currentCarried allowed
  obtain ⟨sameCopies, sameCopied⟩ := Dynamic.EnvironmentCopies.functional entry.entry.copy copy
  rw [← sameCopies, ← sameCopied] at allocated
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  obtain ⟨value, bodyStore, finalMap, finalWorld, originalBody, representedResult, finalHeaps,
      bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, _exit, bodyState, bodyRelated⟩ :=
    bodyMeaning entry added length copiedCanonical spine slots parameterState child (Nat.lt_of_lt_of_le smaller within)
      bodyTrace
  have maps := entry.entry.maps.trans bodyMaps
  have worlds := entry.entry.worlds.trans bodyWorlds
  have frame := entry.entry.frame.trans bodyFrame
  have sourceMetadata := entry.entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := parameterRelated.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, _bodyRelated, _callerRelated, _records, returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position
      (CallableIndexedAmbient.frame_registered compiled.indexed) finalHeaps worlds frame related
  exact ⟨value, _, finalMap, finalWorld, entry.wrap originalBody, representedResult,
    restoredHeaps, maps, worlds, restoredFrame, sourceMetadata, returned⟩


include body inputs represented heaps locals reference currentCarried allowed in
/-- The original strict Source child is proved by the shared actual body
family, then the saved caller frame is restored in that exact reached pool. -/
theorem invocation_preserves_bounded_at (budget : Nat)
    (bodyMeaning : SourceContinuation (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history inputs functions owner caller body budget)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome program size callContext callerEvidence function.evidence before
      (.closure function) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: capturedActual)
        store (code.body.rename captured.embedding.lift.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  apply invocation_preserves_bounded_at_with_continuation captured code history inputs functions represented
    owner caller heaps locals reference currentCarried allowed budget
  · intro entry added length copiedCanonical spine slots reached child strict outcome after trace
    have actualTrace : RecursiveNamedCallBounds.BodyTrace program child body.origin.function body.origin.context
        (source_entry captured code history inputs functions owner caller body entry reached).environment
        (source_entry captured code history inputs functions owner caller body entry reached).heap outcome after := by
      simpa only [body.function_eq, body.context_eq, source_entry] using trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps,
        maps, worlds, frame, metadata, exit, finalState, related⟩ :=
      bodyMeaning entry added length copiedCanonical spine slots reached child strict actualTrace
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, metadata, ?_, ?_⟩
    · simpa only [body.code_eq, source_entry] using evaluated
    · simpa only [body.function_eq, body.output_eq, SourceCoreCompatibleValues.Context.initial] using result
    · simpa only [body.administrative_eq, body.function_eq, body.context_eq, body.scope_eq, source_entry,
        CallableIndexedAmbient.ambientDefinitions, SourceCoreCompatibleValues.Context.initial] using exit
    · simpa only [body.scope_eq, source_entry] using (show ProtectedStateTransition.Transition (protocol headers keys)
        reached ⟨body.origin.scope, finalMap, finalWorld, after, finalStore,
          (source_entry captured code history inputs functions owner caller body entry reached).canonical⟩ from ⟨finalState, related⟩)
  · exact trace
  · exact within

include inputs represented heaps locals reference currentCarried allowed in
/-- The original native completion exposes a strict body child. Its actual
post pool is restored, while the Source call grade is reconstructed separately. -/
theorem invocation_reflects_bounded_at_with_continuation
    (frame : Dynamic.ClosureFrame program function) (budget : Nat)
    (bodyMeaning : CallableIndexedOwnedLambdaEntryBodyContracts.NativeContinuation (arguments := arguments)
      (registry := registry) (faults := faults) captured code history inputs functions owner caller budget)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome program sourceSize callContext callerEvidence function.evidence before
        (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  obtain ⟨entry, child, bodyStore, smaller, bodyCompleted, restored, parameterState, parameterRelated⟩ :=
    body_prefix_with_state captured code history inputs functions represented owner caller heaps locals reference currentCarried allowed completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, originalTrace, representedResult, finalHeaps,
      bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, _exit, bodyState, bodyRelated⟩ :=
    bodyMeaning entry parameterState child (Nat.lt_of_lt_of_le smaller within) bodyCompleted
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have administrativeFrame := entry.frame.trans bodyFrame
  have sourceMetadata := entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := parameterRelated.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, _bodyRelated, _callerRelated, _records, returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position
      (CallableIndexedAmbient.frame_registered compiled.indexed) finalHeaps worlds administrativeFrame related
  subst finalStore
  exact ⟨_, outcome, after, finalMap, finalWorld,
    call_of_body_with_frame captured code inputs frame entry.copy entry.allocation originalTrace,
    representedResult, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata, returned⟩


include body inputs represented heaps locals reference currentCarried allowed in
/-- The original native completion exposes a strict body child. Its actual
post pool is restored, while the Source call grade is reconstructed separately. -/
theorem invocation_reflects_bounded_at (budget : Nat)
    (bodyMeaning : NativeContinuation (arguments := arguments) captured code history inputs functions owner caller body budget)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome program sourceSize callContext callerEvidence function.evidence before
        (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  apply invocation_reflects_bounded_at_with_continuation captured code history inputs functions represented
    owner caller heaps locals reference currentCarried allowed body.frame budget
  · intro entry reached child strict value finalStore completed
    have actualCompleted : EvaluationSize child
        (native_entry captured code history inputs functions owner caller body entry reached).actual
        (native_entry captured code history inputs functions owner caller body entry reached).store
        (body.origin.code.rename
          (native_entry captured code history inputs functions owner caller body entry reached).embedding) value finalStore := by
      simpa only [body.code_eq, native_entry] using completed
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
        maps, worlds, frame, metadata, exit, finalState, related⟩ :=
      bodyMeaning entry reached child strict actualCompleted
    refine ⟨sourceSize, outcome, after, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, metadata, ?_, ?_⟩
    · simpa only [body.function_eq, body.context_eq, native_entry] using trace
    · simpa only [body.function_eq, body.output_eq, SourceCoreCompatibleValues.Context.initial] using result
    · simpa only [body.administrative_eq, body.function_eq, body.context_eq, body.scope_eq, native_entry,
        CallableIndexedAmbient.ambientDefinitions, SourceCoreCompatibleValues.Context.initial] using exit
    · simpa only [body.scope_eq, native_entry] using (show ProtectedStateTransition.Transition (protocol headers keys)
        reached ⟨body.origin.scope, finalMap, finalWorld, after, finalStore,
          (native_entry captured code history inputs functions owner caller body entry reached).canonical⟩ from ⟨finalState, related⟩)
  · exact completed
  · exact within

include body inputs represented heaps locals reference currentCarried allowed in
/-- The original strict Source child is proved by the shared actual body
family, then the saved caller frame is restored in that exact reached pool. -/
theorem invocation_preserves_bounded_with (budget : Nat)
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program body.origin))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome program size callContext callerEvidence function.evidence before
      (.closure function) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: capturedActual)
        store (code.body.rename captured.embedding.lift.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  exact invocation_preserves_bounded_at captured code history inputs functions represented owner caller heaps locals
    reference currentCarried allowed body budget
    (fun entry _added _length _copied _spine _kept reached child strict =>
      bodyMeaning child strict (source_entry captured code history inputs functions owner caller body entry reached)) trace within

include body inputs represented heaps locals reference currentCarried allowed in
/-- The original native completion exposes a strict body child. Its actual
post pool is restored, while the Source call grade is reconstructed separately. -/
theorem invocation_reflects_bounded_with (budget : Nat)
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program body.origin))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome program sourceSize callContext callerEvidence function.evidence before
        (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  exact invocation_reflects_bounded_at captured code history inputs functions represented owner caller heaps locals
    reference currentCarried allowed body budget
    (fun entry reached child strict =>
      bodyMeaning child strict (native_entry captured code history inputs functions owner caller body entry reached)) completed within


include body inputs represented heaps locals reference currentCarried allowed in
/-- Applying the authentic stored lambda payload retains the same actual
parameter/body pool and saved caller restoration. -/
theorem application_preserves_bounded_with (budget : Nat)
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program body.origin))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome program size callContext callerEvidence function.evidence before
      (.closure function) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
    invocation_preserves_bounded_with captured code history inputs functions represented owner caller heaps locals
      reference currentCarried allowed body budget bodyMeaning trace within
  exact ⟨value, finalStore, finalMap, finalWorld,
    .apply (.second (.first (.var rfl))) (.var rfl) evaluated, result, finalHeaps, maps, worlds, frame, metadata, transition⟩

include body inputs represented heaps locals reference currentCarried allowed in
/-- The real apply edge keeps native decrease separate from the independently
reconstructed Source call grade and its actual returned pool. -/
theorem application_reflects_bounded_with (budget : Nat)
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program body.origin))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome program sourceSize callContext callerEvidence function.evidence before
        (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  obtain ⟨bodySize, smaller, applied⟩ := completed.apply_body (.second (.first (.var rfl))) (.var rfl)
  exact invocation_reflects_bounded_with captured code history inputs functions represented owner caller heaps locals
    reference currentCarried allowed body budget bodyMeaning applied (Nat.le_trans (Nat.le_of_lt smaller) within)

include body inputs represented heaps locals reference currentCarried allowed in
/-- Applying the authentic stored lambda payload retains the same actual
parameter/body pool and saved caller restoration. -/
theorem application_preserves_bounded_at (budget : Nat)
    (bodyMeaning : SourceContinuation (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history inputs functions owner caller body budget)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome program size callContext callerEvidence function.evidence before
      (.closure function) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
    invocation_preserves_bounded_at captured code history inputs functions represented owner caller heaps locals
      reference currentCarried allowed body budget bodyMeaning trace within
  exact ⟨value, finalStore, finalMap, finalWorld,
    .apply (.second (.first (.var rfl))) (.var rfl) evaluated, result, finalHeaps, maps, worlds, frame, metadata, transition⟩

include body inputs represented heaps locals reference currentCarried allowed in
/-- The real apply edge keeps native decrease separate from the independently
reconstructed Source call grade and its actual returned pool. -/
theorem application_reflects_bounded_at (budget : Nat)
    (bodyMeaning : NativeContinuation (arguments := arguments) captured code history inputs functions owner caller body budget)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome program sourceSize callContext callerEvidence function.evidence before
        (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  obtain ⟨bodySize, smaller, applied⟩ := completed.apply_body (.second (.first (.var rfl))) (.var rfl)
  exact invocation_reflects_bounded_at captured code history inputs functions represented owner caller heaps locals
    reference currentCarried allowed body budget bodyMeaning applied (Nat.le_trans (Nat.le_of_lt smaller) within)

end Prefix

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaInvocationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCanonicalState
/-! Original canonical global slots accompany the actual owned pool through
lexical allocation and scope restoration. The wrapper adds a proof only;
its complete ordered records and actual row transitions remain unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCanonicalState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedExpressionHeads (Globals argumentProtocol)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat)

/-- Prepending a real lexical slot shifts every original global by one. -/
theorem globals_prepend {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (globals : Globals (headers := headers) owner callerPrefix scope canonical)
    (id : Resolved.LocalId) (type : Ty) (value : Value) :
    Globals (headers := headers) owner callerPrefix ((id, type) :: scope) (value :: canonical) := by
  intro header member
  have offset : ((id, type) :: scope).length + callerPrefix + header.slot =
      scope.length + callerPrefix + header.slot + 1 := by simp; omega
  rw [offset]
  exact globals header member

/-- Removing that same lexical slot restores its exact original global index. -/
theorem globals_restore {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {id : Resolved.LocalId} {type : Ty} {value : Value}
    (globals : Globals (headers := headers) owner callerPrefix ((id, type) :: scope) (value :: canonical)) :
    Globals (headers := headers) owner callerPrefix scope canonical := by
  intro header member
  have slot := globals header member
  have offset : ((id, type) :: scope).length + callerPrefix + header.slot =
      scope.length + callerPrefix + header.slot + 1 := by simp; omega
  rw [offset] at slot
  exact slot

def administrativeTransport :
    ProtectedStateTransition.AdministrativeTransport (argumentProtocol (headers := headers) owner callerPrefix) where
  extend := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata =>
    ⟨(CallableIndexedOwnedFunctionState.administrativeTransport headers keys).extend state.val maps worlds frame metadata,
      state.property⟩
  related := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata =>
    (CallableIndexedOwnedFunctionState.administrativeTransport headers keys).related state.val maps worlds frame metadata
  records_eq := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata =>
    (CallableIndexedOwnedFunctionState.administrativeTransport headers keys).records_eq state.val maps worlds frame metadata

def bindings : ProtectedStateTransition.Bindings (argumentProtocol (headers := headers) owner callerPrefix) where
  prepend := fun state id type value =>
    ⟨(CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).prepend state.val id type value,
      globals_prepend owner callerPrefix state.property id type value⟩
  prepend_related := fun state id type value =>
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).prepend_related state.val id type value
  prepend_records := fun state id type value =>
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).prepend_records state.val id type value
  restore := fun state =>
    ⟨(CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore state.val,
      globals_restore owner callerPrefix state.property⟩
  restore_related := fun state =>
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore_related state.val
  restore_records := fun state =>
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore_records state.val

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)

/-- The real marked allocator returns its actual reached row pool. The added
slot proof describes the canonical reference prepended by that same receipt. -/
def markedProducer :
    ProtectedStateTransition.MarkedAllocation.Producer (argumentProtocol (headers := headers) owner callerPrefix)
      compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model where
  Ready := fun state location native =>
    (CallableIndexedOwnedMarkedAllocation.producer headers keys model).Ready state.val location native
  complete := by
    intro allocationOwner active request globals allocate allocation annotation same definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native sourceType payload sourceValue sourceLocation
      environments agrees heaps reference read payloadAt cell allocated initial ready
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame, transition⟩ :=
      (CallableIndexedOwnedMarkedAllocation.producer headers keys model).complete allocation annotation same definitions registered
        environments agrees heaps reference read payloadAt cell allocated initial.val ready
    obtain ⟨reached, related⟩ := transition
    exact ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame,
      ⟨⟨reached, globals_prepend owner callerPrefix initial.property request.binder.id request.payloadType
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))⟩, related⟩⟩

/-- Allocation readiness comes from the physical owner and authentic history;
the canonical-slot proof supplies no capture or snapshot authority. -/
theorem readyAt_of_stableOwner {location : Location} {native : NativeFrame}
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      (markedProducer (headers := headers) owner callerPrefix model).toOrdinary location native := by
  intro index state read
  exact CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner (headers := headers) model stable state.val read

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCanonicalState
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyCanonicalEntries
/-! An authentic canonical-slot packet wraps one complete actual body entry.
Only that proof is forgotten at the returned pool; every original semantic
field and the exact actual initial/post witnesses remain intact. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyCanonicalEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedExpressionHeads
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat)
  {conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop}
  {origin : CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults}
  (entry : CallableRuntimeBodyOrigins.Stateful.Entry (protocol headers keys) conditionGate origin functions)
  (globals : Globals (headers := headers) owner callerPrefix origin.scope entry.canonical)

/-- The same original entry, with genuine canonical slots beside its actual pool. -/
def wrap : CallableRuntimeBodyOrigins.Stateful.Entry
    (argumentProtocol (headers := headers) owner callerPrefix) conditionGate origin functions :=
  { entry with initial := ⟨entry.initial, globals⟩ }

/-- The actual wrapped body post supplies the same complete base pool. -/
theorem preserves_of_canonical {size : Nat}
    (meaning : CallableRuntimeBodyEntryContracts.PreservesAt
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (protocol := argumentProtocol (headers := headers) owner callerPrefix)
      (conditionGate := conditionGate) (origin := origin) functions program
      (wrap functions owner callerPrefix entry globals) size) :
    CallableRuntimeBodyEntryContracts.PreservesAt
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (protocol := protocol headers keys) (conditionGate := conditionGate) (origin := origin)
      functions program entry size := by
  intro outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
    frame, metadata, exit, returned, related⟩ := meaning trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

/-- Native completion retains its independent Source grade and actual post pool. -/
theorem reflects_of_canonical {size : Nat}
    (meaning : CallableRuntimeBodyEntryContracts.ReflectsAt
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (protocol := argumentProtocol (headers := headers) owner callerPrefix)
      (conditionGate := conditionGate) (origin := origin) functions program
      (wrap functions owner callerPrefix entry globals) size) :
    CallableRuntimeBodyEntryContracts.ReflectsAt
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (protocol := protocol headers keys) (conditionGate := conditionGate) (origin := origin)
      functions program entry size := by
  intro value finalStore completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds,
    frame, metadata, exit, returned, related⟩ := meaning completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyCanonicalEntries
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaCanonicalEntries
/-! The real lambda parameter spine carries original captured global slots
into one actual canonical body entry. The reached pool is wrapped verbatim;
no old catalog authority or unrelated body entry is selected. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaCanonicalEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedExpressionHeads
open RecursiveNamedCatalogInvocationBounds (Below)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := program)
    headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation)

include observed in
/-- Ordered real parameter additions shift scope and captures by exactly the
same length; the copies keep every slot past the scope, so every original
selected named slot is preserved. -/
theorem globals_after_prefix {canonical : Environment} (added : Environment)
    (length : added.length = code.receipt.loweredParameters.length) (copied : Environment)
    (spine : canonical = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?) :
    Globals (headers := headers) owner callerPrefix
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) canonical := by
  intro header member
  rw [spine]
  simp only [List.length_append, List.length_map, List.length_reverse]
  have index : code.receipt.loweredParameters.length + scope.length + callerPrefix + header.slot =
      added.length + (scope.length + callerPrefix + header.slot) := by omega
  rw [index, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, kept _ (by omega)]
  simpa using observed.globals header member

variable (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (body : CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin (program := program) code inputs registry faults)

include observed in
/-- The actual source parameter entry receives only the authentic slot proof. -/
def source_entry
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    CallableRuntimeBodyOrigins.Stateful.Entry (argumentProtocol (headers := headers) owner callerPrefix)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) body.origin functions :=
  CallableIndexedOwnedBodyCanonicalEntries.wrap functions owner callerPrefix
    (CallableIndexedOwnedLambdaInvocationBounds.source_entry captured code history inputs functions owner caller body entry reached)
    (by simpa only [body.scope_eq, CallableIndexedOwnedLambdaInvocationBounds.source_entry] using globals_after_prefix captured code owner callerPrefix observed added length copied spine kept)

include observed in
/-- Native reflection uses the full spine already retained by its actual prefix. -/
def native_entry
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableRuntimeBodyOrigins.Stateful.Entry (argumentProtocol (headers := headers) owner callerPrefix)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) body.origin functions :=
  CallableIndexedOwnedBodyCanonicalEntries.wrap functions owner callerPrefix
    (CallableIndexedOwnedLambdaInvocationBounds.native_entry captured code history inputs functions owner caller body entry reached)
    (by
      obtain ⟨added, copied, length, spine, kept⟩ := entry.spine
      simpa only [body.scope_eq, CallableIndexedOwnedLambdaInvocationBounds.native_entry] using
        globals_after_prefix captured code owner callerPrefix observed added length copied spine kept)

/-- A strict canonical family is specialized to the exact source-produced
entry, then only its proof wrapper is forgotten at the actual body post. -/
theorem source_continuation_of_canonical (budget : Nat)
    (meaning : ∀ (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
        captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
        (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
      (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
      (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
      (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
      (reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩),
      Below budget (CallableRuntimeBodyEntryContracts.PreservesAt
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (protocol := argumentProtocol (headers := headers) owner callerPrefix)
        (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys) (origin := body.origin)
        functions program (source_entry captured code owner callerPrefix observed history inputs functions caller body
          entry added length copied spine kept reached))) :
    CallableIndexedOwnedLambdaInvocationBounds.SourceContinuation (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history inputs functions owner caller body budget := by
  intro entry added length copied spine kept reached child strict
  exact CallableIndexedOwnedBodyCanonicalEntries.preserves_of_canonical functions owner callerPrefix
    (CallableIndexedOwnedLambdaInvocationBounds.source_entry captured code history inputs functions owner caller body entry reached)
    _ (meaning entry added length copied spine kept reached child strict)

/-- The original independently measured native prefix feeds its own canonical
family entry and receives the same base pool after the actual body. -/
theorem native_continuation_of_canonical (budget : Nat)
    (meaning : ∀ (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
        captured code history inputs functions registry arguments before store owner.key.frameLocation
        (caller.rows owner.position).authority.current)
      (reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩),
      Below budget (CallableRuntimeBodyEntryContracts.ReflectsAt
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (protocol := argumentProtocol (headers := headers) owner callerPrefix)
        (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys) (origin := body.origin)
        functions program (native_entry captured code owner callerPrefix observed history inputs functions caller body entry reached))) :
    CallableIndexedOwnedLambdaInvocationBounds.NativeContinuation (arguments := arguments)
      captured code history inputs functions owner caller body budget := by
  intro entry reached child strict
  exact CallableIndexedOwnedBodyCanonicalEntries.reflects_of_canonical functions owner callerPrefix
    (CallableIndexedOwnedLambdaInvocationBounds.native_entry captured code history inputs functions owner caller body entry reached)
    _ (meaning entry reached child strict)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaCanonicalEntries
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCallerProtocol
/-! Caller protocols expose the same actual full pool, and wrap an actual
returned pool only at the unchanged caller scope and canonical environment.
Record equality prevents replacement of any reached row or ordered history. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCallerProtocol
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedExpressionHeads
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

/-- A concrete caller wrapper changes neither its full pool nor records. Its
return operation wraps the actual post at the original scope/canonical only. -/
structure Carrier (caller : ProtectedStateTransition.Protocol.{u, 0} (Records keys)) where
  pool : ∀ {index}, caller.State index → State headers keys index
  records_eq : ∀ {index} (state : caller.State index), caller.records state = records (pool state)
  related : ∀ {initial reached} {first : caller.State initial} {last : caller.State reached},
    caller.Relates first last → Relates (pool first) (pool last)
  of_pool : ∀ {index} (_initial : caller.State index) {mapping world heap store},
    State headers keys (index.extend mapping world heap store) → caller.State (index.extend mapping world heap store)
  pool_of_pool : ∀ {index} (initial : caller.State index) {mapping world heap store}
    (reached : State headers keys (index.extend mapping world heap store)), pool (of_pool initial reached) = reached
  return_related : ∀ {index} (initial : caller.State index) {mapping world heap store}
    (reached : State headers keys (index.extend mapping world heap store)),
    Relates (pool initial) reached → caller.Relates initial (of_pool initial reached)

def base : Carrier (headers := headers) (protocol headers keys) where
  pool := fun state => state
  records_eq := fun _ => rfl
  related := fun related => related
  of_pool := fun {_index} _initial {_mapping _world _heap _store} reached => reached
  pool_of_pool := fun {_index} _initial {_mapping _world _heap _store} _reached => rfl
  return_related := fun {_index} _initial {_mapping _world _heap _store} _reached related => related

/-- Canonical slots come from this caller's original authentic packet. The
selected closure's captured slots belong to a separate body protocol. -/
def canonical (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat) :
    Carrier (headers := headers) (argumentProtocol (headers := headers) owner callerPrefix) where
  pool := fun state => state.val
  records_eq := fun _ => rfl
  related := fun related => related
  of_pool := fun {_index} initial {_mapping _world _heap _store} reached => ⟨reached, initial.property⟩
  pool_of_pool := fun {_index} _initial {_mapping _world _heap _store} _reached => rfl
  return_related := fun {_index} _initial {_mapping _world _heap _store} _reached related => related

/-- Returning wraps the same ordered records at every row, including duplicates. -/
theorem Carrier.returned_records {caller : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (carrier : Carrier (headers := headers) caller)
    {index : ProtectedStateTransition.Index} (initial : caller.State index) {mapping world heap store}
    (reached : State headers keys (index.extend mapping world heap store)) :
    caller.records (carrier.of_pool initial reached) = records reached :=
  (carrier.records_eq _).trans (congrArg (fun state => records state) (carrier.pool_of_pool initial reached))

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCallerProtocol
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSupport
/-! Genuine ordinary lambda support retains its actual cached Header and
accepted Site beside unrestricted same-Code static body receipts. The full
Source frame, compiler Trees, contexts and diagnostic sites stay original.
The ranked ordinary relation and every existing function model stay unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}

/-- An authentic cached Header accompanies the exact accepted lambda Code.
The expression grammar remains the genuine static body grammar supplied here. -/
structure Support (code : Code compiled.indexed function scope administrative)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where
  caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)
  expressionSyntax : TypedSource → ExpressionId → Prop
  certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate
  source : function.source = CallableIndexedNamedGeneration.source caller.named
  compilation : code.compilation = CallableIndexedNamedGeneration.context compiled.indexed caller.named
  active : code.active = []
  body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked) expressionSyntax certificates
    code (Program.ofChecked compiled.sourceProgram) registry faults

variable
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
  (site : CallableIndexedLambdaGeneration.Site compiled.indexed caller.named parameters result statements
    context evidence environment scope administrative)

/-- The real Site and complete same-Code body construct support directly.
The independently established Source frame is retained verbatim. -/
def Support.of_site {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked) expressionSyntax certificates
      site.code (Program.ofChecked compiled.sourceProgram) registry faults) :
    Support site.code registry faults :=
  ⟨caller, expressionSyntax, certificates, rfl, site.compilation, site.active, body⟩

variable {code : Code compiled.indexed function scope administrative}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (support : Support code registry faults)

include support in
/-- Source attribution is derived from the actual cached Header record. -/
theorem Support.source_receipt :
    LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source := by
  rw [support.compilation, support.active, support.source]
  exact .original (CallableIndexedActualNamedSourceReceipts.header_record compiled support.caller)

include support in
/-- The original static body retains uniqueness of this complete Source. -/
theorem Support.unique : NodeOccurrencesUnique function.source := support.body.unique

/-- Changing only the stored actual capture environment retains every same-Code
static receipt, including its original Source frame and body diagnostics. -/
def Support.recapture (environment : Dynamic.Environment) :
    Support (RecursiveNamedLambdaFormationHeads.recaptureCode
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) code environment) registry faults where
  caller := support.caller
  expressionSyntax := support.expressionSyntax
  certificates := support.certificates
  source := support.source
  compilation := support.compilation
  active := support.active
  body := RecursiveNamedLambdaFormationHeads.recaptureBodyWith
    (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) code support.body environment

/-- Captured history retains the complete actual named compiler seed. -/
structure SourceOrigin (history : History code) : Prop where
  metadata : history.metadata = CallableIndexedNamedGeneration.state support.caller.named

/-- The actual selected named hook constructs the original full Source seed. -/
theorem Support.of_site_origin
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked) expressionSyntax certificates
      site.code (Program.ofChecked compiled.sourceProgram) registry faults)
    {hook : Word}
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named caller.named.signature.key) = some hook) :
    SourceOrigin (Support.of_site caller site expressionSyntax certificates body)
      (site.historyAt selected (CallableIndexedActualNamedSourceReceipts.header_record compiled caller)) := ⟨rfl⟩

/-- The original stage descriptor authenticates the same actual lambda payload.
Source attribution is derived from support; captures and history remain real. -/
theorem Support.stage_origin {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
    (captured : Captures compiled.indexed mapping world scope function.captured actual)
    (actualCode : Code compiled.indexed function scope captured.administrative)
    (actualSupport : Support actualCode registry faults) (history : History actualCode) :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      (.closure function) (value actualCode captured.embedding history.native actual) := by
  have prepared := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  exact CompatibleAmbientStageOrigins.actual_lambda_origin prepared.accepted actualCode.descriptor
    actualSupport.source_receipt actualCode.viewOfSource actualSupport.unique actualCode.found
    (actualCode.form.trans actualCode.sourceForm) _

/-- Unrestricted same-Code static fields project to the shared body kernel.
Its original Source frame and compiler fields stay unchanged. -/
def Support.origin (escaped : faults .controlEscapedFunction code.compilation.internalReason) :
    CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults where
  layouts := compiled.indexed.layouts
  owner := code.compilation.owner
  active := code.active
  frameLayout := compiled.indexed.ancestry.layout.frame
  globals := compiled.indexed.base.globals.length
  onError := code.allocationError
  function := function
  expressionSyntax := support.expressionSyntax function.source
  certificates := support.certificates support.body.readFuel function.source
  validity := fun context => CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence
  diagnosticPolicy := .reachable
  administrative := administrative
  context := support.body.context
  scope := code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope
  output := code.receipt.resultCore
  code := code.receipt.body
  fellThrough := code.compilation.internalReason
  escaped := code.compilation.internalReason
  solved := code.compilation.solvedRequirements
  body := { flow := support.body.flow
            tree := support.body.tree
            sites := support.body.sites
            initialValid := support.body.valid
            projection := support.body.projection
            unique := support.body.unique
            emitted := support.body.emitted }
  definitions := rfl
  registered := CallableIndexedAmbient.frame_registered compiled.indexed
  escapedFault := escaped
  extend := fun valid extended => valid.extend extended
  runtimeOf := fun valid => valid

/-- The actual static parameter context, full Source frame and emitted body
remain definitionally those of this same Code. -/
def Support.body_origin (escaped : faults .controlEscapedFunction code.compilation.internalReason) :
    CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin (program := Program.ofChecked compiled.sourceProgram)
      code support.body.toContext registry faults :=
  ⟨support.origin escaped, support.body.frame, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaBinderProjections
/-! The actual contextual lambda producer retains its original binder policy.
Original Source monomorphic extension then supplies every canonical binder
projection for the same returned Code. Accepted lowering alone does not
establish that Source metadata. No body execution law is used. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaBinderProjections
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues

/-- The genuine Source binder extension supplies its own monomorphic metadata. -/
theorem monomorphic {owner : Resolved.DeclarationId} {context final : SourceSemantics.Context}
    {parameters : List TypedBinder} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend owner context parameters types final) :
    ∀ binder ∈ parameters, binder.scheme.quantified = [] := by
  intro binder member
  have schemes : binder.scheme ∈ parameters.map (fun item => item.scheme) := List.mem_map.mpr ⟨binder, member, rfl⟩
  rw [extended.schemes_eq] at schemes
  obtain ⟨type, _member, same⟩ := List.mem_map.mp schemes
  rw [← same]
  rfl

/-- The actual returned policy and original Source metadata identify all
selected native binder projections at this same static Site. -/
theorem Site.projected_bindings {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {captured : Dynamic.Environment} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (site : Site prepared named parameters result body sourceContext evidence captured scope administrative)
    (binderPolicy : site.code.policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
      ((representation prepared).atContext named.signature.key []) prepared.base.locals named.signature.key [])
    {types : List TypeSystem.Ty} {bodyContext : SourceSemantics.Context}
    (extended : MonoBindersExtend (source named).owner sourceContext parameters types bodyContext) :
    ∀ binding ∈ site.code.receipt.loweredParameters,
      checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  have projected := CallableIndexedLambdaScalarNativeTyping.parameter_projections
    site.code.receipt.parametersCompiled binderPolicy (by rfl) (monomorphic extended)
  intro binding member
  exact CompatibleExpressionReads.projectType_of_accepted (projected binding member)

/-- Genuine accepted contextual lowering chooses the actual policy internally;
the same Site carries its original Source binder projection vector. -/
theorem of_contextual_with_projections {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (captured : Dynamic.Environment)
    (profile : checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    {types : List TypeSystem.Ty} {bodyContext : SourceSemantics.Context}
    (extended : MonoBindersExtend (source named).owner sourceContext parameters types bodyContext)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) prepared.layouts.definitions) :
    ∃ site : Site prepared named parameters result body sourceContext evidence captured scope administrative,
      site.code.id = id ∧ site.code.lowered = lowered ∧
        ∀ binding ∈ site.code.receipt.loweredParameters, checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  obtain ⟨site, sameId, sameLowered, binderPolicy⟩ := CallableIndexedLambdaGeneration.of_contextual_with_binder
    prepared compiled record sourceContext evidence captured profile viewOfSource sourceFound sourceForm
    found form owner requirements coercions ordinary read accepted typed
  exact ⟨site, sameId, sameLowered, Site.projected_bindings site binderPolicy extended⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaBinderProjections
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalState
/-! A physical cache layer retains the original caller and its exact ordered
history. It can wrap ordinary or stronger canonical callers. Existing pool
and semantic Header interfaces remain available by projection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedHistory
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

structure State (caller : ProtectedStateTransition.Protocol.{u, 0} (Records keys))
    (index : ProtectedStateTransition.Index) where
  base : caller.State index
  physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store

def protocol (caller : ProtectedStateTransition.Protocol.{u, 0} (Records keys)) :
    ProtectedStateTransition.Protocol.{u, 0} (Records keys) where
  State := State caller
  records := fun state => caller.records state.base
  Relates := fun first last => caller.Relates first.base last.base
  refl := fun state => caller.refl state.base
  trans := fun first last => caller.trans first last

variable {caller : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}

def administrativeTransport (transport : ProtectedStateTransition.AdministrativeTransport caller) :
    ProtectedStateTransition.AdministrativeTransport (protocol caller) where
  extend := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata =>
    ⟨transport.extend state.base maps worlds frame metadata, state.physical.extend frame⟩
  related := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata => transport.related state.base maps worlds frame metadata
  records_eq := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata => transport.records_eq state.base maps worlds frame metadata

/-- Lexical slots affect the canonical environment only. The actual store and
Source map remain unchanged at these administrative scope operations. -/
def bindings (bindings : ProtectedStateTransition.Bindings caller) :
    ProtectedStateTransition.Bindings (protocol caller) where
  prepend := fun state id type value => ⟨bindings.prepend state.base id type value, state.physical⟩
  prepend_related := fun state id type value => bindings.prepend_related state.base id type value
  prepend_records := fun state id type value => bindings.prepend_records state.base id type value
  restore := fun state => ⟨bindings.restore state.base, state.physical⟩
  restore_related := fun state => bindings.restore_related state.base
  restore_records := fun state => bindings.restore_records state.base

/-- The same genuine marked allocation keeps its new snapshot and Source
cell, while its proved administrative frame preserves all cached globals. -/
def markedProducer {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {layouts : SourceCoreAllocationLayouts.Prepared}
    {layout : SourceCoreCallableIndexedFrames.Layout}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (producer : ProtectedStateTransition.MarkedAllocation.Producer caller layouts layout model) :
    ProtectedStateTransition.MarkedAllocation.Producer (protocol caller) layouts layout model where
  Ready := fun state location native => producer.Ready state.base location native
  complete := by
    intro owner active request globals allocate allocation annotation same definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native sourceType payload sourceValue sourceLocation
      environments agrees heaps reference read payloadAt cell allocated initial ready
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame, final, related⟩ :=
      producer.complete allocation annotation same definitions registered
        environments agrees heaps reference read payloadAt cell allocated initial.base ready
    exact ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame,
      ⟨final, initial.physical.extend frame⟩, related⟩

/-- Returning uses the actual reached pool and genuine administrative frame
receipt. Physical cells are never inferred from an arbitrary pool. -/
def carrier {slots : ProtectedStateTransition.Index → Prop}
    (original : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) slots caller) :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun index => slots index ∧ CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
      (protocol caller) where
  pool := fun state => original.pool state.base
  records_eq := fun state => original.records_eq state.base
  related := original.related
  slots := fun state => ⟨original.slots state.base, state.physical⟩
  restore := by
    intro index initial mapping world heap store reached maps worlds frame metadata related
    obtain ⟨returned, same, related⟩ := original.restore initial.base reached maps worlds frame metadata related
    exact ⟨⟨returned, initial.physical.extend frame⟩, same, related⟩

abbrev PoolState (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program))
    (index : ProtectedStateTransition.Index) :=
  State (CallableIndexedOwnedFunctionState.protocol headers keys) index

/-- Actual frame writes retain complete physical cache reads as well as the
reached ordinary pool records. -/
def install {index : ProtectedStateTransition.Index} (state : PoolState headers keys index)
    (selected : Fin keys.length) {next : NativeFrame} {nextGhost : GhostFrame}
    (history : Current compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table next nextGhost) :
    PoolState headers keys (index.extend index.mapping index.world index.heap
      (index.store.set keys[selected.val].frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame next))) := by
  have frameRead := (state.base.rows selected).authority.frame.read
  rw [(state.base.rows selected).frame_eq] at frameRead
  exact ⟨CallableIndexedOwnedFunctionState.install state.base selected history,
    state.physical.install frameRead next⟩

theorem install_records {index : ProtectedStateTransition.Index} (state : PoolState headers keys index)
    (selected : Fin keys.length) {next : NativeFrame} {nextGhost : GhostFrame}
    (history : Current compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table next nextGhost) :
    records (install state selected history).base = records state.base :=
  CallableIndexedOwnedFunctionState.install_records state.base selected history

/-- Restoring the saved frame uses the reached physical store and pool; every
new Source cell and every reached snapshot stays in place. -/
def restored {initial reached : ProtectedStateTransition.Index}
    (saved : PoolState headers keys initial) (after : PoolState headers keys reached) (selected : Fin keys.length) :
    PoolState headers keys (reached.extend reached.mapping reached.world reached.heap
      (reached.store.set keys[selected.val].frameLocation
        (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame
          (saved.base.rows selected).authority.current))) := by
  have frameRead := (after.base.rows selected).authority.frame.read
  rw [(after.base.rows selected).frame_eq] at frameRead
  exact ⟨CallableIndexedOwnedFunctionState.restored saved.base after.base selected,
    after.physical.install frameRead (saved.base.rows selected).authority.current⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalState
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCanonicalState
/-! Canonical callers retain every physical global reference, including method
slots, together with the complete cache. Ordinary Header slots are a derived
projection using the actual owner's initialized location association. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCanonicalState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedHistory
open CallableIndexedOwnedPhysicalGlobals
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

def slotsProtocol (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)) (callerPrefix : Nat) :
    ProtectedStateTransition.Protocol (Records keys) where
  State := fun index => { _pool : State headers keys index // Slots compiled callerPrefix index.scope index.canonical }
  records := fun state => records state.val
  Relates := fun first last => Relates first.val last.val
  refl := fun state => Relates.refl state.val
  trans := fun first last => first.trans last

def protocol (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)) (callerPrefix : Nat) :=
  CallableIndexedOwnedPhysicalState.protocol (slotsProtocol headers keys callerPrefix)

/-- Lift the actual marked parameter result. The full physical proof comes
from the original cache, the actual frame write and the returned administrative
frame; the canonical slots come from the retained allocation spine. -/
def of_parameter_spine
    {mapping : LocationMap} {store : Store} {frameLocation : Location} {native : NativeFrame}
    (physical : Authority compiled mapping store)
    (frameRead : store.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (next : NativeFrame) {index : ProtectedStateTransition.Index}
    (frame : AdministrativePreserved mapping
      (store.set frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame next)) index.mapping index.store)
    (pool : State headers keys index)
    {canonical added : Environment} (slots : Slots compiled 0 [] canonical) (packed : Value)
    (length : added.length = index.scope.length)
    (spine : index.canonical = added ++ packed :: canonical) :
    (protocol headers keys 1).State index :=
  ⟨⟨pool, spine ▸ slots.parameters packed length⟩, (physical.install frameRead next).extend frame⟩

private def slotsCaller (callerPrefix : Nat) :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun index => Slots compiled callerPrefix index.scope index.canonical) (slotsProtocol headers keys callerPrefix) where
  pool := fun state => state.val
  records_eq := fun _ => rfl
  related := fun related => related
  slots := fun state => state.property
  restore := fun {_index} initial {_mapping _world _heap _store} reached _maps _worlds _frame _metadata related =>
    ⟨⟨reached, initial.property⟩, rfl, related⟩

def caller (callerPrefix : Nat) :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun index => Slots compiled callerPrefix index.scope index.canonical ∧
        Authority compiled index.mapping index.store) (protocol headers keys callerPrefix) :=
  CallableIndexedOwnedPhysicalState.carrier (slotsCaller callerPrefix)

theorem ordinary_slots (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (locations : ∀ header, header ∈ headers → owner.key.locations header = location compiled header.slot)
    {callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (slots : Slots compiled callerPrefix scope canonical) :
    CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner callerPrefix scope canonical := by
  intro header member
  rw [locations header member]
  exact slots _ _ (CallableIndexedPreparedInventories.cached_global_at compiled header.selected)

/-- Existing ordinary direct calls use the same stronger state and unchanged
pool. This adapter forgets only the extra slot facts at its interface. -/
def ordinaryCaller (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat)
    (locations : ∀ header, header ∈ headers → owner.key.locations header = location compiled header.slot) :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner callerPrefix index.scope index.canonical)
      (protocol headers keys callerPrefix) where
  pool := (caller callerPrefix).pool
  records_eq := (caller callerPrefix).records_eq
  related := (caller callerPrefix).related
  slots := fun state => ordinary_slots owner locations ((caller callerPrefix).slots state).1
  restore := (caller callerPrefix).restore

private def slotsAdministrative (callerPrefix : Nat) :
    ProtectedStateTransition.AdministrativeTransport (slotsProtocol headers keys callerPrefix) where
  extend := fun {_index} state {_mapping _world _heap _store} maps worlds frame metadata =>
    ⟨state.val.extend maps worlds frame metadata, state.property⟩
  related := fun {_index} _state {_mapping _world _heap _store} _maps _worlds _frame _metadata =>
    Relates.of_records_eq rfl
  records_eq := fun {_index} _state {_mapping _world _heap _store} _maps _worlds _frame _metadata => rfl

def administrativeTransport (callerPrefix : Nat) :
    ProtectedStateTransition.AdministrativeTransport (protocol headers keys callerPrefix) :=
  CallableIndexedOwnedPhysicalState.administrativeTransport (slotsAdministrative callerPrefix)

private def slotsBindings (callerPrefix : Nat) :
    ProtectedStateTransition.Bindings (slotsProtocol headers keys callerPrefix) where
  prepend := fun state id type value =>
    ⟨(CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).prepend state.val id type value,
      state.property.prepend id type value⟩
  prepend_related := fun state id type value =>
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).prepend_related state.val id type value
  prepend_records := fun state id type value =>
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).prepend_records state.val id type value
  restore := fun state => ⟨(CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore state.val,
    state.property.restore⟩
  restore_related := fun state => (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore_related state.val
  restore_records := fun state => (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore_records state.val

def bindings (callerPrefix : Nat) : ProtectedStateTransition.Bindings (protocol headers keys callerPrefix) :=
  CallableIndexedOwnedPhysicalState.bindings (slotsBindings callerPrefix)

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)

private def slotsMarked (callerPrefix : Nat) :
    ProtectedStateTransition.MarkedAllocation.Producer (slotsProtocol headers keys callerPrefix)
      compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model where
  Ready := fun state location native => (CallableIndexedOwnedMarkedAllocation.producer headers keys model).Ready state.val location native
  complete := by
    intro owner active request globals allocate allocation annotation same definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native sourceType payload sourceValue sourceLocation
      environments agrees heaps reference read payloadAt cell allocated initial ready
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame, final, related⟩ :=
      (CallableIndexedOwnedMarkedAllocation.producer headers keys model).complete allocation annotation same definitions registered
        environments agrees heaps reference read payloadAt cell allocated initial.val ready
    exact ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame,
      ⟨final, initial.property.prepend request.binder.id request.payloadType
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))⟩, related⟩

def markedProducer (callerPrefix : Nat) :
    ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys callerPrefix)
      compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model :=
  CallableIndexedOwnedPhysicalState.markedProducer (slotsMarked model callerPrefix)

theorem readyAt_of_stableOwner (callerPrefix : Nat) {location : Location} {native : NativeFrame}
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      (markedProducer (headers := headers) (keys := keys) model callerPrefix).toOrdinary location native := by
  intro index state read
  exact CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner (headers := headers) model stable state.base.val read

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCanonicalState
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPhysicalCaptures
/-! Ordinary named entries can use the same complete physical capture as
methods. The actual Header and cached lambda retain Source provenance; the
canonical environment is the literal installed one with all physical slots. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPhysicalCaptures
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPhysicalGlobals RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping
open CallableIndexedOwnedFunctionValues (Header Key NamedCapture)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (Header compiled program)} {key : Key compiled program}
  {header : Header compiled program} {mapping : LocationMap} {world : StoreTyping} {store : Store}

/-- The genuine initialized owner keeps one frame and the physical locations
of every ordinary semantic header in its catalog. -/
structure KeyPhysical (key : Key compiled program) (headers : List (Header compiled program)) : Prop where
  frame : key.frameLocation = 0
  prefixZero : key.capturePrefix = 0
  locations : ∀ target, target ∈ headers → key.locations target = location compiled target.slot

structure Capture (headers : List (Header compiled program)) (key : Key compiled program)
    (header : Header compiled program) (mapping : LocationMap) (world : StoreTyping) (store : Store) where
  keyPhysical : KeyPhysical key headers
  named : NamedCapture headers key header mapping world
  read : store.read? (key.locations header) = some (.inRight .unit
    (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
      (header.code.rename named.embedding.lift) named.captured))
  canonical_eq : named.canonical = environment compiled
  captured_eq : named.captured = List.replicate header.slot .unit ++ environment compiled
  embedding_eq : named.embedding = shift header.slot
  slots : Slots compiled 0 [] named.canonical

theorem of_read
    (member : header ∈ headers)
    (frameZero : key.frameLocation = 0) (prefixZero : key.capturePrefix = 0)
    (locations : ∀ target, target ∈ headers → key.locations target = location compiled target.slot)
    (globals : header.globals = compiled.indexed.base.globals.length)
    (read : store.read? (location compiled header.slot) = some (.inRight .unit
      (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
        (header.code.rename (shift header.slot).lift)
        (List.replicate header.slot .unit ++ environment compiled))))
    (typed : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions) :
    Nonempty (Capture headers key header mapping world store) := by
  obtain ⟨capturedContext, capturedTyped, _bodyTyped⟩ := stored_closure typed read
  obtain ⟨administrative, canonicalTyped⟩ := drop_installer_units header.slot capturedTyped
  have layout : EnvironmentsAgree (shift header.slot) (environment compiled)
      (List.replicate header.slot .unit ++ environment compiled) := by
    intro index value found
    rw [List.getElem?_append_right (by simp [shift])]
    simpa [shift] using found
  have frameReference := RecursiveNamedCatalogInitialization.frame_reference compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame
  change (RecursiveNamedCatalogPreparedInitialization.environment compiled)[compiled.indexed.base.globals.length]? = _ at frameReference
  rw [RecursiveNamedPublicBootstrapGlobals.environment_eq] at frameReference
  let named : NamedCapture headers key header mapping world := {
    administrative := administrative, canonical := environment compiled
    captured := List.replicate header.slot .unit ++ environment compiled
    capturedContext := capturedContext, embedding := shift header.slot
    environments := .nil canonicalTyped, layout := layout, typed := capturedTyped
    reference := by simpa only [globals, frameZero] using frameReference
    capturedReference := by simpa only [frameZero] using layout frameReference
    coherent := by
      intro target targetMember
      rw [prefixZero, locations target targetMember]
      simpa only [List.length_nil, Nat.zero_add] using environment_slots compiled target.slot target.named.signature
        (CallableIndexedPreparedInventories.cached_global_at compiled target.selected) }
  refine ⟨⟨⟨frameZero, prefixZero, locations⟩, named, ?_, rfl, rfl, rfl, environment_slots compiled⟩⟩
  simpa only [locations header member] using read

theorem of_cached
    (member : header ∈ headers)
    (frameZero : key.frameLocation = 0) (prefixZero : key.capturePrefix = 0)
    (locations : ∀ target, target ∈ headers → key.locations target = location compiled target.slot)
    (globals : header.globals = compiled.indexed.base.globals.length)
    (cached : compiled.indexed.secondPass.closures[header.slot]? = some
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code))
    (physical : Authority compiled mapping store)
    (typed : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions) :
    Nonempty (Capture headers key header mapping world store) := by
  exact of_read member frameZero prefixZero locations globals (physical.cached cached).2 typed

/-- An actual prepared inventory row supplies the exact cache equation and all
header alignment; callers do not separately assume a cached body. -/
theorem of_headerAt
    {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {key : Key compiled (Program.ofChecked compiled.sourceProgram)}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    (member : header ∈ headers) (keyPhysical : KeyPhysical key headers)
    (physical : Authority compiled mapping store)
    (typed : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions) :
    Nonempty (Capture headers key header mapping world store) := by
  have cached : compiled.indexed.secondPass.closures[header.slot]? = some
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code) := by
    rw [aligned.slot, aligned.named, aligned.code]
    exact prepared.cached.trans (congrArg some prepared.compilation.emitted)
  exact of_cached member keyPhysical.frame keyPhysical.prefixZero keyPhysical.locations
    aligned.globals cached physical typed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPhysicalCaptures
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCellAllocationProducer
/-! A live authority row supplies the actual marked allocation even when its
independent source cell keeps a type erased by the compiler's marker binder.
The selected row registers the same captured snapshot before the payload. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCellAllocationProducer
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAllocationProducer (Ready)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

def producer {catalog : SourceCoreDataCatalog.Catalog}
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program))
    (model : GenericHeap.CellModel compiled.indexed.layouts.definitions) :
    ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) (protocol headers keys)
      compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model where
  Ready := Ready
  complete := by
    intro owner active request globals allocate allocation annotation same _definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native sourceCell payload sourceLocation
      environments agrees heaps reference _read payloadAt cell allocated initial ready
    obtain ⟨selected, metadata, physicalOwner, current, history⟩ := ready
    subst contextLocation
    subst native
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, _boundEnvironment,
      frame, final, related, _selectedRecords, _otherRecords⟩ :=
      CallableIndexedOwnedCellAllocation.completed_bind allocation annotation same registered initial selected
        history environments agrees heaps reference payloadAt cell allocated
    exact ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame, final, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCellAllocationProducer
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExpressionTreeBounds
/-! The original static expression Tree fold composes actual child states.
Every call receives the real argument post pool and original canonical slots.
The builtin fragment grammar contains no named calls; its proved administrative
leaf effects preserve the complete record observation. Source and Core grades
remain independent, and callee obligations are strictly smaller. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExpressionTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds RecursiveNamedBoundedContracts
open CallableIndexedOwnedExpressionHeads

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  {literals certificate : GenericExpressionMeaning.Certificate}
  {faults : FunctionCalls.FaultRep}
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) {compilation : SourceCoreFunctions.Context}

/-- The supplied original slot proof is paired with the actual input; only the
proof wrapper is forgotten at the actual reached pool. -/
theorem preserves_with_globals {callerPrefix size}
    (meaning : ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner callerPrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults size) :
    PreservesAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner callerPrefix certificate size := by
  intro scope id lowered certified node found mapping world admin environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees typed initial globals trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related⟩ :=
    meaning certified found environments heaps locals agrees typed ⟨initial, globals⟩ trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached.val, related⟩

/-- Native completion keeps the exact returned pool and its independently
measured source derivation when forgetting the slot proof wrapper. -/
theorem reflects_with_globals {callerPrefix size}
    (meaning : ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner callerPrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults size) :
    ReflectsAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner callerPrefix certificate size := by
  intro scope id lowered certified node found mapping world admin environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees typed initial globals completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related⟩ :=
    meaning certified found environments heaps locals agrees typed ⟨initial, globals⟩ completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached.val, related⟩

include extension faithful functionLeaves functionTypes unique missing in
/-- Compositional heads consume the actual ordered child states. -/
theorem head_preserves_at_with_calls
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (callerPrefix budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → ProtectedStateTransition.PreservesAt
      (argumentProtocol (headers := headers) owner callerPrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults child)
    (callMeaning : ProtectedStateTransition.PreservesAt
      (argumentProtocol (headers := headers) owner callerPrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source (calls certificate) faults size) :
    ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner callerPrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head calls (.initial compiled.compatible.checked) source context reasonAt certificate) faults size := by
  exact ProtectedStateExpressionCallsHeads.head_preserves_at_with_calls functions extension faithful functionLeaves functionTypes evidence unique missing calls
    (argumentProtocol (headers := headers) owner callerPrefix)
    (CallableIndexedOwnedCanonicalState.administrativeTransport owner callerPrefix)
    budget size within children callMeaning

include extension faithful functionLeaves functionTypes missing in
/-- Reflection uses the same actual child posts at their native grades. -/
theorem head_reflects_at_with_calls
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (callerPrefix budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → ProtectedStateTransition.ReflectsAt
      (argumentProtocol (headers := headers) owner callerPrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults child)
    (callMeaning : ProtectedStateTransition.ReflectsAt
      (argumentProtocol (headers := headers) owner callerPrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source (calls certificate) faults size) :
    ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner callerPrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head calls (.initial compiled.compatible.checked) source context reasonAt certificate) faults size := by
  exact ProtectedStateExpressionCallsHeads.head_reflects_at_with_calls functions extension faithful functionLeaves functionTypes evidence missing calls
    (argumentProtocol (headers := headers) owner callerPrefix)
    (CallableIndexedOwnedCanonicalState.administrativeTransport owner callerPrefix)
    budget size within children callMeaning

variable
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (conditions : ∀ header, BodyCondition (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header)
  (authorized : ∀ header, header ∈ headers → CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
    functions registry header owner.key.frameLocation (conditions header))

include extension faithful functionLeaves functionTypes unique owners uninitialized missing sameLayouts authorized in
/-- The unchanged static Tree fold closes every expression child. Actual call
bodies remain only at genuine strict Source child grades. -/
theorem preserves_at_with_literals
    (idsUnique : RequirementIdsUnique context)
    (literalMeaning : GenericExpressionMeaning.Preserves
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        functions registry header faults (protocol headers keys) (conditions header))) :
    ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
          (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
          (some evidence) headers compilation source context)
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply RecursiveNamedExpressionTreeBounds.preserves_at_with_state
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (program := program) (registry := registry) (source := source) (context := context)
    (reasonAt := reasonAt) (solved := solved) (fuel := fuel) (literals := literals) (faults := faults) functions evidence
    (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
    (RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (some evidence) headers compilation source context) budget size within
  · intro child childWithin
    exact ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _
      (CallableIndexedOwnedCanonicalState.administrativeTransport owner compilation.administrativePrefix)
      (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
        (ProtectedExpressionMeaning.preserves_of_typed _
          (CompatibleExpressionBuiltins.preserves_with_literals functions extension faithful functionLeaves functionTypes
            program evidence unique uninitialized missing literalMeaning)) child)
  · intro childCertificate child childWithin children
    apply head_preserves_at_with_calls functions extension faithful functionLeaves functionTypes evidence unique missing owner
      (RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (some evidence) headers compilation source context) compilation.administrativePrefix budget child childWithin children
    exact PreservesAtWithGlobals.to_stateful functions owner compilation.administrativePrefix
      (CallableIndexedOwnedExpressionHeads.preserves_at_with functions owner sameLayouts conditions authorized
        budget child childWithin idsUnique unique owners
        (fun smaller smallerWithin => preserves_with_globals functions evidence owner (children smaller (Nat.le_of_lt smallerWithin))) bodies)

include extension faithful functionLeaves functionTypes uninitialized missing sameLayouts authorized in
/-- Core children and named hook bodies supply their independent strict grades;
the existing fold returns the separately measured Source trace and real pool. -/
theorem reflects_at_with_literals
    (literalMeaning : GenericExpressionMeaning.Reflects
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        functions registry header faults (protocol headers keys) (conditions header))) :
    ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
          (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
          (some evidence) headers compilation source context)
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply RecursiveNamedExpressionTreeBounds.reflects_at_with_state
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (program := program) (registry := registry) (source := source) (context := context)
    (reasonAt := reasonAt) (solved := solved) (fuel := fuel) (literals := literals) (faults := faults) functions evidence
    (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
    (RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (some evidence) headers compilation source context) budget size within
  · intro child childWithin
    exact ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _
      (CallableIndexedOwnedCanonicalState.administrativeTransport owner compilation.administrativePrefix)
      (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
        (ProtectedExpressionMeaning.reflects_of_typed _
          (CompatibleExpressionBuiltins.reflects_with_literals functions extension faithful functionLeaves functionTypes
            program evidence uninitialized missing literalMeaning)) child)
  · intro childCertificate child childWithin children
    apply head_reflects_at_with_calls functions extension faithful functionLeaves functionTypes evidence missing owner
      (RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (some evidence) headers compilation source context) compilation.administrativePrefix budget child childWithin children
    exact ReflectsAtWithGlobals.to_stateful functions owner compilation.administrativePrefix
      (CallableIndexedOwnedExpressionHeads.reflects_at_with functions owner sameLayouts conditions authorized
        budget child childWithin
        (fun smaller smallerWithin => reflects_with_globals functions evidence owner (children smaller (Nat.le_of_lt smallerWithin))) bodies)

include extension faithful functionLeaves functionTypes valid unique owners uninitialized missing sameLayouts authorized in
/-- The original compiler Tree supplies its complete literal receipts. -/
theorem preserves_at
    (idsUnique : RequirementIdsUnique context)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        functions registry header faults (protocol headers keys) (conditions header))) :
    ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree
        (RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
          (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
          (some evidence) headers compilation source context)
        fuel (.initial compiled.compatible.checked) source context solved reasonAt) faults size := by
  intro scope id lowered tree
  exact preserves_at_with_literals functions extension faithful functionLeaves functionTypes evidence unique owners uninitialized missing
    owner sameLayouts conditions authorized idsUnique
    (CompatibleExpressionLiterals.preserves functions program context evidence valid unique faults) budget size within bodies
    ⟨tree, tree.literalSites⟩

include extension faithful functionLeaves functionTypes valid uninitialized missing sameLayouts authorized in
/-- The original compiler Tree supplies its complete literal receipts. -/
theorem reflects_at
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        functions registry header faults (protocol headers keys) (conditions header))) :
    ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree
        (RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
          (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
          (some evidence) headers compilation source context)
        fuel (.initial compiled.compatible.checked) source context solved reasonAt) faults size := by
  intro scope id lowered tree
  exact reflects_at_with_literals functions extension faithful functionLeaves functionTypes evidence uninitialized missing
    owner sameLayouts conditions authorized
    (CompatibleExpressionLiterals.reflects functions program context evidence valid source faults) budget size within bodies
    ⟨tree, tree.literalSites⟩

include extension faithful functionLeaves functionTypes unique owners uninitialized missing sameLayouts authorized in
/-- Genuine runtime ledger receipts supply every literal leaf of the same Tree. -/
theorem preserves_at_runtime
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        functions registry header faults (protocol headers keys) (conditions header))) :
    ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
          (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
          (some evidence) headers compilation source context)
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)) faults size :=
  preserves_at_with_literals functions extension faithful functionLeaves functionTypes evidence unique owners uninitialized missing
    owner sameLayouts conditions authorized runtime.idsUnique
    (CompatibleExpressionLiteralRuntime.preserves functions program context evidence sameLedger runtime unique faults) budget size within bodies

include extension faithful functionLeaves functionTypes uninitialized missing sameLayouts authorized in
/-- Genuine runtime ledger receipts supply every literal leaf of the same Tree. -/
theorem reflects_at_runtime
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        functions registry header faults (protocol headers keys) (conditions header))) :
    ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
          (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
          (some evidence) headers compilation source context)
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)) faults size :=
  reflects_at_with_literals functions extension faithful functionLeaves functionTypes evidence uninitialized missing
    owner sameLayouts conditions authorized
    (CompatibleExpressionLiteralRuntime.reflects functions program context evidence sameLedger runtime source faults) budget size within bodies

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExpressionTreeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedBodyBounds
/-! A real named parameter entry supplies its original canonical globals.
The body family keeps those proofs alongside actual pools, while strict callee
callbacks receive the same concrete pools through the original low contracts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedFunctionState CallableIndexedOwnedExpressionHeads
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {condition : BodyCondition (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers)
    (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header}

/-- The complete real parameter entry supplies globals at its own body prefix.
The wrapped initial and returned witnesses contain the exact actual pools. -/
theorem preserves_of_canonical {size : Nat}
    (meaning : RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers)
      (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header faults
      (argumentProtocol (headers := headers) owner (owner.key.capturePrefix + 1)) condition size) :
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers)
      (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header faults
      (protocol headers keys) condition size := by
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry initial outcome after allowed trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, returned, related⟩ :=
    meaning entry ⟨initial, entry.catalog.globals⟩ allowed trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, returned.val, related⟩

/-- Native completion returns its original independent Source grade and the
same actual reached pool after forgetting only the canonical-slot proof. -/
theorem reflects_of_canonical {size : Nat}
    (meaning : RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers)
      (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header faults
      (argumentProtocol (headers := headers) owner (owner.key.capturePrefix + 1)) condition size) :
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers)
      (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header faults
      (protocol headers keys) condition size := by
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry initial value finalStore allowed completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, returned, related⟩ :=
    meaning entry ⟨initial, entry.catalog.globals⟩ allowed completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, returned.val, related⟩

section Family
variable (runtime : Bool)
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (certificates : CallableIndexedOwnedFunctionValues.Header compiled program → SourceSemantics.Context → GenericExpressionMeaning.Certificate)

def stableCondition (header : CallableIndexedOwnedFunctionValues.Header compiled program) :
    BodyCondition (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers)
      (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header :=
  CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
    (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header

variable (profileProvider : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : NativeFrame} {ghost : GhostFrame},
      (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers owner.key.locations owner.key.capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost) →
      stableCondition functions owner header entry →
      MatchProfileWith (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.solved context header.function.evidence)
        (certificates header) diagnosticPolicy header (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

private def producer {header : CallableIndexedOwnedFunctionValues.Header compiled program} (member : header ∈ headers) :
    ProtectedStateTransition.MarkedAllocation.Producer
      (argumentProtocol (headers := headers) owner (owner.key.capturePrefix + 1))
      header.layouts compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
  (sameLayouts header member).symm ▸ CallableIndexedOwnedCanonicalState.markedProducer owner (owner.key.capturePrefix + 1)
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)

private theorem ready_layout {first second : SourceCoreAllocationLayouts.Prepared}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (same : first = second)
    (marked : ProtectedStateTransition.MarkedAllocation.Producer
      (argumentProtocol (headers := headers) owner (owner.key.capturePrefix + 1)) second compiled.indexed.ancestry.layout.frame model)
    {location : Location} {native : NativeFrame}
    (ready : ProtectedStateTransition.OrdinaryAllocation.ReadyAt marked.toOrdinary location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt ((same.symm ▸ marked).toOrdinary) location native := by
  cases same
  exact ready

private theorem acquire {header : CallableIndexedOwnedFunctionValues.Header compiled program} (member : header ∈ headers)
    (location : Location) (native : NativeFrame)
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt (producer (registry := registry) functions owner sameLayouts member).toOrdinary location native := by
  exact ready_layout owner (sameLayouts header member)
    (CallableIndexedOwnedCanonicalState.markedProducer owner (owner.key.capturePrefix + 1)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (CallableIndexedOwnedCanonicalState.readyAt_of_stableOwner owner (owner.key.capturePrefix + 1)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable)

include extension faithful observations sameLayouts escaped profileProvider in
/-- The shared actual body fold closes callee meanings internally. Original
parameter globals authorize the canonical proof wrapper at each callee input. -/
theorem preserves_at_with_family
    (expressionMeaning : ∀ header, header ∈ headers → ∀ context,
      RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.solved context header.function.evidence →
      ∀ budget child, child ≤ budget →
      (∀ callee, callee ∈ headers → RecursiveNamedBoundedContracts.Below budget
        (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
          (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers)
          (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry callee faults
          (protocol headers keys) (stableCondition functions owner callee))) →
      ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner (owner.key.capturePrefix + 1))
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        program context header.function.evidence header.function.source (certificates header context) faults child)
    (size : Nat) : ∀ header, header ∈ headers →
      RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers)
        (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header faults
        (protocol headers keys) (stableCondition functions owner header) size := by
  have bodies := CallableRuntimeNamedBodyFamily.preserves_at
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) runtime functions extension faithful observations escaped
    (argumentProtocol (headers := headers) owner (owner.key.capturePrefix + 1)) (stableCondition functions owner)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun header member => producer (registry := registry) functions owner sameLayouts member)
    (fun header member => acquire (registry := registry) functions owner sameLayouts member)
    (CallableIndexedOwnedCanonicalState.administrativeTransport owner (owner.key.capturePrefix + 1))
    (CallableIndexedOwnedCanonicalState.bindings owner (owner.key.capturePrefix + 1))
    certificates profileProvider
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry allowed
      exact allowed)
    (by
      intro header member context valid budget child within below
      apply expressionMeaning header member context valid budget child within
      intro callee calleeMember smaller strict
      exact preserves_of_canonical functions owner (below callee calleeMember smaller strict)) size
  intro header member
  exact preserves_of_canonical functions owner (bodies header member)

include extension faithful observations sameLayouts escaped profileProvider functionTypes in
/-- The shared actual body fold closes callee meanings internally. Original
parameter globals authorize the canonical proof wrapper at each callee input. -/
theorem reflects_at_with_family
    (expressionMeaning : ∀ header, header ∈ headers → ∀ context,
      RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.solved context header.function.evidence →
      ∀ budget child, child ≤ budget →
      (∀ callee, callee ∈ headers → RecursiveNamedBoundedContracts.Below budget
        (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
          (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers)
          (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry callee faults
          (protocol headers keys) (stableCondition functions owner callee))) →
      ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner (owner.key.capturePrefix + 1))
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        program context header.function.evidence header.function.source (certificates header context) faults child)
    (size : Nat) : ∀ header, header ∈ headers →
      RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers)
        (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header faults
        (protocol headers keys) (stableCondition functions owner header) size := by
  have bodies := CallableRuntimeNamedBodyFamily.reflects_at
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) runtime functions extension faithful observations functionTypes escaped
    (argumentProtocol (headers := headers) owner (owner.key.capturePrefix + 1)) (stableCondition functions owner)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun header member => producer (registry := registry) functions owner sameLayouts member)
    (fun header member => acquire (registry := registry) functions owner sameLayouts member)
    (CallableIndexedOwnedCanonicalState.administrativeTransport owner (owner.key.capturePrefix + 1))
    (CallableIndexedOwnedCanonicalState.bindings owner (owner.key.capturePrefix + 1))
    certificates profileProvider
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry allowed
      exact allowed)
    (by
      intro header member context valid budget child within below
      apply expressionMeaning header member context valid budget child within
      intro callee calleeMember smaller strict
      exact reflects_of_canonical functions owner (below callee calleeMember smaller strict)) size
  intro header member
  exact reflects_of_canonical functions owner (bodies header member)

end Family
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedFamilyClosure
/-! Authentic named profiles close the actual body and expression families.
The original static Tree fold supplies all expression children, and the shared
measured body fold supplies strictly smaller callees. Complete evidence and
parameter entries remain intact; no execution meaning is a factory premise. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedFamilyClosure
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedExpressionHeads CallableIndexedOwnedExpressionTreeBounds
open CallableIndexedOwnedNamedBodyBounds (stableCondition)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)

section Expressions
variable {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {compilation : SourceCoreFunctions.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {fuel : Nat}
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful observations functionTypes unique owners uninitialized missing sameLayouts in
/-- Ordinary static call heads are included pointwise in the full evidence
head. The original Tree fold receives actual children and callee witnesses. -/
private theorem ordinary_preserves
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        functions registry header faults (protocol headers keys) (stableCondition functions owner header))) :
    ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (Expressions (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation fuel source context solved reasonAt) faults size := by
  have meaning : ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := RecursiveNamedCatalog.Head (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers compilation source context)
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source) (context := context)
        (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiterals.Certificate solved source id code)) faults size := by
    apply RecursiveNamedExpressionTreeBounds.preserves_at_with_state
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := program) (registry := registry) (source := source) (context := context)
      (reasonAt := reasonAt) (solved := solved) (fuel := fuel) (faults := faults)
      (literals := fun _ id code => CompatibleExpressionLiterals.Certificate solved source id code)
      functions evidence (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (RecursiveNamedCatalog.Head (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers compilation source context) budget size within

    · intro child childWithin
      exact ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedCanonicalState.administrativeTransport owner compilation.administrativePrefix)
        (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
          (ProtectedExpressionMeaning.preserves_of_typed _
            (CompatibleExpressionBuiltins.preserves_with_literals functions extension faithful observations functionTypes
              program evidence unique uninitialized missing
              (CompatibleExpressionLiterals.preserves functions program context evidence valid unique faults))) child)
    · intro childCertificate child childWithin children
      apply head_preserves_at_with_calls functions extension faithful observations functionTypes evidence unique missing owner
        (RecursiveNamedCatalog.Head (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers compilation source context) compilation.administrativePrefix budget child childWithin children
      have full : ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          program context evidence source
          (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
            (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
            headers compilation source context evidence childCertificate) faults child :=
        PreservesAtWithGlobals.to_stateful functions owner compilation.administrativePrefix
          (CallableIndexedOwnedExpressionHeads.preserves_at_with
            (certificate := childCertificate) functions owner sameLayouts (stableCondition functions owner)
            (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
            budget child childWithin (CompatibleRuntimeContextValidity.of_ordinary valid).runtime.idsUnique unique owners
            (fun smaller smallerWithin => preserves_with_globals functions evidence owner (children smaller (Nat.le_of_lt smallerWithin))) bodies)
      intro current id code head
      exact full (.ordinary head)

  intro scope id lowered tree
  exact meaning ⟨tree, tree.literalSites⟩

include extension faithful observations functionTypes uninitialized missing sameLayouts in
/-- Native ordinary heads use the same full evidence adapter pointwise, with
independently measured Source children and the exact reached actual pool. -/
private theorem ordinary_reflects
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        functions registry header faults (protocol headers keys) (stableCondition functions owner header))) :
    ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (Expressions (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation fuel source context solved reasonAt) faults size := by
  have meaning : ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := RecursiveNamedCatalog.Head (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers compilation source context)
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source) (context := context)
        (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiterals.Certificate solved source id code)) faults size := by
    apply RecursiveNamedExpressionTreeBounds.reflects_at_with_state
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := program) (registry := registry) (source := source) (context := context)
      (reasonAt := reasonAt) (solved := solved) (fuel := fuel) (faults := faults)
      (literals := fun _ id code => CompatibleExpressionLiterals.Certificate solved source id code)
      functions evidence (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (RecursiveNamedCatalog.Head (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers compilation source context) budget size within

    · intro child childWithin
      exact ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedCanonicalState.administrativeTransport owner compilation.administrativePrefix)
        (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
          (ProtectedExpressionMeaning.reflects_of_typed _
            (CompatibleExpressionBuiltins.reflects_with_literals functions extension faithful observations functionTypes
              program evidence uninitialized missing
              (CompatibleExpressionLiterals.reflects functions program context evidence valid source faults))) child)
    · intro childCertificate child childWithin children
      apply head_reflects_at_with_calls functions extension faithful observations functionTypes evidence missing owner
        (RecursiveNamedCatalog.Head (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers compilation source context) compilation.administrativePrefix budget child childWithin children
      have full : ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          program context evidence source
          (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
            (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
            headers compilation source context evidence childCertificate) faults child :=
        ReflectsAtWithGlobals.to_stateful functions owner compilation.administrativePrefix
          (CallableIndexedOwnedExpressionHeads.reflects_at_with
            (certificate := childCertificate) functions owner sameLayouts (stableCondition functions owner)
            (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
            budget child childWithin
            (fun smaller smallerWithin => reflects_with_globals functions evidence owner (children smaller (Nat.le_of_lt smallerWithin))) bodies)
      intro current id code head
      exact full (.ordinary head)

  intro scope id lowered tree
  exact meaning ⟨tree, tree.literalSites⟩

include extension faithful observations functionTypes unique owners uninitialized missing sameLayouts in
private theorem expressions_preserve (runtime : Bool)
    (valid : RecursiveNamedCatalogMutualMeaning.ContextFor runtime solved context evidence)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        functions registry header faults (protocol headers keys) (stableCondition functions owner header))) :
    ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (RecursiveNamedCatalogMutualMeaning.ExpressionsForWith true runtime evidence
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation fuel source context solved reasonAt) faults size := by
  cases runtime with
  | false => exact ordinary_preserves functions extension faithful observations functionTypes owner sameLayouts unique owners uninitialized missing valid budget size within bodies
  | true =>
    exact CallableIndexedOwnedExpressionTreeBounds.preserves_at_runtime functions extension faithful observations functionTypes evidence unique owners
      uninitialized missing owner sameLayouts (stableCondition functions owner)
      (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      valid.ledger valid.runtime budget size within bodies

include extension faithful observations functionTypes uninitialized missing sameLayouts in
private theorem expressions_reflect (runtime : Bool)
    (valid : RecursiveNamedCatalogMutualMeaning.ContextFor runtime solved context evidence)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
        functions registry header faults (protocol headers keys) (stableCondition functions owner header))) :
    ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (RecursiveNamedCatalogMutualMeaning.ExpressionsForWith true runtime evidence
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation fuel source context solved reasonAt) faults size := by
  cases runtime with
  | false => exact ordinary_reflects functions extension faithful observations functionTypes owner sameLayouts uninitialized missing valid budget size within bodies
  | true =>
    exact CallableIndexedOwnedExpressionTreeBounds.reflects_at_runtime functions extension faithful observations functionTypes evidence
      uninitialized missing owner sameLayouts (stableCondition functions owner)
      (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      valid.ledger valid.runtime budget size within bodies
end Expressions

section Families
variable (runtime : Bool)
  {compilation : CallableIndexedOwnedFunctionValues.Header compiled program → SourceCoreFunctions.Context}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = owner.key.capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : NativeFrame} {ghost : GhostFrame},
      BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers owner.key.locations owner.key.capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RecursiveNamedCatalogMutualMeaning.MatchProfileForModeWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) true runtime diagnosticPolicy headers header (compilation header)
        header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

include extension faithful observations functionTypes sameLayouts owners uninitialized missing escaped prefixMatches profiles in
/-- Authentic static profiles and actual parameter entries close all named
callee bodies through the existing measured mutual family. -/
theorem preserves_at (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) (stableCondition functions owner header) size := by
  apply CallableIndexedOwnedNamedBodyBounds.preserves_at_with_family functions owner runtime extension faithful observations
    sameLayouts escaped
    (fun header context => RecursiveNamedCatalogMutualMeaning.ExpressionsForWith true runtime header.function.evidence
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers (compilation header) header.readFuel header.function.source context header.solved header.reasonAt)
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry _allowed
      exact profiles header member entry) ?_ size
  intro header member context valid budget child within below
  rw [← prefixMatches header member]
  exact expressions_preserve (compilation := compilation header) (fuel := header.readFuel)
    functions extension faithful observations functionTypes owner sameLayouts header.unique owners
    (uninitialized header member) (missing header member) runtime valid budget child within below

include extension faithful observations functionTypes sameLayouts uninitialized missing escaped prefixMatches profiles in
/-- Original native grades choose the strict callees; the Source grade and
actual body post are returned by the same shared family. -/
theorem reflects_at (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) (stableCondition functions owner header) size := by
  apply CallableIndexedOwnedNamedBodyBounds.reflects_at_with_family functions owner runtime extension faithful observations functionTypes
    sameLayouts escaped
    (fun header context => RecursiveNamedCatalogMutualMeaning.ExpressionsForWith true runtime header.function.evidence
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers (compilation header) header.readFuel header.function.source context header.solved header.reasonAt)
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry _allowed
      exact profiles header member entry) ?_ size
  intro header member context valid budget child within below
  rw [← prefixMatches header member]
  exact expressions_reflect (compilation := compilation header) (fuel := header.readFuel)
    functions extension faithful observations functionTypes owner sameLayouts
    (uninitialized header member) (missing header member) runtime valid budget child within below

section Callers
variable {callerCompilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {fuel : Nat}
  (evidence : Dynamic.EvidenceEnvironment)
  (valid : RecursiveNamedCatalogMutualMeaning.ContextFor runtime solved context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful observations functionTypes sameLayouts owners uninitialized missing escaped prefixMatches profiles
  valid sourceUnique callerUninitialized callerMissing in
/-- The whole caller Tree may call any member, including itself or a mutual
callee. The shared body family closes every strictly smaller call internally. -/
theorem expression_preserves_at (size : Nat) :
    ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner callerCompilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (RecursiveNamedCatalogMutualMeaning.ExpressionsForWith true runtime evidence
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers callerCompilation fuel source context solved reasonAt) faults size := by
  exact expressions_preserve functions extension faithful observations functionTypes owner sameLayouts sourceUnique owners
    callerUninitialized callerMissing runtime valid size size (Nat.le_refl _) (by
      intro header member child _smaller
      exact preserves_at functions extension faithful observations functionTypes owner sameLayouts runtime owners
        uninitialized missing escaped prefixMatches profiles child header member)

include extension faithful observations functionTypes sameLayouts uninitialized missing escaped prefixMatches profiles
  valid callerUninitialized callerMissing in
/-- Completed native callers obtain independently graded Source traces and
actual restored pools from the same closed named body and expression families. -/
theorem expression_reflects_at (size : Nat) :
    ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner callerCompilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (RecursiveNamedCatalogMutualMeaning.ExpressionsForWith true runtime evidence
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers callerCompilation fuel source context solved reasonAt) faults size := by
  exact expressions_reflect functions extension faithful observations functionTypes owner sameLayouts
    callerUninitialized callerMissing runtime valid size size (Nat.le_refl _) (by
      intro header member child _smaller
      exact reflects_at functions extension faithful observations functionTypes owner sameLayouts runtime
        uninitialized missing escaped prefixMatches profiles child header member)
end Callers
end Families
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedFamilyClosure
end
