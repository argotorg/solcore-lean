import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeMeaning

/-! Runtime method bodies for the actual ordered output-coercion suffix.
Preservation consumes the raw operator's selected argument trace and the same
selected suffix dictionaries. It does not identify arbitrary source method
selections from native signatures. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedOperatorSuffixMeaning
open Core CoreProof Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory
open SourceCoreCallableIndexedFrames CallableIndexedParameterMeaning
open CallableCoercionPathMeaning

/-- The full static runtime profile belongs to the actual selected method row.
Raw endpoints and the singleton input layout are independent of projection. -/
structure Method {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (values : SourceCoreCompatibleValues.Context) (ambient : AmbientDefinitions values.checked.catalog.definitions)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) where
  step : CoercionStep
  call : CallableCoercionSpine.Call
  named : SourceCoreGeneralFunctions.Function
  diagnostics : SourceCoreDataPlaceFaultSites.Program
  code : Expr
  compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code
  signature : named.signature = call.signature
  sourceBody : Dynamic.BodyInstance
  dictionary : Dynamic.EvidenceEnvironment
  selected : Dynamic.OperatorMethodSelected program context evidence "Coerce" "coerce"
    step.requirements sourceBody dictionary
  administrative : Core.Context
  profile : CallablePreparedMethodRuntimeMeaning.Profile compiled values ambient sourceBody dictionary administrative registry faults
  input : TypedBinder
  bindings : named.inputs = [(input, call.signature.parameterType)]
  inputType : input.scheme.body = step.source
  result : sourceBody.resultType = step.target

section Rows

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
abbrev Methods := List (Method prepared values ambient registry faults program context evidence)

def Method.row (method : Method prepared values ambient registry faults program context evidence) : Row :=
  ⟨method.step, method.call, method.sourceBody, method.dictionary⟩

/-- The saved native closure and physical global slot are observations of the
same actual caller state. No runtime body law is stored in this receipt. -/
structure Capture (method : Method prepared values ambient registry faults program context evidence)
    (functions : FunctionModel values.checked.catalog ambient)
    (caller : Environment) (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) where
  installed : CallablePreparedMethodRuntimeMeaning.Installed method.compiled (sourceBody := method.sourceBody)
    (administrative := method.administrative) functions mapping world heap store caller
  index : installed.globalIndex = method.call.index

structure Entry (methods : Methods (prepared := prepared) (values := values) (ambient := ambient)
    (registry := registry) (faults := faults) (program := program) (context := context) (evidence := evidence))
    (functions : FunctionModel values.checked.catalog ambient)
    (caller : Environment) (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) : Type where
  captures : ∀ method ∈ methods, Nonempty (Capture method functions caller mapping world heap store)

variable {methods : Methods (prepared := prepared) (values := values) (ambient := ambient)
    (registry := registry) (faults := faults) (program := program) (context := context) (evidence := evidence)}
  {functions : FunctionModel values.checked.catalog ambient} {caller : Environment}
  {mapping nextMap : LocationMap} {world nextWorld : StoreTyping}
  {before after : Dynamic.Heap} {store finalStore : Store}

def Entry.extend (entry : Entry methods functions caller mapping world before store)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld)
    (frame : AdministrativePreserved mapping store nextMap finalStore)
    (metadata : Dynamic.HeapMetadataExtend before after) :
    Entry methods functions caller nextMap nextWorld after finalStore := by
  constructor
  intro method member
  obtain ⟨capture⟩ := entry.captures method member
  exact ⟨⟨capture.installed.extend maps worlds frame metadata, capture.index⟩⟩

variable (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (uninitialized : ∀ method ∈ methods, ∀ id location,
    faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  (escaped : ∀ method ∈ methods, faults .controlEscapedFunction method.compiled.own.table.escapedReason)

private theorem arguments {method : Method prepared values ambient registry faults program context evidence}
    {input : Dynamic.Value} {native : Value}
    (represented : ValueRep values.checked registry functions mapping world method.step.source input native
      method.call.signature.parameterType) :
    Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world
      method.named.inputs [input] [native] := by
  rw [method.bindings]
  apply Arguments.cons _ Arguments.nil
  change ValueRep _ _ _ _ _ method.input.scheme.body _ _ _
  simpa only [method.inputType] using represented

include extension faithful observations runtimeViews uninitialized missing escaped in
theorem method_preserves {method : Method prepared values ambient registry faults program context evidence}
    (member : method ∈ methods) {input : Dynamic.Value} {native : Value} {outcome : Dynamic.ExpressionOutcome}
    (entry : Entry methods functions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world method.step.source input native
      method.call.signature.parameterType)
    (trace : NamedCalls.BodyOutcome program method.sourceBody method.dictionary before [input] outcome after)
    (reason : Word) :
    ∃ value finalStore finalMap finalWorld,
      CallableCoercionSpine.Invoke caller reason method.call store (.inRight .word native) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        method.step.target method.call.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods functions caller finalMap finalWorld after finalStore) := by
  obtain ⟨capture⟩ := entry.captures method member
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, _, _⟩ :=
    method.profile.preserves method.compiled functions extension program faithful observations runtimeViews
      (uninitialized method member) (missing method member) (escaped method member)
      capture.installed (arguments functions represented) heaps trace
  have reference := capture.installed.globalReference
  rw [capture.index] at reference
  exact ⟨value, finalStore, finalMap, finalWorld,
    .applied reference capture.installed.globalRead evaluated,
    by simpa only [method.result, method.signature] using related,
    finalHeaps, maps, worlds, frame, metadata, ⟨entry.extend maps worlds frame metadata⟩⟩

/-- The same physical cell observation identifies the original measured body
child. It does not obtain a fresh measurement from an erased completion. -/
theorem Capture.completed_sized {method : Method prepared values ambient registry faults program context evidence}
    {budget : Nat} {input value : Value} {reason : Word}
    (capture : Capture method functions caller mapping world before store)
    (completed : CallableCoercionSpine.InvokeSized budget caller reason method.call store (.inRight .word input) value finalStore) :
    ∃ size, size < budget ∧ EvaluationSize size (input :: capture.installed.captured) store
      (method.compiled.output.rename capture.installed.embedding.lift) value finalStore := by
  have reference := capture.installed.globalReference
  rw [capture.index] at reference
  cases completed with
  | absent actual read =>
    have same := Option.some.inj (actual.symm.trans reference)
    cases same
    have impossible := Option.some.inj (read.symm.trans capture.installed.globalRead)
    cases impossible
  | applied actual read body smaller =>
    have same := Option.some.inj (actual.symm.trans reference)
    cases same
    have same := Option.some.inj (read.symm.trans capture.installed.globalRead)
    cases same
    exact ⟨_, smaller, body⟩

include extension faithful observations runtimeViews uninitialized missing escaped in
theorem method_reflects {method : Method prepared values ambient registry faults program context evidence}
    (member : method ∈ methods) {input : Dynamic.Value} {native value : Value} {budget : Nat} {reason : Word}
    (entry : Entry methods functions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world method.step.source input native
      method.call.signature.parameterType)
    (completed : CallableCoercionSpine.InvokeSized budget caller reason method.call store (.inRight .word native) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program method.sourceBody method.dictionary before [input] outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        method.step.target method.call.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods functions caller finalMap finalWorld after finalStore) := by
  obtain ⟨capture⟩ := entry.captures method member
  obtain ⟨size, _smaller, evaluated⟩ := capture.completed_sized functions completed
  obtain ⟨outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, frame, metadata, _, _⟩ :=
    method.profile.reflects_sized method.compiled functions extension program faithful observations runtimeViews
      (uninitialized method member) (missing method member) (escaped method member)
      capture.installed (arguments functions represented) heaps evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace,
    by simpa only [method.result, method.signature] using related,
    finalHeaps, maps, worlds, frame, metadata, ⟨entry.extend maps worlds frame metadata⟩⟩

include extension faithful observations runtimeViews uninitialized missing escaped in
theorem path_preserves {source target : TypeSystem.Ty} {inputType outputType : Ty}
    (chain : ChainFor Method.row source inputType methods target outputType)
    {input : Dynamic.Value} {native : Value} {outcome : Dynamic.ExpressionOutcome}
    (entry : Entry methods functions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputType)
    (trace : SelectedTraceFor Method.row program methods before input outcome after) (reason : Word) :
    ∃ value finalStore finalMap finalWorld,
      CallableCoercionSpine.Runs caller reason store (.inRight .word native) (methods.map (·.call)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods functions caller finalMap finalWorld after finalStore) :=
  CallableCoercionPathMeaning.preserves_for (functions := functions)
    (State := Entry methods functions caller)
    (fun entry maps worlds frame metadata => entry.extend maps worlds frame metadata)
    (fun member entry heaps represented trace => method_preserves functions extension faithful observations runtimeViews
      uninitialized missing escaped member entry heaps represented trace reason)
    chain entry heaps represented trace

include extension faithful observations runtimeViews uninitialized missing escaped in
theorem path_reflects {source target : TypeSystem.Ty} {inputType outputType : Ty}
    (chain : ChainFor Method.row source inputType methods target outputType)
    {input : Dynamic.Value} {native value : Value} {budget : Nat} {reason : Word}
    (entry : Entry methods functions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputType)
    (runs : CallableCoercionSpine.RunsFor (CallableCoercionSpine.InvokeSized budget caller reason)
      store (.inRight .word native) (methods.map (·.call)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      SelectedTraceFor Method.row program methods before input outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods functions caller finalMap finalWorld after finalStore) :=
  CallableCoercionPathMeaning.reflects_for (functions := functions)
    (State := Entry methods functions caller) (fun invoked => invoked.forget)
    (fun entry maps worlds frame metadata => entry.extend maps worlds frame metadata)
    (fun member entry heaps represented completed => method_reflects functions extension faithful observations runtimeViews
      uninitialized missing escaped member entry heaps represented completed)
    chain entry heaps represented runs

/-- Erasure retains the real selected Coerce judgment and all ordered heaps. -/
theorem path_source {input : Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (trace : SelectedTraceFor Method.row program methods before input outcome after) :
    CallableCoercionExpressionMeaning.Path program context evidence before (methods.map (·.step)) input outcome after := by
  induction trace with
  | nil => exact .nil
  | @cons method methods before middle after input value outcome invoked tail ih =>
    cases outcome with
    | value result => exact .cons (.method method.selected invoked) ih
    | fault reason => exact .tail (.method method.selected invoked) ih
  | @fault method methods before after input reason failed => exact .head (.method method.selected failed)

section Emission
variable {compilerProgram : CheckedProgram} {project : SourceCoreEvidence.Projector}
  {compilation : SourceCoreFunctions.Context} {callerFunction : SourceSpecialization.SpecializedFunction}
  {available : SourceCompilationPlan.EvidenceEnvironment} {scope : SourceCoreBasic.Scope}
  {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy} {ξ : Renaming}

/-- Each row retains the actual output compiler step, full selected record and
ordered dictionary. The body profile's source and saved captures are separate
from the renamed caller slot. -/
inductive Emitted (compilerProgram : CheckedProgram) (project : SourceCoreEvidence.Projector)
    (compilation : SourceCoreFunctions.Context) (callerFunction : SourceSpecialization.SpecializedFunction)
    (available : SourceCompilationPlan.EvidenceEnvironment) (scope : SourceCoreBasic.Scope)
    (node : ExpressionNode) (policy : SourceCoreFunctions.CallablePolicy) (ξ : Renaming) :
    SourceCoreBasic.LoweredExpr → Methods (prepared := prepared) (values := values) (ambient := ambient)
      (registry := registry) (faults := faults) (program := program) (context := context) (evidence := evidence) →
    SourceCoreBasic.LoweredExpr → List CallableCoercionSpine.Call → Prop where
  | nil {input} : Emitted compilerProgram project compilation callerFunction available scope node policy ξ input [] input []
  | cons {input middle output call calls method methods}
      (step : CallableCoercionSpine.Step compilerProgram project compilation callerFunction available scope node policy input method.step middle call)
      (slot : method.call = call.rename ξ)
      (completeRecord : method.named.specialized = step.specialized)
      (dictionary : method.dictionary = CallableNamedMetadata.environment step.dictionary)
      (tail : Emitted compilerProgram project compilation callerFunction available scope node policy ξ middle methods output calls) :
      Emitted compilerProgram project compilation callerFunction available scope node policy ξ input (method :: methods) output (call :: calls)

variable {input output : SourceCoreBasic.LoweredExpr} {calls : List CallableCoercionSpine.Call}

theorem Emitted.spine
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ input methods output calls) :
    CallableCoercionSpine.Spine compilerProgram project compilation callerFunction available scope node policy
      input (methods.map (·.step)) output calls := by
  induction emitted with
  | nil => exact .nil
  | cons step _ _ _ tail ih => exact .cons step ih

theorem Emitted.calls_eq
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ input methods output calls) :
    methods.map (·.call) = calls.map (CallableCoercionSpine.Call.rename ξ) := by
  induction emitted with
  | nil => rfl
  | cons step slot _ _ tail ih => simp only [List.map_cons, slot, ih]

/-- The actual compiler success supplies its ordered native spine before any
source body profiles are chosen. This reuses the existing compiler extractor. -/
theorem actual_suffix
    (accepted : SourceCoreEvidence.applyCoercions compilerProgram project compilation callerFunction available
      scope node policy input node.coercions = .ok output) :
    ∃ calls, CallableCoercionSpine.Spine compilerProgram project compilation callerFunction available scope node policy
      input node.coercions output calls :=
  CallableCoercionSpine.of_accepted accepted

end Emission

end Rows

section Operator
open CallablePreparedMethodRuntimeMeaning

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  {compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

variable (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
  (profile : CallablePreparedMethodRuntimeMeaning.Profile compiled values ambient sourceBody dictionary administrative registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (diagnostics.reasonAt named.signature.key id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((diagnostics.reasonAt named.signature.key id).add tag))
  (escaped : faults .controlEscapedFunction compiled.own.table.escapedReason)
  {callerSource : TypedSource} {callerContext : SourceSemantics.Context}
  {callerEvidence : Dynamic.EvidenceEnvironment} {callerSolved : List SolvedRequirement}
  {callerReasonAt : ExpressionId → Word} {readFuel : Nat}
  (callerValid : CompatibleRuntimeContextValidity.Valid callerSolved callerContext callerEvidence)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (callerReasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((callerReasonAt id).add tag))
  {checkedProgram : CheckedProgram} {project : CallableCoercionExpressionCertificates.Projector}
  {caller : SourceSpecialization.SpecializedFunction} {compilation : SourceCoreFunctions.Context}
  {child : SourceCoreEvidence.Child} {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode} {output : SourceCoreBasic.LoweredExpr}
  (receipt : CallablePreparedMethodSelection.Operator checkedProgram project caller compilation child fuel
    callerSource scope id callerReasonAt policy node output)

variable (alignment : OperatorAlignment (named := named) (sourceBody := sourceBody) (dictionary := dictionary) receipt)
  (selected : OperatorSource receipt)
  (selection : Dynamic.OperatorMethodSelected program callerContext callerEvidence selected.traitName selected.methodName
    receipt.requirements sourceBody dictionary)
  (children : DataExpressionSequence.Tree callerSource
    (CompatibleExpressionBuiltinRuntime.Certificate readFuel values callerSource callerContext callerSolved callerReasonAt)
    scope receipt.arguments (named.inputs.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments)
  (nativeTypes : receipt.loweredArguments.map (·.type) = named.inputs.map Prod.snd)


variable {methods : Methods (prepared := prepared) (values := values) (ambient := ambient)
    (registry := registry) (faults := faults) (program := program) (context := callerContext) (evidence := callerEvidence)}
  (suffixUninitialized : ∀ method ∈ methods, ∀ id location,
    faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (suffixMissing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  (suffixEscaped : ∀ method ∈ methods, faults .controlEscapedFunction method.compiled.own.table.escapedReason)
  {ξ : Renaming} {calls : List CallableCoercionSpine.Call}
  (emitted : Emitted checkedProgram project compilation caller receipt.available scope node policy ξ receipt.operand methods output calls)
  (steps : methods.map (·.step) = node.coercions)
  (chain : ChainFor Method.row sourceBody.resultType receipt.operand.type methods node.type output.type)

/-- Preservation is deliberately restricted to the raw operator's actual
selected argument/body trace and the same ordered suffix dictionaries. -/
abbrev Trace (sourceEnvironment : Dynamic.Environment) (before : Dynamic.Heap) :=
  CallableCoercionExpressionMeaning.TraceFor
    (NamedCalls.Arguments.Trace program callerContext callerEvidence dictionary callerSource sourceEnvironment
      before receipt.arguments sourceBody)
    (SelectedTraceFor Method.row program methods)

include selected selection steps in
theorem Trace.source {sourceEnvironment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (trace : Trace (sourceBody := sourceBody) (dictionary := dictionary) (program := program) (receipt := receipt) (methods := methods) sourceEnvironment before outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after := by
  apply CallableCoercionExpressionMeaning.Trace.source receipt.found
  cases trace with
  | rawFault raw => exact .rawFault (selected.raw selection raw)
  | path raw path =>
    refine .path (selected.raw selection raw) ?_
    have actual := path_source path
    simpa only [steps] using actual

include alignment in
private theorem operand_type : receipt.operand.type = named.signature.resultType := by
  simpa only [alignment.signature] using congrArg SourceCoreBasic.LoweredExpr.type receipt.native.emitted

include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes profile alignment selected selection suffixUninitialized suffixMissing suffixEscaped emitted steps chain in
/-- The original raw operator and every selected output conversion are closed
by their actual runtime trees. No child or body execution law is an input. -/
theorem preserves {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment canonical : Environment}
    {callerAdministrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {outcome : Dynamic.ExpressionOutcome}
    (installed : CallablePreparedMethodRuntimeMeaning.Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
    (suffixEntry : Entry methods functions callerEnvironment mapping world before store)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      callerAdministrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (unique : NodeOccurrencesUnique callerSource)
    (execution : Trace (sourceBody := sourceBody) (dictionary := dictionary) (program := program) (receipt := receipt) (methods := methods) sourceEnvironment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      Evaluates callerEnvironment store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods functions callerEnvironment finalMap finalWorld after finalStore) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  have packedType : named.signature.parameterType = (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
    simpa only [alignment.signature] using receipt.native.inputType
  have operandCode := alignment.operand_emitted receipt ξ
  rw [← located] at operandCode
  have wholeCode : output.expression.rename ξ = CallableCoercionSpine.emit compilation.internalReason
      (receipt.operand.expression.rename ξ) (methods.map (·.call)) := by
    rw [emitted.spine.code, CallableCoercionSpine.emit_rename, ← emitted.calls_eq]
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, next⟩ :=
    CallableCoercionExpressionMeaning.preserves_for functions
      (State := Entry methods functions callerEnvironment)
      (fun entry maps worlds frame metadata => entry.extend maps worlds frame metadata)
      chain.final_type suffixEntry wholeCode
      (fun raw => by
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, _, _⟩ :=
          call_preserves compiled profile functions extension program faithful observations functionTypes uninitialized missing escaped
            callerValid callerUninitialized callerMissing children nativeTypes packedType
            installed environments heaps locals layout actualTyped unique raw
        exact ⟨value, finalStore, finalMap, finalWorld, operandCode.symm ▸ evaluated,
          by simpa only [operand_type receipt alignment] using related,
          finalHeaps, maps, worlds, frame, metadata⟩)
      (fun entry heaps represented trace => path_preserves functions extension faithful observations functionTypes
        suffixUninitialized suffixMissing suffixEscaped chain entry heaps represented trace compilation.internalReason)
      execution
  let original := installed.extend maps worlds frame metadata
  exact ⟨value, finalStore, finalMap, finalWorld, Trace.source (program := program) (receipt := receipt) (selected := selected) (selection := selection) (steps := steps) execution,
    evaluated, related, finalHeaps, maps, worlds, frame, metadata, next, original.caller, original.snapshots⟩

include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes profile alignment selected selection suffixUninitialized suffixMissing suffixEscaped emitted steps chain in
/-- Completed output code supplies the original measured operand and each
actual suffix body. Reflection does not require a source completion. -/
theorem reflects_sized {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment canonical : Environment}
    {callerAdministrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {value : Value} {size : Nat}
    (installed : CallablePreparedMethodRuntimeMeaning.Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
    (suffixEntry : Entry methods functions callerEnvironment mapping world before store)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      callerAdministrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (completed : EvaluationSize size callerEnvironment store (output.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods functions callerEnvironment finalMap finalWorld after finalStore) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  have packedType : named.signature.parameterType = (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
    simpa only [alignment.signature] using receipt.native.inputType
  have operandCode := alignment.operand_emitted receipt ξ
  rw [← located] at operandCode
  let E := fun native middleStore => ∃ child, child ≤ size ∧
    EvaluationSize child callerEnvironment store (receipt.operand.expression.rename ξ) native middleStore
  have completedPrefix : ∃ native middleStore, E native middleStore ∧
      CallableCoercionSpine.RunsFor (CallableCoercionSpine.InvokeSized size callerEnvironment compilation.internalReason)
        middleStore native (methods.map (·.call)) value finalStore := by
    obtain ⟨child, native, middleStore, within, _strict, operand, runs⟩ := emitted.spine.renamed_completed_sized ξ completed
    exact ⟨native, middleStore, ⟨child, within, operand⟩, emitted.calls_eq.symm ▸ runs⟩
  obtain ⟨outcome, after, finalMap, finalWorld, execution, related, finalHeaps, maps, worlds, frame, metadata, next⟩ :=
    CallableCoercionExpressionMeaning.reflects_for functions
      (State := Entry methods functions callerEnvironment)
      (rawTrace := NamedCalls.Arguments.Trace program callerContext callerEvidence dictionary callerSource sourceEnvironment
        before receipt.arguments sourceBody)
      (pathTrace := SelectedTraceFor Method.row program methods)
      (fun entry maps worlds frame metadata => entry.extend maps worlds frame metadata)
      chain.final_type suffixEntry (fun invoked => invoked.forget)
      (fun original => by
        obtain ⟨child, _within, operand⟩ := original
        rw [operandCode] at operand
        obtain ⟨outcome, after, finalMap, finalWorld, raw, related, finalHeaps, maps, worlds, frame, metadata, _, _⟩ :=
          call_reflects_sized compiled profile functions extension program faithful observations functionTypes uninitialized missing escaped
            callerValid callerUninitialized callerMissing children nativeTypes packedType
            installed environments heaps locals layout actualTyped operand
        exact ⟨outcome, after, finalMap, finalWorld, raw,
          by simpa only [operand_type receipt alignment] using related,
          finalHeaps, maps, worlds, frame, metadata⟩)
      (fun entry heaps represented runs => path_reflects functions extension faithful observations functionTypes
        suffixUninitialized suffixMissing suffixEscaped chain entry heaps represented runs)
      completedPrefix
  let original := installed.extend maps worlds frame metadata
  exact ⟨outcome, after, finalMap, finalWorld, Trace.source (program := program) (receipt := receipt) (selected := selected) (selection := selection) (steps := steps) execution,
    related, finalHeaps, maps, worlds, frame, metadata, next, original.caller, original.snapshots⟩

end Operator

end Solcore.SourceSemantics.CoreLowering.CallablePreparedOperatorSuffixMeaning
