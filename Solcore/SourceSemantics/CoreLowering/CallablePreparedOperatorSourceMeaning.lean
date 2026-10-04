import Solcore.SourceSemantics.CoreLowering.CallablePreparedOperatorSourceBounds
import Solcore.SourceSemantics.CoreLowering.CallablePreparedOperatorSuffixMeaning
import Solcore.SourceSemantics.CoreLowering.CallableCoercionSourcePathMeaning
import Solcore.SourceSemantics.CoreLowering.CallableCallRequirementLayouts

/-! Independently evaluated source operators retain their own dictionaries.
Actual selection identifies the full body, while coverage reindexes only the
static evidence view. Native code, captures, histories and ordered suffix rows
remain those of the original compilation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory

/-- Coverage changes the source evidence index while preserving the complete
runtime ledger, actual flow/tree/sites, emitted body and parameter context. -/
def Profile.with_evidence
    {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    {compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code}
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {body : Dynamic.BodyInstance} {oldDictionary : Dynamic.EvidenceEnvironment}
    {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (profile : Profile compiled values ambient body oldDictionary administrative registry faults)
    (dictionary : Dynamic.EvidenceEnvironment) (covers : dictionary.Covers body.context) :
    Profile compiled values ambient body dictionary administrative registry faults :=
  { profile with
    sourceFrame := { profile.sourceFrame with covers }
    body := profile.body.with_evidence dictionary
      ((RecursiveNamedInitialContextValidity.mono_fields profile.extended).covers covers) }

end Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeMeaning

namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedOperatorSourceMeaning
open Core CoreProof Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory
open SourceCoreCallableIndexedFrames CallableIndexedParameterMeaning
open CallableCoercionPathMeaning CallablePreparedOperatorSuffixMeaning

section Rows
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}

/-- This is a static source-evidence view of the same compiled method. Its
new dictionary is not asserted equal to the compiler's retained annotation. -/
def method_with_evidence (method : Method prepared values ambient registry faults program context evidence)
    (dictionary : Dynamic.EvidenceEnvironment)
    (selected : Dynamic.OperatorMethodSelected program context evidence "Coerce" "coerce"
      method.step.requirements method.sourceBody dictionary) :
    Method prepared values ambient registry faults program context evidence :=
  { method with
    dictionary := dictionary
    selected := selected
    profile := method.profile.with_evidence dictionary (by
      cases selected with | intro _ _ _ _ _ _ _ _ _ _ _ _ _ covers => exact covers) }

variable {methods : Methods (prepared := prepared) (values := values) (ambient := ambient)
    (registry := registry) (faults := faults) (program := program) (context := context) (evidence := evidence)}
  {caller : Environment} {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (uninitialized : ∀ method ∈ methods, ∀ id location,
    faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  (escaped : ∀ method ∈ methods, faults .controlEscapedFunction method.compiled.own.table.escapedReason)

include extension faithful observations runtimeViews uninitialized missing escaped in
/-- The concrete body is evaluated at the independent source dictionary. Its
saved closure, original physical slot and every future suffix capture stay fixed. -/
theorem method_preserves_at_source {method : Method prepared values ambient registry faults program context evidence}
    (member : method ∈ methods) {input : Dynamic.Value} {native : Value} {outcome : Dynamic.ExpressionOutcome}
    (entry : Entry methods functions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world method.step.source input native method.call.signature.parameterType)
    {dictionary : Dynamic.EvidenceEnvironment}
    (selected : Dynamic.OperatorMethodSelected program context evidence "Coerce" "coerce"
      method.step.requirements method.sourceBody dictionary)
    (trace : NamedCalls.BodyOutcome program method.sourceBody dictionary before [input] outcome after)
    (reason : Word) :
    ∃ value finalStore finalMap finalWorld,
      CallableCoercionSpine.Invoke caller reason method.call store (.inRight .word native) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        method.step.target method.call.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods functions caller finalMap finalWorld after finalStore) := by
  let viewed := method_with_evidence method dictionary selected
  obtain ⟨capture⟩ := entry.captures method member
  have viewedEntry : Entry [viewed] functions caller mapping world before store :=
    ⟨fun other member => by
      have same := List.mem_singleton.mp member
      subst other
      exact ⟨⟨capture.installed, capture.index⟩⟩⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, invoked, related, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    CallablePreparedOperatorSuffixMeaning.method_preserves functions extension faithful observations runtimeViews
      (fun other singleMember => by cases List.mem_singleton.mp singleMember; exact uninitialized method member)
      (fun other singleMember => by cases List.mem_singleton.mp singleMember; exact missing method member)
      (fun other singleMember => by cases List.mem_singleton.mp singleMember; exact escaped method member)
      (List.mem_singleton_self viewed) viewedEntry heaps represented trace reason
  exact ⟨value, finalStore, finalMap, finalWorld, invoked, related, finalHeaps, maps, worlds, frame, metadata,
    ⟨entry.extend maps worlds frame metadata⟩⟩

section Emission
variable {compilerProgram : CheckedProgram} {project : SourceCoreEvidence.Projector}
  {compilation : SourceCoreFunctions.Context} {callerFunction : SourceSpecialization.SpecializedFunction}
  {available : SourceCompilationPlan.EvidenceEnvironment} {scope : SourceCoreBasic.Scope}
  {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy} {ξ : Renaming}
  {inputCode outputCode : SourceCoreBasic.LoweredExpr} {calls : List CallableCoercionSpine.Call}

private theorem emitted_selection
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode methods outputCode calls)
    {method : Method prepared values ambient registry faults program context evidence} (member : method ∈ methods) :
    ∃ selected, SourceCompilationPlan.checkedCoercionMethod compilerProgram callerFunction node available method.step = .ok selected := by
  induction emitted with
  | nil => cases member
  | cons actual _ _ _ tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, actual.selectedMethod⟩
    · exact ih member

variable (catalog : CallableCoercionSelectionIdentity.Catalog program)
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)

include extension faithful observations runtimeViews uninitialized missing escaped catalog ledger in
/-- An independently evaluated path keeps each source-selected dictionary.
The real compiler rows fix only its complete body and reached requirement rows. -/
theorem path_preserves_source
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode methods outputCode calls)
    {source target : TypeSystem.Ty} {inputType outputType : Ty}
    (chain : ChainFor Method.row source inputType methods target outputType)
    {input : Dynamic.Value} {native : Value} {outcome : Dynamic.ExpressionOutcome}
    (entry : Entry methods functions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputType)
    (trace : CallableCoercionSourcePathMeaning.PathFor Method.row program context evidence methods before input outcome after)
    (reason : Word) :
    ∃ value finalStore finalMap finalWorld,
      CallableCoercionSpine.Runs caller reason store (.inRight .word native) (methods.map (·.call)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods functions caller finalMap finalWorld after finalStore) := by
  apply CallableCoercionSourcePathMeaning.preserves_for (row := Method.row)
    (State := fun mapping world heap store => Entry methods functions caller mapping world heap store)
    (fun entry maps worlds frame metadata => entry.extend maps worlds frame metadata)
    (functions := functions) (registry := registry) (faults := faults) (program := program)
    (context := context) (evidence := evidence) (caller := caller) (reason := reason)
    (chain := chain) (entry := entry) (heaps := heaps) (represented := represented) (trace := trace)
  intro method mapping world before after store input native outcome member entry heaps represented execution
  obtain ⟨selectedMethod, accepted⟩ := emitted_selection emitted member
  obtain ⟨receipt⟩ := CallableCoercionMethodCertificates.of_accepted accepted
  have sameBody : ∀ {selectedBody dictionary},
      Dynamic.OperatorMethodSelected program context evidence "Coerce" "coerce"
        method.step.requirements selectedBody dictionary → selectedBody = method.sourceBody :=
    fun selected => CallableCoercionSelectionIdentity.body_eq catalog
      (CallableCoercionSelectionIdentity.primary_unique ledger receipt.primarySelected) selected method.selected
  cases outcome with
  | value value =>
    cases execution with
    | primitive absent _ => exact False.elim (absent _ _ method.selected)
    | method selected invoked =>
      cases sameBody selected
      exact method_preserves_at_source functions extension faithful observations runtimeViews
        uninitialized missing escaped member entry heaps represented selected (.value invoked) reason
  | fault failed =>
    cases execution with
    | requirement unavailable =>
      exact False.elim (CallableCoercionRequirementSafety.selected_safe_for ledger receipt.roots method.selected unavailable)
    | primitiveInput absent _ _ => exact False.elim (absent _ _ method.selected)
    | method selected bodyFailed =>
      cases sameBody selected
      exact method_preserves_at_source functions extension faithful observations runtimeViews
        uninitialized missing escaped member entry heaps represented selected (.fault bodyFailed) reason

end Emission

end Rows

section SourceInversion
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallablePreparedMethodSelection CallablePreparedMethodRuntimeMeaning
open CallableCoercionExpressionCertificates (Projector Specialized Lowered)

private theorem unary_dispatch_unique {operator : Syntax.UnaryOp}
    {leftTrait leftMethod rightTrait rightMethod : String}
    (left : UnaryTraitDispatch operator leftTrait leftMethod)
    (right : UnaryTraitDispatch operator rightTrait rightMethod) :
    leftTrait = rightTrait ∧ leftMethod = rightMethod :=
  CallablePreparedOperatorSourceBounds.unary_dispatch_unique left right

private theorem binary_dispatch_valid_left {operator : Syntax.BinaryOp}
    {traitName methodName : String} {value : Dynamic.Value}
    (dispatch : BinaryTraitDispatch operator traitName methodName)
    (invalid : Dynamic.BinaryLeftOperandInvalid operator value) : False :=
  CallablePreparedOperatorSourceBounds.binary_dispatch_valid_left dispatch invalid

private theorem binary_dispatch_unique {operator : Syntax.BinaryOp}
    {leftTrait leftMethod rightTrait rightMethod : String}
    (left : BinaryTraitDispatch operator leftTrait leftMethod)
    (right : BinaryTraitDispatch operator rightTrait rightMethod) :
    leftTrait = rightTrait ∧ leftMethod = rightMethod :=
  CallablePreparedOperatorSourceBounds.binary_dispatch_unique left right

variable {checkedProgram : CheckedProgram} {project : Projector} {caller : Specialized}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  {receipt : Operator checkedProgram project caller compilation child fuel source scope id reasonAt policy node output}
  (selected : OperatorSource receipt)
  {program : Program} {context : SourceSemantics.Context} {evidence dictionary : Dynamic.EvidenceEnvironment}
  {sourceBody : Dynamic.BodyInstance}
  (catalog : CallableCoercionSelectionIdentity.Catalog program)
  (ledger : context.solvedRequirements = caller.function.solvedRequirements)
  (selection : Dynamic.OperatorMethodSelected program context evidence selected.traitName selected.methodName
    receipt.requirements sourceBody dictionary)

private theorem owned_eq {owned : List RequirementId}
    (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions owned) :
    owned = receipt.requirements :=
  CallablePreparedOperatorSourceBounds.owned_eq layout

include selected catalog ledger selection in
private theorem same_body {otherBody : Dynamic.BodyInstance} {otherDictionary : Dynamic.EvidenceEnvironment}
    (actual : Dynamic.OperatorMethodSelected program context evidence selected.traitName selected.methodName
      receipt.requirements otherBody otherDictionary) : otherBody = sourceBody :=
  CallablePreparedOperatorSourceBounds.same_body selected catalog ledger selection actual

include selected ledger selection in
private theorem requirement_safe {failed : RequirementId}
    (fault : Dynamic.RequirementListFaults context evidence receipt.requirements failed) : False :=
  CallablePreparedOperatorSourceBounds.requirement_safe selected ledger selection fault

include selected catalog ledger selection in
/-- Reverse the original raw source outcome, preserving each actual source
dictionary. An argument fault retains the anchor selection without invoking it. -/
theorem OperatorSource.raw_inv {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (raw : CallableCoercionExpressionMeaning.RawOutcome program context evidence source environment before node outcome after) :
    ∃ actualDictionary,
      Dynamic.OperatorMethodSelected program context evidence selected.traitName selected.methodName
        receipt.requirements sourceBody actualDictionary ∧
      NamedCalls.Arguments.Trace program context evidence actualDictionary source environment before
        receipt.arguments sourceBody outcome after := by
  obtain ⟨size, measured⟩ : ∃ size,
      CallablePreparedOperatorSourceBounds.RawOutcomeAt program size context evidence source environment before node outcome after := by
    cases outcome with
    | value value => exact SourceExecutionSize.ExpressionFormEvaluates.has_size raw
    | fault reason => exact SourceExecutionSize.ExpressionFormFaults.has_size raw
  obtain ⟨actualDictionary, actual, traced⟩ :=
    CallablePreparedOperatorSourceBounds.OperatorSource.raw_inv_sized selected catalog ledger selection measured
  exact ⟨actualDictionary, actual, traced.sound⟩

include selected catalog ledger selection in
/-- Whole source outcomes retain the raw intermediate value and heap before
the original nonempty suffix. Neither its requirements nor its order changes. -/
theorem OperatorSource.source_inv {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique source)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    CallableCoercionExpressionMeaning.TraceFor
      (fun rawOutcome rawHeap => ∃ actualDictionary,
        Dynamic.OperatorMethodSelected program context evidence selected.traitName selected.methodName
          receipt.requirements sourceBody actualDictionary ∧
        NamedCalls.Arguments.Trace program context evidence actualDictionary source environment before
          receipt.arguments sourceBody rawOutcome rawHeap)
      (fun heap value => CallableCoercionExpressionMeaning.Path program context evidence heap node.coercions value)
      outcome after := by
  obtain ⟨size, measured⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size trace
  exact (CallablePreparedOperatorSourceBounds.OperatorSource.source_inv_sized
    selected catalog ledger selection unique measured).forget
    (fun ⟨actualDictionary, actual, traced⟩ => ⟨actualDictionary, actual, traced.sound⟩)
    CallablePreparedOperatorSourceBounds.PathAt.sound

end SourceInversion

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


include alignment in
private theorem operand_type : receipt.operand.type = named.signature.resultType := by
  simpa only [alignment.signature] using congrArg SourceCoreBasic.LoweredExpr.type receipt.native.emitted


variable (catalog : CallableCoercionSelectionIdentity.Catalog program)
  (ledger : callerContext.solvedRequirements = caller.function.solvedRequirements)

include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes profile alignment selected selection suffixUninitialized suffixMissing suffixEscaped emitted steps chain catalog ledger in
/-- An independent whole source outcome supplies its own raw and suffix
dictionaries. Actual selection fixes the full bodies; their static runtime
trees close every child and body execution obligation internally. -/
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
    (execution : Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after) :
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
  have trace := OperatorSource.source_inv selected catalog ledger selection unique execution
  have packedType : named.signature.parameterType = (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
    simpa only [alignment.signature] using receipt.native.inputType
  have operandCode := alignment.operand_emitted receipt ξ
  rw [← located] at operandCode
  have wholeCode : output.expression.rename ξ = CallableCoercionSpine.emit compilation.internalReason
      (receipt.operand.expression.rename ξ) (methods.map (·.call)) := by
    rw [emitted.spine.code, CallableCoercionSpine.emit_rename, ← emitted.calls_eq]
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, next⟩ :=
    CallableCoercionExpressionMeaning.preserves_for functions
      (sourceType := sourceBody.resultType) (targetType := node.type)
      (State := Entry methods functions callerEnvironment)
      (fun entry maps worlds frame metadata => entry.extend maps worlds frame metadata)
      chain.final_type suffixEntry wholeCode
      (fun raw => by
        obtain ⟨actualDictionary, actualSelection, raw⟩ := raw
        have covers : actualDictionary.Covers sourceBody.context := by
          generalize receipt.requirements = requirements at actualSelection
          cases actualSelection with | intro _ _ _ _ _ _ _ _ _ _ _ _ _ covers => exact covers
        let sourceProfile := profile.with_evidence actualDictionary covers
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, _, _⟩ :=
          call_preserves compiled sourceProfile functions extension program faithful observations functionTypes uninitialized missing escaped
            callerValid callerUninitialized callerMissing children nativeTypes packedType
            installed environments heaps locals layout actualTyped unique raw
        exact ⟨value, finalStore, finalMap, finalWorld, operandCode.symm ▸ evaluated,
          by simpa only [operand_type receipt alignment] using related,
          finalHeaps, maps, worlds, frame, metadata⟩)
      (fun {nextMap nextWorld rawBefore rawAfter nextStore input native result} entry heaps represented path => by
        have path' : CallableCoercionSourcePathMeaning.PathFor Method.row program callerContext callerEvidence
            methods rawBefore input result rawAfter := by
          cases result <;> simpa only [CallableCoercionSourcePathMeaning.PathFor, CallableCoercionExpressionMeaning.Path, Method.row, steps] using path
        exact path_preserves_source functions extension faithful observations functionTypes
          suffixUninitialized suffixMissing suffixEscaped catalog ledger emitted chain entry heaps represented path' compilation.internalReason)
      trace
  let original := installed.extend maps worlds frame metadata
  exact ⟨value, finalStore, finalMap, finalWorld, execution,
    evaluated, related, finalHeaps, maps, worlds, frame, metadata, next, original.caller, original.snapshots⟩


include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes profile alignment selected selection suffixUninitialized suffixMissing suffixEscaped emitted steps chain in
/-- The original measured native completion uses the established suffix
reflection directly, with no source execution or dictionary equality premise. -/
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
  exact CallablePreparedOperatorSuffixMeaning.reflects_sized compiled profile functions extension program
    faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
    receipt alignment selected selection children nativeTypes suffixUninitialized suffixMissing suffixEscaped
    emitted steps chain installed located suffixEntry environments heaps locals layout actualTyped completed

end Operator

end Solcore.SourceSemantics.CoreLowering.CallablePreparedOperatorSourceMeaning
