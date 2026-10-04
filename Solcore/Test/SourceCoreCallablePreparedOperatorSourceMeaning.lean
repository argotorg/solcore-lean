import Solcore.SourceSemantics.CoreLowering.CallablePreparedOperatorSourceMeaning
import Solcore.Test.SourceCoreCallablePreparedOperatorSuffixMeaning

/-! Independent source completion and the original native completion meet at
one actual operator and ordered suffix. Static profiles retain full runtime
ledgers when source selection chooses its own covered dictionary. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePreparedOperatorSourceMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CoreProof ReadOnly CompatiblePayload CallableIndexedHistory
open CallablePreparedOperatorSuffixMeaning

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure CallablePreparedOperatorSuffixMeaning.Method.ordinary

section Actual
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
  (program : SourceSemantics.Program) {identities : Dynamic.Value → Word → Prop}
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
  (chain : CallableCoercionPathMeaning.ChainFor Method.row sourceBody.resultType receipt.operand.type methods node.type output.type)


include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes profile alignment selected selection suffixUninitialized suffixMissing suffixEscaped emitted steps chain in
/-- The original raw operator and every selected output conversion are closed
by their actual runtime trees. No child or body execution law is an input. -/
theorem actual_preserves {rawWorkspace : Workspace.RawWorkspace} {checkFuel : Nat}
    (checkedAccepted : checkProgram rawWorkspace checkFuel = .ok checkedProgram)
    (sourceProgram : program = SourceSemantics.Program.ofChecked checkedProgram)
    (ledger : callerContext.solvedRequirements = caller.function.solvedRequirements) {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
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
  exact CallablePreparedOperatorSourceMeaning.preserves
    (compiled := compiled) (profile := profile) (functions := functions) (extension := extension)
    (program := program) (faithful := faithful) (observations := observations) (functionTypes := functionTypes)
    (uninitialized := uninitialized) (missing := missing) (escaped := escaped) (callerValid := callerValid)
    (callerUninitialized := callerUninitialized) (callerMissing := callerMissing) (receipt := receipt) (alignment := alignment)
    (selected := selected) (selection := selection) (children := children) (nativeTypes := nativeTypes)
    (suffixUninitialized := suffixUninitialized) (suffixMissing := suffixMissing) (suffixEscaped := suffixEscaped) (emitted := emitted)
    (steps := steps) (chain := chain)
    (catalog := by simpa only [sourceProgram] using CallableCoercionSelectionIdentity.Catalog.of_checked checkedAccepted)
    (ledger := ledger) installed located suffixEntry environments heaps locals layout actualTyped unique execution
include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes profile alignment selected selection suffixUninitialized suffixMissing suffixEscaped emitted steps chain in
/-- Completed output code supplies the original measured operand and each
actual suffix body. Reflection does not require a source completion. -/
theorem actual_reflects {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
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
  exact CallablePreparedOperatorSourceMeaning.reflects_sized
    (compiled := compiled) (profile := profile) (functions := functions) (extension := extension)
    (program := program) (faithful := faithful) (observations := observations) (functionTypes := functionTypes)
    (uninitialized := uninitialized) (missing := missing) (escaped := escaped) (callerValid := callerValid)
    (callerUninitialized := callerUninitialized) (callerMissing := callerMissing) (receipt := receipt) (alignment := alignment)
    (selected := selected) (selection := selection) (children := children) (nativeTypes := nativeTypes)
    (suffixUninitialized := suffixUninitialized) (suffixMissing := suffixMissing) (suffixEscaped := suffixEscaped) (emitted := emitted)
    (steps := steps) (chain := chain)
    installed located suffixEntry environments heaps locals layout actualTyped completed

end Actual

abbrev original_native_children := @CallableCoercionSpine.Spine.renamed_completed_sized
abbrev independent_raw_dictionary := @CallablePreparedOperatorSourceMeaning.OperatorSource.raw_inv
abbrev original_raw_middle_heap := @CallablePreparedOperatorSourceMeaning.OperatorSource.source_inv

section Boundaries
open CallablePreparedMethodRuntimeMeaning
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  {compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {oldDictionary dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : Profile compiled values ambient sourceBody oldDictionary administrative registry faults)
  (covers : dictionary.Covers sourceBody.context)

theorem same_runtime_tree :
    (profile.with_evidence dictionary covers).body.tree = profile.body.tree := rfl

theorem same_emitted_body :
    (profile.with_evidence dictionary covers).body.flow = profile.body.flow := rfl

theorem full_runtime_ledger :
    (profile.with_evidence dictionary covers).context.solvedRequirements =
      named.specialized.function.solvedRequirements := profile.body.valid.ledger

theorem actual_covered_dictionary :
    dictionary.Covers (profile.with_evidence dictionary covers).context :=
  (profile.with_evidence dictionary covers).body.valid.covers

variable {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  (method : Method prepared values ambient registry faults program context evidence)
  (selected : Dynamic.OperatorMethodSelected program context evidence "Coerce" "coerce"
    method.step.requirements method.sourceBody dictionary)

theorem same_actual_row :
    (CallablePreparedOperatorSourceMeaning.method_with_evidence method dictionary selected).call = method.call := rfl

theorem source_dictionary :
    (CallablePreparedOperatorSourceMeaning.method_with_evidence method dictionary selected).dictionary = dictionary := rfl

theorem repeated_order (other : Dynamic.EvidenceEnvironment)
    (otherSelected : Dynamic.OperatorMethodSelected program context evidence "Coerce" "coerce"
      method.step.requirements method.sourceBody other) :
    [CallablePreparedOperatorSourceMeaning.method_with_evidence method dictionary selected,
     CallablePreparedOperatorSourceMeaning.method_with_evidence method other otherSelected].map (·.dictionary) =
      [dictionary, other] := rfl

/-- The generic outer trace keeps the successful raw heap distinct from the
suffix's final heap; no equality between the two is needed. -/
theorem raw_middle_heap {rawTrace : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop}
    {pathTrace : Dynamic.Heap → Dynamic.Value → Dynamic.ExpressionOutcome → Dynamic.Heap → Prop}
    {value : Dynamic.Value} {middle after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (raw : rawTrace (.value value) middle) (suffix : pathTrace middle value outcome after) :
    CallableCoercionExpressionMeaning.TraceFor rawTrace pathTrace outcome after := .path raw suffix

end Boundaries

/-- Reuse the actual public success/raw/first/later-fault fixture once. -/
def run : IO Unit := SourceCoreCallablePreparedOperatorSuffixMeaning.run

end Tests.SourceCoreCallablePreparedOperatorSourceMeaning
