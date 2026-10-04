import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeMeaning
import Solcore.Test.SourceCoreCallablePreparedMethodSelection

/-! The same actual method compilation, runtime body tree, selected dictionary
and installed histories close both call directions. Ordinary ledger validity
and external child/body execution laws are not inputs. Nonempty output coercion
paths remain a separate consumer; existing public operator IO is reused. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePreparedMethodRuntimeMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CoreProof ReadOnly CompatiblePayload CallableIndexedHistory
open CallablePreparedMethodRuntimeMeaning

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure CallablePreparedMethodRuntimeMeaning.Profile.ordinary

section Actual
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  {compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

variable (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
  (profile : Profile compiled values ambient sourceBody dictionary administrative registry faults)
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

include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes profile alignment selected selection in
theorem actual_source {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment canonical : Environment}
    {callerAdministrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (coercions : node.coercions = [])
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      callerAdministrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (unique : NodeOccurrencesUnique callerSource)
    (execution : NamedCalls.Arguments.Trace program callerContext callerEvidence dictionary callerSource sourceEnvironment
      before receipt.arguments sourceBody outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      Evaluates callerEnvironment store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  exact operator_preserves (compiled := compiled) (profile := profile) (functions := functions) (extension := extension)
    (program := program) (faithful := faithful) (observations := observations) (functionTypes := functionTypes)
    (uninitialized := uninitialized) (missing := missing) (escaped := escaped)
    (callerValid := callerValid) (callerUninitialized := callerUninitialized) (callerMissing := callerMissing)
    (receipt := receipt) (alignment := alignment) (selected := selected) (selection := selection)
    (children := children) (nativeTypes := nativeTypes)
    coercions installed located environments heaps locals layout actualTyped unique execution

include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes profile alignment selected selection in
theorem actual_native {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment canonical : Environment}
    {callerAdministrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {value : Value} {size : Nat}
    (coercions : node.coercions = [])
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
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
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  exact operator_reflects_sized (compiled := compiled) (profile := profile) (functions := functions) (extension := extension)
    (program := program) (faithful := faithful) (observations := observations) (functionTypes := functionTypes)
    (uninitialized := uninitialized) (missing := missing) (escaped := escaped)
    (callerValid := callerValid) (callerUninitialized := callerUninitialized) (callerMissing := callerMissing)
    (receipt := receipt) (alignment := alignment) (selected := selected) (selection := selection)
    (children := children) (nativeTypes := nativeTypes)
    coercions installed located environments heaps locals layout actualTyped completed


include alignment in
theorem retained_full_method : named.specialized = receipt.selection.method.specialized := alignment.retained

include alignment in
theorem actual_dictionary : dictionary = CallableNamedMetadata.environment receipt.dictionary := alignment.dictionary

include profile in
theorem same_full_ledger : profile.context.solvedRequirements = named.specialized.function.solvedRequirements :=
  profile.body.valid.ledger

include profile in
theorem runtime_context : RuntimeRequirementLedgerValid profile.context := profile.body.valid.runtime

include profile in
theorem actual_body_source : sourceBody.source = CallableIndexedNamedGeneration.source named := profile.sameSource

include profile in
theorem ordered_inputs : sourceBody.source.inputs = named.inputs.map Prod.fst := profile.parameters

end Actual

abbrev actual_selected_dispatch := @CallablePreparedMethodRuntimeMeaning.OperatorSource.of_accepted
abbrev original_hook_child := @CallablePreparedMethodRuntimeMeaning.hook_prefix
abbrev original_body_child := @CallablePreparedMethodRuntimeMeaning.Profile.reflects_sized
abbrev same_dictionary_cover := @CallablePreparedMethodRuntimeMeaning.Body.with_evidence

/-- Packing cannot recover source arity: an empty bundle and one Unit payload
have the same native value. Ordered source binders remain explicit. -/
theorem pack_does_not_identify_arity :
    DataPatternValues.packValues [] = DataPatternValues.packValues [Core.Value.unit] ∧
      ([] : List Core.Value) ≠ [.unit] := by
  constructor
  · rfl
  · intro equal; cases equal

/-- Actual public unary/binary methods retain nonempty ordered dictionaries,
unused rows, body effects, a later coercion suffix, and first argument faults.
This reuses their original full source/native heap and resume oracle. -/
def run : IO Unit := Tests.SourceCoreCallablePreparedMethodSelection.run

end Tests.SourceCoreCallablePreparedMethodRuntimeMeaning
