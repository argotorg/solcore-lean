import Solcore.SourceSemantics.CoreLowering.CompatibleProjectedBitNotStatementHead
import Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceResolution

/-! Shared assignment composition consumes a typed expression meaning contract.
Concrete clients discharge that contract with their own expression Tree theorem.
Seven actual temporary values retain post-write typing and closure captures. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleProjectedBitNotStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CompatibleRenamedPlace DataPlaceExecution DataPatternValues

namespace Head
variable {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel values.checked registry functions)
    program context evidence source certificate faults)
  (reflection : TypedGenericExpressionMeaning.Reflects (payloadModel values.checked registry functions)
    program context evidence source certificate faults)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  {assignment : AssignmentResolution}
  (head : Head values source context certificate scope administrative ambient.definitions assignment)
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)

include extension meaning faithful observations environments heaps locals agrees actualTyped in
theorem preserves_prefix {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      environment before assignment.target updated after) :
    ∃ finalStore finalMap finalWorld slots,
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  cases trace with
  | intro resolve write =>
    obtain ⟨resolution, coreLookup⟩ := CompatibleRenamedPlaceResolution.preserves
      head.layout.path head.layout.views head.layout.children head.layout.keyTypes head.layout.leafProjected
      head.layout.virtual extension head.layout.nonempty
      (getter_typed head.layout (virtual_closed head.layout head.ordinary)
        (environment_respects environments.runtime_hasTypes actualTyped agrees))
      meaning faithful observations environments heaps locals agrees actualTyped head.slot head.writable resolve
    obtain ⟨commit, typed⟩ := ProtectedStagedProjectedBitNotCommit.typed_of_write head.layout head.ordinary extension
      faithful observations head.profile environments agrees actualTyped resolution write
      (binaryOperator (head.prepared.route.leafType = .integer) .equal) head.invalid
    refine ⟨commit.finalStore, resolution.mapping, commit.finalWorld,
      [.unit, commit.value, commit.replacement, .unit, .inRight .unit resolution.snapshot,
        packValues resolution.values, .cellRef (OptionalCell.cellType head.prepared.route.rootType) resolution.target],
      commit.heaps, resolution.maps, resolution.worlds.trans commit.worlds,
      resolution.frame.trans commit.frame, resolution.metadata.trans commit.metadata, rfl, typed, ?_⟩
    intro next output
    change ContinuationAgreement actual store
      ((execute head.prepared (.var head.index) (SourceCoreCalls.packArguments head.codes) (LanguageResult.success .unit)
        next output (binaryOperator (head.prepared.route.leafType = .integer) .equal) true head.invalid).rename ξ) _ _ _
    rw [execute_rename head.layout.path (virtual_closed head.layout head.ordinary)]
    simpa only [renamed_packed, Expr.rename, LanguageResult.success, writtenEnvironment, modifiedEnvironment, rhsEnvironment, snapshotEnvironment, keysEnvironment, referenceEnvironment, List.cons_append, List.nil_append] using
      commit.prefix_agreement resolution coreLookup (next.rename ξ) output

end Head
end Solcore.SourceSemantics.CoreLowering.CompatibleProjectedBitNotStatements
