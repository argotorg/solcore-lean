import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogHookMeaning

/-! The actual compiled hook is consumed with concrete builtin certificates.
The formal consumer keeps its complete caller state and independent source
outcome, and takes no body or expression execution law. No new runtime runner. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePreparedMethodCatalogHookMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedParameterCertificates
open CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallablePreparedMethodRuntimeMeaning CallablePreparedMethodCatalogEntries
open CallablePreparedMethodCatalogHookMeaning

abbrev original_hook := @reflects_hook_sized
abbrev generic_compiled := @ProfileFor.reflects_sized

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

variable (profile : CallablePreparedMethodRuntimeMeaning.Profile compiled values ambient sourceBody dictionary
    administrative registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {program : SourceSemantics.Program}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values ambient.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values) (ambient := ambient) (program := program)}
  {capturePrefix callerPrefix : Nat}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (escaped : faults .controlEscapedFunction compiled.own.table.escapedReason)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) ((diagnostics.reasonAt named.signature.key) id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) (((diagnostics.reasonAt named.signature.key) id).add tag))

include profile extension faithful observations functionTypes escaped uninitialized missing in
theorem closed_builtin_compiled {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    {size : Nat} {value : Value}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
    (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store installed.canonical)
    (sameFrame : initial.authority.frameLocation = installed.frameLocation)
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world named.inputs arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: installed.captured) store
      (compiled.output.rename installed.embedding.lift) value finalStore) :
    ∃ sourceSize environment bound outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before sourceBody.source.inputs arguments environment bound ∧
      RecursiveNamedCallBounds.BodyTrace program sourceSize (methodFunction compiled sourceBody dictionary)
        profile.context environment bound outcome after ∧
      CallableCoercionMethodFrame.BodyOutcome program sourceBody dictionary before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative) program
        (methodFunction compiled sourceBody dictionary) profile.context
        (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] finalMap finalWorld after finalStore installed.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  have expressions : ∀ context, CompatibleRuntimeContextValidity.Valid named.specialized.function.solvedRequirements context dictionary →
      RecursiveNamedBoundedContracts.Below size (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context dictionary sourceBody.source
        (CompatibleExpressionBuiltinRuntime.Certificate profile.readFuel values sourceBody.source context
          named.specialized.function.solvedRequirements (diagnostics.reasonAt named.signature.key)) faults
        (protectedEntry named sourceBody (methodFunction compiled sourceBody dictionary)
          headers locations capturePrefix (callerPrefix + 1))) := by
    intro context valid
    exact RecursiveNamedBoundedContracts.reflects_below_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed _
        (CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations functionTypes
          program dictionary valid.ledger valid.runtime uninitialized missing)) size
  exact ProfileFor.reflects_sized compiled (of_builtin compiled profile) functions extension
    faithful observations functionTypes escaped (fun valid extended => valid.extend extended) (fun valid => valid)
    installed initial sameFrame represented heaps expressions completed

/-- The generic receipt preserves the actual compilation output and full dictionary. -/
theorem builtin_dictionary : (of_builtin compiled profile).body.initialValid = profile.body.valid := rfl

include profile in
/-- A zero-arity hook still has its actual pack slot; no strict grade is inferred from arity. -/
theorem empty_parameter_pack (empty : named.inputs = []) : named.signature.parameterType = .unit := by
  simpa only [empty, List.map_nil, SourceCoreCompatibleCatalog.packTypes] using profile.parameterType

-- No dictionary-only reindexing operation is exposed for a generic certificate family.
#check_failure CallablePreparedMethodCatalogHookMeaning.ProfileFor.with_evidence

end Tests.SourceCoreCallablePreparedMethodCatalogHookMeaning
