import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodOriginMeaning
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning

/-! The actual compiled hook is consumed with concrete builtin certificates.
The formal consumer keeps its complete caller state and independent source
outcome, and takes no body or expression execution law. No new runtime runner. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePreparedMethodOriginMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedParameterCertificates
open CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallablePreparedMethodRuntimeMeaning CallablePreparedMethodCatalogEntries
open CallablePreparedMethodCatalogHookMeaning

open CallablePreparedMethodOriginMeaning

abbrev original_hook := @CallablePreparedMethodOriginMeaning.ProfileFor.reflects_hook_of_below
abbrev actual_prefix := @CallablePreparedMethodOriginMeaning.entry_of_prefix
abbrev source_child := @CallablePreparedMethodOriginMeaning.ProfileFor.preserves_reached_of_below

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


def builtinOrigin : CallableRuntimeBodyOrigins.Origin values ambient registry faults :=
  CallablePreparedMethodOriginMeaning.ProfileFor.origin
    (headers := headers) (locations := locations) (capturePrefix := capturePrefix) (callerPrefix := callerPrefix)
    compiled (of_builtin compiled profile) escaped (fun valid extended => valid.extend extended) (fun valid => valid)

include profile extension faithful observations functionTypes escaped uninitialized missing in
/-- Concrete builtin leaves internally close the source family at the original body grade. -/
theorem closed_builtin_source (size : Nat) : CallableRuntimeBodyOrigins.PreservesAt functions program
    (builtinOrigin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      (callerPrefix := callerPrefix) compiled profile escaped) size := by
  apply CallableRuntimeBodyMutualMeaning.preserves_at
    (fun _ : Unit => builtinOrigin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      (callerPrefix := callerPrefix) compiled profile escaped) functions extension program faithful observations ?_ size ()
  intro _ context valid budget child within _ scope id lowered
  exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
    (ProtectedExpressionMeaning.preserves_of_typed _
      (CompatibleExpressionBuiltinRuntime.preserves (fuel := profile.readFuel) functions extension faithful observations functionTypes
        program dictionary valid.ledger valid.runtime profile.body.unique uninitialized missing)) child
    (scope := scope) (id := id) (lowered := lowered)

include profile extension faithful observations functionTypes escaped uninitialized missing in
/-- The native family starts from its own completed body and returns an independent source grade. -/
theorem closed_builtin_native (size : Nat) : CallableRuntimeBodyOrigins.ReflectsAt functions program
    (builtinOrigin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      (callerPrefix := callerPrefix) compiled profile escaped) size := by
  apply CallableRuntimeBodyMutualMeaning.reflects_at
    (fun _ : Unit => builtinOrigin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      (callerPrefix := callerPrefix) compiled profile escaped) functions extension program faithful observations functionTypes ?_ size ()
  intro _ context valid budget child within _ scope id lowered
  exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
    (ProtectedExpressionMeaning.reflects_of_typed _
      (CompatibleExpressionBuiltinRuntime.reflects (fuel := profile.readFuel) functions extension faithful observations functionTypes
        program dictionary valid.ledger valid.runtime uninitialized missing)) child
    (scope := scope) (id := id) (lowered := lowered)

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
  exact CallablePreparedMethodOriginMeaning.ProfileFor.reflects_hook_of_below compiled (of_builtin compiled profile)
    functions escaped (fun valid extended => valid.extend extended) (fun valid => valid) size
    installed initial sameFrame represented heaps (Nat.le_refl size)
    (fun child _ => closed_builtin_native compiled profile functions extension faithful observations functionTypes
      escaped uninitialized missing child) completed

/-- The dictionary is exactly the one in the actual selected method profile. -/
theorem same_dictionary :
    (builtinOrigin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      (callerPrefix := callerPrefix) compiled profile escaped).function.evidence = dictionary := rfl

/-- Full method provenance is protected, including the actual source frame and history. -/
theorem same_protected_entry :
    (builtinOrigin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      (callerPrefix := callerPrefix) compiled profile escaped).protectedEntry =
      protectedEntry named sourceBody (methodFunction compiled sourceBody dictionary)
        headers locations capturePrefix (callerPrefix + 1) := rfl

include profile in
/-- Zero parameters retain the real packed slot. -/
theorem empty_pack (empty : named.inputs = []) : named.signature.parameterType = .unit := by
  simpa only [empty, List.map_nil, SourceCoreCompatibleCatalog.packTypes] using profile.parameterType

#check_failure CallablePreparedMethodOriginMeaning.ProfileFor.preserves_hook
#check_failure CallablePreparedMethodOriginMeaning.ProfileFor.with_evidence

end Tests.SourceCoreCallablePreparedMethodOriginMeaning
