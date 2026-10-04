import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodSourceHookMeaning
import Solcore.Test.SourceCoreCallablePreparedMethodOriginMeaning

/-! Actual source body children execute the real method hook with concrete
builtin leaves. Parameter spines retain the packed slot and full global suffix;
source and native grades remain separate. No new runtime runner. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePreparedMethodSourceHookMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedParameterCertificates
open CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallablePreparedMethodRuntimeMeaning CallablePreparedMethodCatalogEntries
open CallablePreparedMethodCatalogHookMeaning CallablePreparedMethodOriginMeaning CallablePreparedMethodSourceHookMeaning

abbrev actual_hook := @CallablePreparedMethodSourceHookMeaning.ProfileFor.preserves_hook_of_below
abbrev actual_parameters := @CallablePreparedMethodSourceHookMeaning.entry_of_parameters
abbrev catalog_effects := @CallablePreparedMethodCatalogEntries.catalog_entry_of_effects
abbrev source_effects := @CallablePreparedMethodCatalogEntries.source_entry_of_effects

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
theorem closed_builtin_hook (budget child : Nat) (strict : child < budget)
    {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
    (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store installed.canonical)
    (sameFrame : initial.authority.frameLocation = installed.frameLocation)
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world named.inputs arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate [] before sourceBody.source.inputs arguments environment bound)
    (trace : RecursiveNamedCallBounds.BodyTrace program child (methodFunction compiled sourceBody dictionary)
      profile.context environment bound outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (compiled.output.rename installed.embedding.lift) value finalStore ∧
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
  exact CallablePreparedMethodSourceHookMeaning.ProfileFor.preserves_hook_of_below
    compiled (of_builtin compiled profile) functions escaped
    (fun valid extended => valid.extend extended) (fun valid => valid) budget child strict
    installed initial sameFrame represented heaps
    (fun smaller _ => Tests.SourceCoreCallablePreparedMethodOriginMeaning.closed_builtin_source
      compiled profile functions extension faithful observations functionTypes escaped uninitialized missing smaller)
    allocated trace

include profile extension faithful observations functionTypes escaped uninitialized missing in
/-- The parent source derivation supplies the original child and strict bound.
The resulting native hook is ungraded; no native grade is inferred from it. -/
theorem original_method_body (size : Nat)
    {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
    (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store installed.canonical)
    (sameFrame : initial.authority.frameLocation = installed.frameLocation)
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world named.inputs arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : RecursiveNamedCallBounds.BodyOutcome program size sourceBody dictionary before arguments outcome after) :
    ∃ child environment bound,
      child < size ∧
      Dynamic.BindersAllocate [] before sourceBody.source.inputs arguments environment bound ∧
      RecursiveNamedCallBounds.BodyTrace program child (methodFunction compiled sourceBody dictionary)
        profile.context environment bound outcome after ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (compiled.output.rename installed.embedding.lift) value finalStore ∧
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
  have arity : (methodFunction compiled sourceBody dictionary).parameters.length = arguments.length := by
    change sourceBody.source.inputs.length = arguments.length
    rw [profile.parameters, List.length_map]
    exact represented.length.1
  obtain ⟨child, environment, bound, allocated, trace, strict⟩ :=
    RecursiveNamedCallBounds.body_trace_of_fields profile.sourceFrame.source profile.sourceFrame.context
      profile.sourceFrame.parameters profile.sourceFrame.result profile.sourceFrame.roots profile.extended arity executed
  refine ⟨child, environment, bound, strict, allocated, trace, ?_⟩
  exact closed_builtin_hook compiled profile functions extension faithful observations functionTypes escaped
    uninitialized missing size child strict installed initial sameFrame represented heaps allocated trace

section ActualParameters
variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {arguments : List Dynamic.Value} {payloads : List Value} {actualContext : Core.Context}
  {canonical actual : Environment} {ξ : Renaming}
  {location : Location} {next : NativeFrame}
  (reached : TypedMixedNamedParameters.Entry prepared.ancestry.layout.frame prepared.base.globals.length location next values functions registry
    (methodFunction compiled sourceBody dictionary) profile.context named.inputs arguments before
    (store.set location (encode prepared.ancestry.layout.frame next)) mapping world administrative actualContext
    actual ξ compiled.parameterCode compiled.body)
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store canonical)
  (sameFrame : initial.authority.frameLocation = location)
  {added : Environment} (length : added.length = named.inputs.length)
  (spine : reached.canonical = added ++ DataPatternValues.packValues payloads :: canonical)
  {originId : Word} {metadata : MetadataState}
  (owned : prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some originId)
  (history : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table next (.named originId) (some metadata))

/-- The actual parameter entry is embedded without a native body completion. -/
theorem same_parameter_state :
    (entry_of_parameters compiled (of_builtin compiled profile) functions escaped (fun valid extended => valid.extend extended) (fun valid => valid) reached initial sameFrame length spine owned history).environment = reached.environment ∧
    (entry_of_parameters compiled (of_builtin compiled profile) functions escaped (fun valid extended => valid.extend extended) (fun valid => valid) reached initial sameFrame length spine owned history).heap = reached.heap ∧
    (entry_of_parameters compiled (of_builtin compiled profile) functions escaped (fun valid extended => valid.extend extended) (fun valid => valid) reached initial sameFrame length spine owned history).store = reached.store ∧
    (entry_of_parameters compiled (of_builtin compiled profile) functions escaped (fun valid extended => valid.extend extended) (fun valid => valid) reached initial sameFrame length spine owned history).canonical = reached.canonical := ⟨rfl, rfl, rfl, rfl⟩

include length spine in
theorem global_suffix : reached.canonical.drop (named.inputs.length + 1) = canonical := by
  rw [spine, ← length]
  simp

include length spine in
theorem empty_parameters (empty : named.inputs = []) :
    reached.canonical = DataPatternValues.packValues payloads :: canonical := by
  have noAdded : added = [] := by
    cases added with
    | nil => rfl
    | cons head tail => simp [empty] at length
  simpa [noAdded] using spine

include length spine in
theorem ordered_globals (first second : Value) (unused : Environment)
    (original : canonical = first :: second :: unused) :
    reached.canonical[named.inputs.length + 1]? = some first ∧
    reached.canonical[named.inputs.length + 2]? = some second ∧
    reached.canonical.drop (named.inputs.length + 3) = unused := by
  rw [spine, original, ← length]
  simp [Nat.add_assoc]
end ActualParameters

/-- Empty source arguments retain the actual native unit carrier. -/
theorem empty_pack_slot (canonical : Environment) :
    DataPatternValues.packValues [] :: canonical = Value.unit :: canonical := rfl
end Tests.SourceCoreCallablePreparedMethodSourceHookMeaning
