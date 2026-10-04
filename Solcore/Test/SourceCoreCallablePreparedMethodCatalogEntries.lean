import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogEntries
import Solcore.Test.SourceCoreCallablePreparedMethodSelection

/-! Actual marked prefixes keep the packed-argument slot, complete source heap,
ordered catalog, and physical history. Pure list fixtures below check offsets;
they do not construct catalog authority or source provenance. The runtime
runner reuses the existing four actual operator programs once. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallablePreparedMethodCatalogEntries
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames CallablePreparedMethodRuntimeMeaning CallablePreparedMethodCatalogEntries

abbrev actual_hook := @hook_catalog_entry
abbrev original_hook_spine := @hook_prefix_with_spine
abbrev caller_catalog_restore := @restore_catalog

theorem actual_parameter_prefix
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {bindings : List Binding} {output : Ty} {body parameterCode : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      function.source [] bindings output SourceCoreFunctions.argumentProjection body = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (inputs : function.source.inputs = bindings.map Prod.fst)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    {size : Nat} {result : Value} {afterStore : Store}
    (completed : EvaluationSize size actual store (parameterCode.rename ξ) result afterStore) :
    ∃ entry : Prefix layout globals contextLocation native values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body size result afterStore,
      ∃ added : Environment, added.length = bindings.length ∧
        entry.canonical = added ++ DataPatternValues.packValues nativeArguments :: canonical ∧
        entry.canonical[bindings.length]? = some (DataPatternValues.packValues nativeArguments) ∧
        entry.canonical.drop (bindings.length + 1) = canonical := by
  obtain ⟨entry, added, length, spine⟩ := parameter_prefix_with_spine functions onError accepted parameters inputs extended
    definitions registered represented environments heaps initialLocals actualLayout actualTyped reference read unmapped completed
  refine ⟨entry, added, length, spine, ?_, ?_⟩
  · simp [spine, ← length]
  · simp [spine, ← length]

section Catalog
variable {checked : Checked} {base : Base checked} {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {program : SourceSemantics.Program}
  {headers : RecursiveNamedCatalog.Inventory prepared values ambient.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared) (values := values) (ambient := ambient) (program := program)}
  {capturePrefix callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope}
  {named : SourceCoreGeneralFunctions.Function} {body : Dynamic.BodyInstance} {function : Dynamic.Closure}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
  (entry : SourceEntry named body function headers locations capturePrefix callerPrefix scope mapping world heap store canonical)

include entry in
theorem actual_catalog_globals : ∀ header, header ∈ headers →
    canonical[scope.length + callerPrefix + header.slot]? = some
      (.cellRef (OptionalCell.cellType header.named.signature.functionType) (locations header)) := entry.catalog.globals

include entry in
theorem actual_source_dictionary : function.evidence.Covers body.context ∧
    function.source = body.source ∧ body.source = CallableIndexedNamedGeneration.source named :=
  ⟨entry.sourceFrame.covers, entry.sourceFrame.source, entry.sameSource⟩

include entry in
theorem actual_frame_and_history :
    canonical[scope.length + 1 + base.globals.length]? =
      some (.cellRef prepared.layout.frame.type entry.catalog.authority.frameLocation) ∧
    store.read? entry.catalog.authority.frameLocation = some
      (encode prepared.layout.frame entry.catalog.authority.current) ∧
    Carries prepared.graph.inputs prepared.graph.table entry.catalog.authority.current (.named entry.origin) (some entry.metadata) :=
  ⟨entry.reference, entry.catalog.authority.frame.read, entry.carried⟩

theorem retained_original_source {futureMap : LocationMap} {futureWorld : StoreTyping}
    {after : Dynamic.Heap} {futureStore : Store}
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    (entry.extend maps worlds frame metadata).sourceFrame = entry.sourceFrame ∧
    (entry.extend maps worlds frame metadata).origin = entry.origin ∧
    (entry.extend maps worlds frame metadata).metadata = entry.metadata ∧
    (entry.extend maps worlds frame metadata).catalog.authority.frameLocation = entry.catalog.authority.frameLocation :=
  ⟨rfl, rfl, rfl, rfl⟩
end Catalog

section Boundaries

theorem packed_slot_and_full_suffix (added canonical : Environment) (arguments : List Value) :
    let reached := added ++ DataPatternValues.packValues arguments :: canonical
    reached[added.length]? = some (DataPatternValues.packValues arguments) ∧
      reached.drop (added.length + 1) = canonical := by simp

theorem empty_arity_keeps_pack (added canonical : Environment) (empty : added.length = 0) :
    added ++ DataPatternValues.packValues [] :: canonical = Value.unit :: canonical := by
  cases added with
  | nil => rfl
  | cons head tail => simp at empty

/-- Two actual lookup positions and the independent frame index are preserved
under an arbitrary unused suffix; this fixture asserts no authority. -/
theorem ordered_globals_with_unused_suffix (unused : Environment) (bundle : Value) :
    let initial : Environment := [.bool true, .cellRef .word 3, .cellRef .bool 4, .cellRef .unit 5] ++ unused
    let reached := [Value.cellRef .word 7, .cellRef .bool 8] ++ bundle :: initial
    reached[2]? = some bundle ∧ reached[4]? = some (.cellRef .word 3) ∧
      reached[5]? = some (.cellRef .bool 4) ∧ reached[6]? = some (.cellRef .unit 5) ∧ reached.drop 7 = unused := by simp

theorem empty_parameters_with_unused_suffix (unused : Environment) :
    let initial : Environment := [.bool true, .cellRef .word 3, .cellRef .bool 4, .cellRef .unit 5] ++ unused
    let reached := Value.unit :: initial
    reached[0]? = some .unit ∧ reached[2]? = some (.cellRef .word 3) ∧
      reached[3]? = some (.cellRef .bool 4) ∧ reached[4]? = some (.cellRef .unit 5) ∧ reached.drop 5 = unused := by simp

end Boundaries

def run : IO Unit := Tests.SourceCoreCallablePreparedMethodSelection.run
end Tests.SourceCoreCallablePreparedMethodCatalogEntries
