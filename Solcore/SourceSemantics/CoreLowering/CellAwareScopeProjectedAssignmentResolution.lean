import Solcore.SourceSemantics.CoreLowering.CellAwareScopeProjectedAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStagedProjectedAssignmentAdmission
import Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedFaults

/-! The actual staged key row and RHS produce the physical write and its
reached admission. Structural faults retain their actual diagnostic phase. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeProjectedAssignmentHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CompatibleRenamedPlace DataPatternValues DataPlaceExecution
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareScopeExpressionBounds
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

section Rhs
variable {registry : SourceCoreRawMetadata.Registry} {named : SourceCoreGeneralFunctions.Function}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {before targetHeap : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping}
  {faults : RecursiveStageMeaning.FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {canonical : Environment}
  {certificate : Certificate} {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
  {leaf : TypeSystem.Ty} {target : Dynamic.ResolvedPlace}
  (resolution : CompatibleCellPlaceResolution.Execution compiled.compatible.checked registry functions (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) (GeneralizedLocalInstanceValues.model compiled.indexed) prepared
    (CompatibleRenamedPlace.renamedCodes codes ξ) sourceTypes place leaf target actual store mapping world before targetHeap)


/-- Only an actual successful staged RHS is erased to the ordinary suffix
receipt. Its current root is read from the actual represented RHS heap. -/
theorem RhsResult.to_ordinary_value {size : Nat} {right : Dynamic.Value} {after : Dynamic.Heap}
    {native : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (result : RhsResult (program := program) (context := context) (stages := stages)
      (invocation := invocation) (faults := faults) (id := id) (node := node) (lowered := lowered)
      (environment := environment) resolution size (.value right) after native finalStore finalMap finalWorld) :
    CompatibleCellPlaceRhs.Result (program := program) (context := context)
      (evidence := invocation.evidence) (source := invocation.source)
      (faults := fun reason token => faults (.semantic reason) token)
      resolution id node (renamed lowered ξ) environment (.value right) after native finalStore finalMap finalWorld := by
  refine ⟨.value result.trace.sound.value_plain, result.evaluated, ?_, result.heaps,
    result.maps, result.worlds, result.frame, result.metadata, result.effect, ?_⟩
  · cases result.represented with
    | value related => exact .value related
  · exact CompatibleCellPlaceRhs.latest_of_heap resolution GeneralizedLocalDescriptorHeap.ordinary_cells
      result.heaps result.maps result.worlds result.metadata
end Rhs

section Resolution
variable {registry : SourceCoreRawMetadata.Registry} {named : SourceCoreGeneralFunctions.Function}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : Certificate} {faults : RecursiveStageMeaning.FaultRep} {scope : Scope}
  {site : SourceCoreElaboration.ErrorSite} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {rhsType : Core.Ty} {administrative actualContext : Core.Context} {ξ : Renaming}
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before getter : Dynamic.Heap} {store : Store} {index : Nat}
  {target : Dynamic.ResolvedPlace} {sources : List Dynamic.Value}

/-- The independent ordered key trace determines the getter state before any
RHS execution. The original key value types and deep heap typing are retained. -/
theorem preserves_keys (budget : Nat)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := compiled.indexed.layouts.definitions) (.initial compiled.compatible.checked) invocation.source
      certificate scope site place prepared codes sourceTypes leaf administrative rhsType)
    (environments : DataHeap.EnvRepresents (definitions := compiled.indexed.layouts.definitions) (storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location)
    (unique : NodeOccurrencesUnique invocation.source)
    {originalTypes : List TypeSystem.Ty}
    (originalKeyTyped : ExpressionsHaveTypes invocation.source context (DataPlaceKeyOrder.sourceKeys place.projections) originalTypes)
    (meaning : PreservesBelow bridge context (payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (writable : WritableLocal context place.root prepared.route.rootSourceType)
    {keySize : Nat}
    (keyTrace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys place.projections) (.values sources) getter)
    (keyBound : keySize ≤ budget)
    {location : Dynamic.Location} {initialCell : Dynamic.Cell} {resolved : List Dynamic.EvaluatedProjection}
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (ordered : Staging.Recursive.ProjectedTarget.Values place.projections sources resolved) :
    ∃ execution : CompatibleCellPlaceTargetKeys.Execution compiled.compatible.checked registry functions (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) (GeneralizedLocalInstanceValues.model compiled.indexed) prepared place
      (renamedCodes codes ξ) sourceTypes location resolved actual before getter store mapping world (ξ index),
      Dynamic.ValuesHaveTypes context getter sources sourceTypes ∧ Dynamic.HeapWellTyped context getter ∧
      ∃ reached : callerProtocol.State ⟨scope, execution.keyMap, execution.keyWorld, getter, execution.keyStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached := by
  obtain ⟨target, selected, reference⟩ := environments.lookup_visible lookup slot
  obtain ⟨native, keyStore, keyMap, keyWorld, evaluated, represented, keyHeaps,
    maps, worlds, frame, metadata, effect, typed, reached, related, post⟩ :=
    CellAwareScopeTypedExpressionSequence.preserves_values bridge budget
      layout.children unique originalKeyTyped meaning environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
      (.cons (.cellRef reference.typed) actualTyped) initial admitted authority physical owner ownerFrame
      (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keyTrace) keyBound
  obtain ⟨scheme, staticLookup, _wellFormed, monomorphic, bodyEq⟩ := writable.scheme
  obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
  cases lookup.functional staticLookupRuntime
  cases initialRead.functional staticRead
  obtain ⟨cell, read, sameType, _⟩ := metadata _ _ initialRead
  refine ⟨⟨target, sources, native, keyStore, keyMap, keyWorld, cell, read,
    (locals.mono metadata).descriptor_empty_of_monomorphic post.at_values.heap staticLookup lookup read monomorphic,
    sameType.trans (staticCellType.trans bodyEq), reference.extend maps worlds, agrees selected,
    ordered.to_data, ?_, ?_, keyHeaps, maps, worlds, frame, metadata, effect⟩,
    typed, post.at_values.heap, reached, related, post.at_values⟩
  · simpa only [DataPlaceChildExpressions.rename_prefix, packed_renamed_expression, List.length_cons, List.length_nil,
      List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated
  · simpa only [renamedCodes_types, CallableIndexedAmbient.ambientDefinitions] using represented

theorem preserves_resolution (budget : Nat)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := compiled.indexed.layouts.definitions) (.initial compiled.compatible.checked) invocation.source
      certificate scope site place prepared codes sourceTypes leaf administrative rhsType)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
    (environments : DataHeap.EnvRepresents (definitions := compiled.indexed.layouts.definitions) (storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location)
    (unique : NodeOccurrencesUnique invocation.source)
    {originalTypes : List TypeSystem.Ty}
    (originalKeyTyped : ExpressionsHaveTypes invocation.source context (DataPlaceKeyOrder.sourceKeys place.projections) originalTypes)
    (meaning : PreservesBelow bridge context (payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (writable : WritableLocal context place.root prepared.route.rootSourceType)
    {keySize : Nat}
    (keyTrace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys place.projections) (.values sources) getter)
    (keyBound : keySize ≤ budget)
    (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before getter place sources target) :
    ∃ resolution : CompatibleCellPlaceResolution.Execution compiled.compatible.checked registry functions (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)) (GeneralizedLocalInstanceValues.model compiled.indexed) prepared
      (renamedCodes codes ξ) sourceTypes place leaf target actual store mapping world before getter,
      resolution.sources = sources ∧ Dynamic.ValuesHaveTypes context getter sources sourceTypes ∧
      Dynamic.HeapWellTyped context getter ∧
      actual[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target) ∧
      ∃ reached : callerProtocol.State ⟨scope, resolution.mapping, resolution.world, getter, resolution.store, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached := by
  obtain ⟨resolution, sameSources, keyValues, keyHeap, coreLookup, reached, related⟩ :=
    CellAwareStagedProjectedResolution.preserves GeneralizedLocalDescriptorHeap.ordinary_cells layout.path layout.views layout.keyTypes layout.leafProjected
      layout.virtual extension layout.nonempty
      (CompatibleRenamedPlace.getter_typed layout (CompatibleRenamedPlace.virtual_closed layout ordinary)
        (CompatibleRenamedPlace.environment_respects environments.runtime_hasTypes actualTyped agrees))
      callerProtocol transport faithful observations environments locals agrees actualTyped initial
      (fun target _ hiddenTyped => by
        obtain ⟨native, keyStore, keyMap, keyWorld, evaluated, represented, keyHeaps,
          maps, worlds, frame, metadata, effect, typed, reached, related, post⟩ :=
          CellAwareScopeTypedExpressionSequence.preserves_values bridge budget
            layout.children unique originalKeyTyped meaning environments heaps locals
            (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
            hiddenTyped initial admitted authority physical owner ownerFrame
            (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keyTrace) keyBound
        exact ⟨native, keyStore, keyMap, keyWorld, evaluated, represented, keyHeaps, maps, worlds,
          frame, metadata, typed, post.at_values.heap, effect, reached, related⟩)
      slot writable snapshot
  exact ⟨resolution, sameSources, keyValues, keyHeap, coreLookup, reached, related, keyHeap,
    StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows resolution.frame⟩
end Resolution

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeProjectedAssignmentHeads
