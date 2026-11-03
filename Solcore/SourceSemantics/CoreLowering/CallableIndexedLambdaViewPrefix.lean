import Solcore.SourceSemantics.CoreLowering.FunctionCallBody
import Solcore.SourceSemantics.CoreLowering.LambdaMetadataViews
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterTyped
import Solcore.SourceSemantics.CoreLowering.CaptureCopiesMarked

/-! A closure's entry copies its captured cells and then installs its
parameters, reaching the actual monomorphic call context. Its
finite continuation agreement comes from the production allocation receipts;
the compiler view is retained independently of the canonical closure source.
Body correspondence remains a separate concrete static certificate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewPrefix
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning

/-- The allocation authenticator observes the same owner, binder inputs,
forms, and statement metadata in every genuine metadata view. -/
theorem sourceView_eq {source view : TypedSource}
    (metadata : LambdaMetadataViews.MetadataView source view) :
    SourceCoreAllocationCodebook.sourceView source = SourceCoreAllocationCodebook.sourceView view := by
  have go {before after : List Node} (related : DataPatternValues.ListRel LambdaMetadataViews.NodeView before after) :
      before.map (fun node => match node with
        | .expression expression => SourceCoreAllocationCodebook.MetadataNode.expression expression.id expression.form
        | .statement statement => .statement statement) =
      after.map (fun node => match node with
        | .expression expression => SourceCoreAllocationCodebook.MetadataNode.expression expression.id expression.form
        | .statement statement => .statement statement) := by
    induction related with
    | nil => rfl
    | cons head _ ih =>
      cases head with
      | expression sameId sameForm => simp only [List.map_cons, sameId, sameForm, ih]
      | statement => exact congrArg (List.cons _) ih
  simp only [SourceCoreAllocationCodebook.sourceView, metadata.owner, metadata.inputs, metadata.roots]
  exact congrArg (fun nodes => SourceCoreAllocationCodebook.MetadataSource.mk view.owner view.inputs view.roots nodes) (go metadata.nodes)

structure Entry (layout : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : SourceCoreCallableIndexedFrames.Frame) (values : SourceCoreCompatibleValues.Context)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (function : Dynamic.Closure) (context : SourceSemantics.Context) (scope : Scope) (bindings : List Binding)
    (arguments : List Dynamic.Value) (before : Dynamic.Heap) (initialStore : Store)
    (initialMap : LocationMap) (initialWorld : StoreTyping) (administrative actualContext : Core.Context)
    (actual : Environment) (ξ : Renaming) (parameterCode body : Expr) where private mk ::
  copies : Dynamic.Environment
  copiedHeap : Dynamic.Heap
  copiedContext : Core.Context
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  actualBody : Environment
  store : Store
  mapping : LocationMap
  world : StoreTyping
  embedding : Renaming
  copy : Dynamic.EnvironmentCopies function.source function.captured before copies copiedHeap
  allocation : Dynamic.BindersAllocate copies copiedHeap function.parameters arguments environment heap
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) environment canonical ambient.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before heap
  lookups : EnvironmentsAgree embedding canonical actualBody
  actualTyped : RuntimeEnvironmentHasTypes world actualBody
    (CallableIndexedParameterTyped.prefixContext bindings copiedContext) ambient.definitions
  reference : canonical[(bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length + 1 + globals]? =
    some (.cellRef layout.type contextLocation)
  read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native)
  unmapped : contextLocation ∉ mapping
  agreement : ContinuationAgreement actual initialStore (parameterCode.rename ξ) actualBody store (body.rename embedding)

private theorem liftMany_insertion (count cutoff : Nat) :
    DataMatchCoreAllocation.liftMany count (Renaming.insertion cutoff) = Renaming.insertion (cutoff + count) := by
  induction count generalizing cutoff with
  | zero => rfl
  | succ count ih =>
    simp only [DataMatchCoreAllocation.liftMany, Renaming.lift_insertion, ih]
    congr 1
    omega

namespace Stateful

/-- The entry copies the closure's captured cells through the marked
allocator, then the actual prefix receipts construct parameter allocation, the
typed body environment and the surviving context-reference slot. Its read and
unmapped status follow from allocation preservation. The protected state
crosses the copies administratively and is rebound to the copied slots. No
final body facts are assumed. -/
theorem entry_of_accepted_with_spine_of_copies
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {Records : Type} (protocol : ProtectedStateTransition.Protocol Records)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts layout
      (CompatibleAmbientHeap.payloadModel values.checked registry functions))
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (rebinds : ProtectedStateTransition.Rebinds protocol)
    {function : Dynamic.Closure} {view : TypedSource} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {scope : Scope} {bindings : List Binding} {output : Ty} {body allocatedCode parameterCode : Expr}
    (inputIds : function.source.inputs.map TypedBinder.id = view.inputs.map TypedBinder.id)
    (copies : SourceSemantics.CaptureBinders.copiedBinder? function.source =
      SourceSemantics.CaptureBinders.copiedBinder? view)
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      view scope bindings output SourceCoreFunctions.argumentProjection (body.weakenAt bindings.length) = .ok allocatedCode)
    (copied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError)))
      view scope (· + 1) allocatedCode = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (kinds : ∀ binding ∈ bindings, function.source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope function.captured canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (types : Renaming.Respects ξ (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) ::
      (SourceCoreLocalCell.coreContext scope ++ administrative)) actualContext)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary contextLocation native) :
    ∃ entry : Entry layout globals contextLocation native values functions registry function context scope bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body,
      ∃ added copied : Environment, added.length = bindings.length ∧ entry.canonical = added ++ copied ∧
        (∀ slot, scope.length ≤ slot → copied[slot]? = canonical[slot]?) ∧
        ProtectedStateTransition.Transition protocol initial
          ⟨bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
            entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := by
  obtain ⟨copiesEnvironment, copiedHeap, copiedCanonical, copiedActual, copiedContext, copiedStore, copiedMap,
      copiedWorld, copiedEmbedding, copy, copiedEnvironments, slots, copiedHeaps, copiedMaps, copiedWorlds,
      copiedFrame, copiedRead, copiedLookups, _copiedTypes, copiedTyped, copyAgreement⟩ :=
    CaptureCopies.marked_copies_prefix (pre := [DataPatternValues.packValues nativeArguments])
      (preContext := [SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd)])
      copied definitions registered environments heaps actualLayout rfl types actualTyped reference read
  have sourceCopy := copy.of_copiedBinder copies.symm
  obtain ⟨copiedUnmapped, _⟩ := copiedFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1
  obtain ⟨extendedState, extendedRelated⟩ := ProtectedStateTransition.AdministrativeTransport.transition protocol
    transport initial copiedMaps copiedWorlds copiedFrame sourceCopy.metadata_extends
  obtain ⟨reboundState, reboundRelated⟩ := rebinds extendedState copiedCanonical slots
  have copiedReference : copiedCanonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation) := by
    rw [slots _ (by omega)]
    exact reference
  have tree := CallableIndexedParameterCertificates.of_accepted onError accepted
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) copiedCanonical
      (DataPatternValues.packValues nativeArguments :: copiedCanonical) := by
    intro index value found; exact found
  have length : (bindings.map Prod.snd).length = nativeArguments.length := by simpa using represented.length.2
  obtain ⟨environment, heap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding,
      allocated, finalEnvironments, finalHeaps, maps, worlds, preservation, sourceLayout, lookups, spine, finalTyped, agreement, transition⟩ :=
    CallableIndexedParameterTyped.Stateful.prefix_typed tree protocol producer definitions registered
      (represented.extend copiedMaps copiedWorlds) copiedEnvironments copiedHeaps
      sourceLayout copiedLookups copiedTyped (allTypes := bindings.map Prod.snd) (named := false) rfl (by simp) length
      (fun {_ _} found => by simpa using found)
      (by
        intro binding member
        have same := congrArg (fun ids : List Resolved.LocalId =>
          ids.any (fun id => decide (id = binding.1.id))) inputIds
        simp only [List.any_map] at same
        exact same.symm.trans (kinds binding member))
      (by simpa using copiedReference) copiedRead copiedUnmapped reboundState readyAt
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have finalReference : finalCanonical[(bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length + 1 + globals]? =
      some (.cellRef layout.type contextLocation) := by
    rw [canonicalEq]
    simp only [List.length_append, List.length_map, List.length_reverse]
    have index : bindings.length + scope.length + 1 + globals = added.length + (scope.length + 1 + globals) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using copiedReference
  have finalLookups : EnvironmentsAgree (Renaming.comp embedding (Renaming.insertion bindings.length))
      finalCanonical finalActual := by
    intro index value found
    apply lookups
    have transported := sourceLayout found
    simpa only [liftMany_insertion, Nat.zero_add] using transported
  have bodyEq : (body.weakenAt bindings.length).rename embedding =
      body.rename (Renaming.comp embedding (Renaming.insertion bindings.length)) := by
    rw [← Expr.rename_insertion, Expr.rename_comp]
  rw [bodyEq] at agreement
  obtain ⟨finalUnmapped, unchanged⟩ := preservation contextLocation copiedUnmapped (List.getElem?_eq_some_iff.mp copiedRead).1
  rw [← parameters] at allocated
  have mono := FunctionCallBody.mono_binders extended
  have copiedLocals := Dynamic.EnvironmentCopies.agrees initialLocals sourceCopy
  refine ⟨⟨copiesEnvironment, copiedHeap, copiedContext, environment, heap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, Renaming.comp embedding (Renaming.insertion bindings.length),
    sourceCopy, allocated, by simpa [CallableIndexedParameters.scope_eq] using finalEnvironments, finalHeaps,
    GenericLexicalContext.binders_agree mono.1 mono.2 copiedLocals allocated,
    copiedMaps.trans maps, copiedWorlds.trans worlds, copiedFrame.trans preservation,
    sourceCopy.metadata_extends.trans (GenericLexicalContext.binders_metadata allocated), finalLookups, finalTyped,
    finalReference, unchanged.trans copiedRead, finalUnmapped, copyAgreement.continuation.trans agreement⟩,
    added, copiedCanonical, prefixLength, canonicalEq, slots, ?_⟩
  have composed : ProtectedStateTransition.Transition protocol initial
      ⟨bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope,
        finalMap, finalWorld, heap, finalStore, finalCanonical⟩ := by
    obtain ⟨reached, related⟩ := transition
    exact ⟨reached, protocol.trans (protocol.trans extendedRelated reboundRelated) related⟩
  simpa only [CallableIndexedParameters.scope_eq] using composed

/-- Compatibility with the original full metadata-view receipt. -/
theorem entry_of_accepted_with_spine
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {Records : Type} (protocol : ProtectedStateTransition.Protocol Records)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts layout
      (CompatibleAmbientHeap.payloadModel values.checked registry functions))
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (rebinds : ProtectedStateTransition.Rebinds protocol)
    {function : Dynamic.Closure} {view : TypedSource} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {scope : Scope} {bindings : List Binding} {output : Ty} {body allocatedCode parameterCode : Expr}
    (viewOfSource : LambdaMetadataViews.MetadataView function.source view)
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      view scope bindings output SourceCoreFunctions.argumentProjection (body.weakenAt bindings.length) = .ok allocatedCode)
    (copied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError)))
      view scope (· + 1) allocatedCode = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (kinds : ∀ binding ∈ bindings, function.source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope function.captured canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (types : Renaming.Respects ξ (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) ::
      (SourceCoreLocalCell.coreContext scope ++ administrative)) actualContext)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary contextLocation native) :
    ∃ entry : Entry layout globals contextLocation native values functions registry function context scope bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body,
      ∃ added copied : Environment, added.length = bindings.length ∧ entry.canonical = added ++ copied ∧
        (∀ slot, scope.length ≤ slot → copied[slot]? = canonical[slot]?) ∧
        ProtectedStateTransition.Transition protocol initial
          ⟨bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
            entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := by
  exact entry_of_accepted_with_spine_of_copies functions onError protocol producer transport rebinds
    (congrArg (List.map TypedBinder.id) viewOfSource.inputs) (LambdaMetadataViews.MetadataView.copiedBinder viewOfSource)
    accepted copied parameters kinds extended definitions registered represented environments heaps initialLocals
    actualLayout types actualTyped reference read unmapped initial readyAt

end Stateful

theorem entry_of_accepted_with_spine
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {function : Dynamic.Closure} {view : TypedSource} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {scope : Scope} {bindings : List Binding} {output : Ty} {body allocatedCode parameterCode : Expr}
    (viewOfSource : LambdaMetadataViews.MetadataView function.source view)
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      view scope bindings output SourceCoreFunctions.argumentProjection (body.weakenAt bindings.length) = .ok allocatedCode)
    (copied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError)))
      view scope (· + 1) allocatedCode = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (kinds : ∀ binding ∈ bindings, function.source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope function.captured canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (types : Renaming.Respects ξ (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) ::
      (SourceCoreLocalCell.coreContext scope ++ administrative)) actualContext)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ entry : Entry layout globals contextLocation native values functions registry function context scope bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body,
      ∃ added copied : Environment, added.length = bindings.length ∧ entry.canonical = added ++ copied ∧
        (∀ slot, scope.length ≤ slot → copied[slot]? = canonical[slot]?) := by
  obtain ⟨entry, added, copied, length, spine, slots, _transition⟩ :=
    Stateful.entry_of_accepted_with_spine functions onError ProtectedStateTransition.OrdinaryAllocation.unitProtocol
      (ProtectedStateTransition.MarkedAllocation.unitProducer layouts layout
        (CompatibleAmbientHeap.payloadModel values.checked registry functions))
      ProtectedStateTransition.OrdinaryAllocation.unitTransport ProtectedStateTransition.OrdinaryAllocation.unitRebinds
      viewOfSource accepted copied parameters kinds extended definitions registered represented environments heaps
      initialLocals actualLayout types actualTyped reference read unmapped () (by intro index state read; trivial)
  exact ⟨entry, added, copied, length, spine, slots⟩

/-- The original receipt forgets only the certified canonical allocation prefix. -/
theorem entry_of_accepted
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {function : Dynamic.Closure} {view : TypedSource} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {scope : Scope} {bindings : List Binding} {output : Ty} {body allocatedCode parameterCode : Expr}
    (viewOfSource : LambdaMetadataViews.MetadataView function.source view)
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      view scope bindings output SourceCoreFunctions.argumentProjection (body.weakenAt bindings.length) = .ok allocatedCode)
    (copied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError)))
      view scope (· + 1) allocatedCode = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (kinds : ∀ binding ∈ bindings, function.source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope function.captured canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (types : Renaming.Respects ξ (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) ::
      (SourceCoreLocalCell.coreContext scope ++ administrative)) actualContext)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    Nonempty (Entry layout globals contextLocation native values functions registry function context scope bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body) := by
  obtain ⟨entry, _⟩ := entry_of_accepted_with_spine functions onError viewOfSource accepted copied parameters kinds
    extended definitions registered represented environments heaps initialLocals actualLayout types actualTyped
    reference read unmapped
  exact ⟨entry⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewPrefix
