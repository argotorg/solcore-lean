import Solcore.SourceSemantics.CoreLowering.FunctionCallBody
import Solcore.SourceSemantics.CoreLowering.LambdaMetadataViews
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterTyped

/-! Parameter installation reaches the actual monomorphic call context. Its
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
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  actualBody : Environment
  store : Store
  mapping : LocationMap
  world : StoreTyping
  embedding : Renaming
  allocation : Dynamic.BindersAllocate function.captured before function.parameters arguments environment heap
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
    (CallableIndexedParameterTyped.prefixContext bindings actualContext) ambient.definitions
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

/-- Actual prefix receipts construct parameter allocation, the typed body
environment and the surviving context-reference slot. Its read and unmapped
status follow from allocation preservation. No final body facts are assumed. -/
theorem entry_of_accepted
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {function : Dynamic.Closure} {view : TypedSource} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {scope : Scope} {bindings : List Binding} {output : Ty} {body parameterCode : Expr}
    (viewOfSource : LambdaMetadataViews.MetadataView function.source view)
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      view scope bindings output SourceCoreFunctions.argumentProjection (body.weakenAt bindings.length) = .ok parameterCode)
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
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    Nonempty (Entry layout globals contextLocation native values functions registry function context scope bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body) := by
  have tree := CallableIndexedParameterCertificates.of_accepted onError accepted
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) canonical
      (DataPatternValues.packValues nativeArguments :: canonical) := by
    intro index value found; exact found
  have length : (bindings.map Prod.snd).length = nativeArguments.length := by simpa using represented.length.2
  obtain ⟨environment, heap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding,
      allocated, finalEnvironments, finalHeaps, maps, worlds, preservation, sourceLayout, lookups, spine, finalTyped, agreement⟩ :=
    CallableIndexedParameterTyped.prefix_typed tree definitions registered represented environments heaps
      sourceLayout actualLayout actualTyped (allTypes := bindings.map Prod.snd) (named := false) rfl (by simp) length
      (fun {_ _} found => by simpa using found)
      (by simpa only [← viewOfSource.inputs] using kinds)
      (by simpa using reference) read unmapped
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have finalReference : finalCanonical[(bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length + 1 + globals]? =
      some (.cellRef layout.type contextLocation) := by
    rw [canonicalEq]
    simp only [List.length_append, List.length_map, List.length_reverse]
    have index : bindings.length + scope.length + 1 + globals = added.length + (scope.length + 1 + globals) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using reference
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
  obtain ⟨finalUnmapped, unchanged⟩ := preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1
  rw [← parameters] at allocated
  have mono := FunctionCallBody.mono_binders extended
  exact ⟨⟨environment, heap, finalCanonical, finalActual, finalStore, finalMap, finalWorld, Renaming.comp embedding (Renaming.insertion bindings.length),
    allocated, by simpa [CallableIndexedParameters.scope_eq] using finalEnvironments, finalHeaps,
    GenericLexicalContext.binders_agree mono.1 mono.2 initialLocals allocated,
    maps, worlds, preservation, GenericLexicalContext.binders_metadata allocated, finalLookups, finalTyped,
    finalReference, unchanged.trans read, finalUnmapped, agreement⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewPrefix
