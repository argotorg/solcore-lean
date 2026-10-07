import Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedArmAllocation
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmPrefix

/-! The real successful marked arm prefix preserves typing of every actual
slot, including the retained bundle, scrutinee and initializer temporaries.
Typed child expressions can therefore enter without a supplied final typing. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedArmPrefix
open Core Frontend SourceInference GeneralHeap DataEquality CoreProof ReadOnly DataPatternValues
open CompatibleMatchArmPrefix DataMatchCoreAllocation
open CompatibleMatchArmCertificates (Scope)
universe u v

private theorem liftMany_twoInsertions (count cutoff : Nat) :
    liftMany count (Renaming.comp (Renaming.insertion cutoff) (Renaming.insertion cutoff)) =
      Renaming.comp (Renaming.insertion (cutoff + count)) (Renaming.insertion (cutoff + count)) := by
  induction count generalizing cutoff with
  | zero => rfl
  | succ count ih =>
    simp only [liftMany, Renaming.lift_comp, Renaming.lift_insertion, ih]
    congr 2 <;> omega

/-- This is the successful branch emitted by compatible match lowering,
including its two hidden lexical slots. The result relates the arm's ordinary lexical scope
to its actual Core environment and transforms the body syntax with the same
embedding. Both finite evaluation directions retain the exact final store. -/
theorem Stateful.bindArm_prefix_sized {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {context : SourceCoreCompatibleDataMatches.Context}
    {catalog : SourceCoreDataCatalog.Catalog}
    {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    {bindings : List (TypedBinder × Ty)} {sources : List Dynamic.Value} {values : List Value}
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {scope : Scope} {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world bindings sources values)
    {scrutinee : Value} {outputType : Ty} {body code : Expr}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts layout model)
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = nativeDefinitions) (registered : layout.Registered nativeDefinitions)
    (allocator : context.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError)))
    (accepted : SourceCoreCompatibleDataMatches.bindArmWithAllocator context source scope bindings outputType
      (body.weakenAt bindings.length) = .ok code)
    {named : Bool} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (packValues values :: scrutinee :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext nativeDefinitions)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary contextLocation native) :
    ∃ finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources
        finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual
        (CompatibleMatchTypedArmAllocation.prefixContext bindings actualContext) nativeDefinitions ∧
      finalCanonical[(bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope).length +
        (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope) finalCanonical ∧
      ContinuationSize false actual store
        (code.rename ξ)
        finalActual finalStore (body.rename finalEmbedding) ∧
      ∃ final : protocol.State
          ⟨bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope,
            finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        protocol.Relates initial final ∧ Nonempty (ProtectedStateTransition.ReturnTo protocol scope canonical
          (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope) finalCanonical) := by
  let κ := Renaming.comp (Renaming.insertion 0) (Renaming.insertion 0)
  have sourceLayout : EnvironmentsAgree κ canonical (packValues values :: scrutinee :: canonical) := by
    intro index value found
    exact found
  have length : (bindings.map Prod.snd).length = values.length := by
    simpa using represented.length.2
  obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap,
    finalWorld, finalEmbedding, allocated, finalEnv, finalHeapRep, maps, worlds, frame,
    finalSourceLayout, finalActualLayout, spine, finalTyped, agreement, finalState, related, restoration⟩ :=
    CompatibleMatchTypedArmAllocation.Stateful.prefix_sized
      (CompatibleMatchArmCertificates.of_accepted onError allocator accepted) protocol producer stateBindings definitions registered represented
      environments heaps sourceLayout actualLayout actualTyped (start := 0) rfl rfl length
      (fun {_ _} found => by simpa using found) kinds reference read unmapped initial readyAt
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have finalReference : finalCanonical[(bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope).length +
      (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation) := by
    rw [canonicalEq]
    have scopeLength : (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope).length =
        bindings.length + scope.length := by simp
    rw [scopeLength]
    have index : bindings.length + scope.length + (if named then 0 else 1) + globals =
        added.length + (scope.length + (if named then 0 else 1) + globals) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using reference
  obtain ⟨stillUnmapped, stillRead⟩ := frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1
  refine ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap,
    finalWorld, Renaming.comp finalEmbedding (liftMany bindings.length κ), allocated, finalEnv,
    finalHeapRep, maps, worlds, frame, ?_, finalTyped, finalReference, stillRead.trans read, stillUnmapped, ?_, ?_, finalState, related, restoration⟩
  · intro index value found
    exact finalActualLayout (finalSourceLayout found)
  · rw [canonicalEq]
    exact CanonicalPrefix.fold scope canonical bindings (fun binding => (binding.1.id, binding.2)) prefixLength
  · have same : ((body.weakenAt bindings.length).weakenAt bindings.length).rename finalEmbedding =
        body.rename (Renaming.comp finalEmbedding (liftMany bindings.length κ)) := by
      simp only [κ, liftMany_twoInsertions, Nat.zero_add]
      rw [← Expr.rename_insertion, ← Expr.rename_insertion, Expr.rename_comp, Expr.rename_comp]
      rfl
    rw [same] at agreement
    exact agreement



/-- Compatibility erasure of the same actual arm prefix. -/
theorem bindArm_prefix_sized {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {context : SourceCoreCompatibleDataMatches.Context}
    {catalog : SourceCoreDataCatalog.Catalog}
    {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    {bindings : List (TypedBinder × Ty)} {sources : List Dynamic.Value} {values : List Value}
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {scope : Scope} {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world bindings sources values)
    {scrutinee : Value} {outputType : Ty} {body code : Expr}
    (definitions : layouts.definitions = nativeDefinitions) (registered : layout.Registered nativeDefinitions)
    (allocator : context.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError)))
    (accepted : SourceCoreCompatibleDataMatches.bindArmWithAllocator context source scope bindings outputType
      (body.weakenAt bindings.length) = .ok code)
    {named : Bool} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (packValues values :: scrutinee :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext nativeDefinitions) :
    ∃ finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources
        finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual
        (CompatibleMatchTypedArmAllocation.prefixContext bindings actualContext) nativeDefinitions ∧
      finalCanonical[(bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope).length +
        (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope) finalCanonical ∧
      ContinuationSize false actual store
        (code.rename ξ)
        finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, allocated, finalEnv, finalHeaps, maps, worlds, preserved, finalLayout, finalTyped,
    finalReference, finalRead, finalUnmapped, spine, agreement, _final, _related, _return⟩ :=
    Stateful.bindArm_prefix_sized represented ProtectedStateTransition.OrdinaryAllocation.unitProtocol
      (ProtectedStateTransition.MarkedAllocation.unitProducer layouts layout model)
      ProtectedStateTransition.MatchPrefix.unitBindings definitions registered allocator accepted kinds reference read unmapped
      environments heaps actualLayout actualTyped () (fun _ _ => True.intro)
  exact ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, allocated, finalEnv, finalHeaps, maps, worlds, preserved, finalLayout, finalTyped,
    finalReference, finalRead, finalUnmapped, spine, agreement⟩

theorem bindArm_prefix_typed {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {context : SourceCoreCompatibleDataMatches.Context}
    {catalog : SourceCoreDataCatalog.Catalog}
    {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    {bindings : List (TypedBinder × Ty)} {sources : List Dynamic.Value} {values : List Value}
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {scope : Scope} {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world bindings sources values)
    {scrutinee : Value} {outputType : Ty} {body code : Expr}
    (definitions : layouts.definitions = nativeDefinitions) (registered : layout.Registered nativeDefinitions)
    (allocator : context.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError)))
    (accepted : SourceCoreCompatibleDataMatches.bindArmWithAllocator context source scope bindings outputType
      (body.weakenAt bindings.length) = .ok code)
    {named : Bool} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (packValues values :: scrutinee :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext nativeDefinitions) :
    ∃ finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources
        finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual
        (CompatibleMatchTypedArmAllocation.prefixContext bindings actualContext) nativeDefinitions ∧
      finalCanonical[(bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope).length +
        (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native) ∧
      contextLocation ∉ finalMap ∧
      ContinuationAgreement actual store
        (code.rename ξ)
        finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, allocated, finalEnv, finalHeaps, maps, worlds, frame, layout, typed, finalReference,
    finalRead, finalUnmapped, _, agreement⟩ :=
    bindArm_prefix_sized represented definitions registered allocator accepted kinds reference read unmapped
      environments heaps actualLayout actualTyped
  exact ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, allocated, finalEnv, finalHeaps, maps, worlds, frame, layout, typed, finalReference,
    finalRead, finalUnmapped, agreement.agreement⟩


end Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedArmPrefix
