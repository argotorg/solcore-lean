import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterMeaning

/-! A named function enters with a packed argument slot followed by its
administrative environment. The actual common parameter compiler allocates all
source inputs, then reaches the unchanged body with that bundle retained in
its administrative suffix. Allocation receipts and argument representations
supply the prefix; no body execution is a premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedParameters
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning

private theorem insert_at_suffix (added tail : Environment) (value : Value) :
    Environment.insertAt (added ++ tail) added.length value = added ++ value :: tail := by
  induction added with
  | nil => simp [Environment.insertAt]
  | cons head rest ih => simpa [Environment.insertAt] using congrArg (head :: ·) ih

private theorem insert_administrative {catalog : SourceCoreDataCatalog.Catalog} {nativeDefinitions : DataEnvironment}
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {scope : Scope} {environment : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    {value : Value} {type : Ty} (typed : RuntimeValueHasType world value type nativeDefinitions) :
    DataHeap.EnvRepresents catalog mapping world (type :: administrative) scope environment
      (Environment.insertAt canonical scope.length value) nativeDefinitions := by
  induction related with
  | nil values => exact .nil (by simpa [Environment.insertAt] using RuntimeEnvironmentHasTypes.cons typed values)
  | cons reference _ ih => exact .cons reference ih
  | internal reference absent _ ih => exact .internal reference absent ih

theorem scope_eq (bindings : List Binding) (scope : Scope) :
    bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope =
      bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope := by
  induction bindings generalizing scope with
  | nil => rfl
  | cons binding rest ih => simp [ih, List.append_assoc]

theorem inputKinds {source : TypedSource} {bindings : List Binding}
    (inputs : source.inputs = bindings.map Prod.fst) :
    ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = true := by
  intro binding member
  rw [inputs]
  exact List.any_eq_true.mpr ⟨binding.1, List.mem_map.mpr ⟨binding, member, rfl⟩, by simp⟩

/-- The retained bundle is typed directly from represented arguments, even
when a payload is a closure that captures mutable cells. -/
theorem Arguments.pack_typed {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions} {mapping : LocationMap} {world : StoreTyping}
    {bindings : List Binding} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values) :
    RuntimeValueHasType world (DataPatternValues.packValues values)
      (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd)) nativeDefinitions := by
  induction represented with
  | nil => exact .unit
  | @cons binder payload source value bindings sources values head rest ih =>
    cases rest with
    | nil => exact model.runtime_hasType head
    | cons => exact .pair (model.runtime_hasType head) ih

/-- Successful actual named-input compilation reaches a body whose lexical
relation includes the surviving packed-argument administrative slot. The
agreement wraps and inverts every finite body execution. -/
theorem named_prefix {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} {bindings : List Binding} {output : Ty} {body code : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      source [] bindings output SourceCoreFunctions.argumentProjection body = .ok code)
    (inputs : source.inputs = bindings.map Prod.fst)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    (definitions : layouts.definitions = nativeDefinitions)
    (registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrative : Core.Context} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative [] [] canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues values :: canonical) actual)
    (reference : canonical[globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate [] heap (bindings.map Prod.fst) sources finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative)
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      ContinuationAgreement actual store (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  have tree := CallableIndexedParameterCertificates.of_accepted onError accepted
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) canonical (DataPatternValues.packValues values :: canonical) := by
    intro index value found
    exact found
  have length : (bindings.map Prod.snd).length = values.length := by simpa using represented.length.2
  obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, allocated, finalEnvironments, finalHeaps, maps, worlds,
    frame, _, finalActualLayout, spine, agreement⟩ :=
    CallableIndexedParameterMeaning.Tree.prefix tree definitions registered represented environments heaps sourceLayout actualLayout
      (allTypes := bindings.map Prod.snd) (named := true) rfl (by simp) length
      (fun {_ _} found => by simpa using found) (inputKinds inputs) (by simpa using reference) read unmapped
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have typed := (Arguments.pack_typed represented).weaken worlds
  have finalEnvironmentWithBundle := insert_administrative finalEnvironments typed
  have scopeLength : (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) []).length = bindings.length := by
    simp
  have exactEnvironment : Environment.insertAt finalCanonical bindings.length (DataPatternValues.packValues values) = finalLogical := by
    rw [canonicalEq, ← prefixLength, insert_at_suffix, logicalEq]
  rw [scopeLength, exactEnvironment, scope_eq] at finalEnvironmentWithBundle
  exact ⟨finalEnvironment, finalHeap, finalLogical, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, allocated, by simpa using finalEnvironmentWithBundle, finalHeaps, maps, worlds,
    frame, finalActualLayout, agreement⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedParameters
