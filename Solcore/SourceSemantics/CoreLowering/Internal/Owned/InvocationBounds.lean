import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.SourceSemantics.CoreLowering.ProtectedStateAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeIndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeBodies
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallBounds
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence

/-!
# Owned callables: invocation bounds

Allocation readiness, method and named invocation bounds, the named caller protocol, and fault contracts of named bodies.

`StableOwner` is here and not beside `Ready`, because it binds `keys` explicitly: in one file Lean would reuse the proofs of the copies that bind it implicitly.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCallerProtocol
/-! A stronger caller returns the same actual reached pool using the real
map, world, administrative and Source heap receipts. Its own static admission
and canonical slots stay separate from the selected named body's admission. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCallerProtocol
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

/-- Slots are authentic static caller receipts. Returning accepts the actual
post pool and every original preservation receipt, so stronger caller facts
need never be inferred from a bare pool. -/
structure Carrier (slots : ProtectedStateTransition.Index → Prop)
    (caller : ProtectedStateTransition.Protocol.{u, 0} (Records keys)) where
  pool : ∀ {index}, caller.State index → State headers keys index
  records_eq : ∀ {index} (state : caller.State index), caller.records state = records (pool state)
  related : ∀ {initial reached} {first : caller.State initial} {last : caller.State reached},
    caller.Relates first last → Relates (pool first) (pool last)
  slots : ∀ {index}, caller.State index → slots index
  restore : ∀ {index} (initial : caller.State index) {mapping world heap store}
    (reached : State headers keys (index.extend mapping world heap store)),
    LocationMap.Extends index.mapping mapping → WorldExtends index.world world →
    AdministrativePreserved index.mapping index.store mapping store →
    Dynamic.HeapMetadataExtend index.heap heap → Relates (pool initial) reached →
    ∃ returned : caller.State (index.extend mapping world heap store),
      pool returned = reached ∧ caller.Relates initial returned

/-- The returned wrapper observes exactly the actual ordered reached records,
including repeated snapshots. -/
theorem Carrier.returned_records {slots : ProtectedStateTransition.Index → Prop}
    {caller : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (carrier : Carrier (headers := headers) slots caller)
    {index : ProtectedStateTransition.Index} {mapping world heap store}
    {returned : caller.State (index.extend mapping world heap store)}
    {reached : State headers keys (index.extend mapping world heap store)}
    (same : carrier.pool returned = reached) : caller.records returned = records reached :=
  (carrier.records_eq returned).trans (congrArg (fun state => records state) same)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCallerProtocol
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCallerSlotForgetting
/-! A caller may retain stronger slot receipts while ordinary recursive
children use exactly the same pool, records, restoration and state relation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCallerProtocol
open CallableIndexedOwnedFunctionState
universe u
variable {compiled : Frontend.SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

/-- Forget only the slot proposition; all operational state fields remain
those of the original carrier. -/
def Carrier.forgetSlots {slots : ProtectedStateTransition.Index → Prop}
    {caller : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (carrier : Carrier (headers := headers) slots caller) :
    Carrier (headers := headers) (fun _ => True) caller where
  pool := carrier.pool
  records_eq := carrier.records_eq
  related := carrier.related
  slots := fun _ => trivial
  restore := carrier.restore

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCallerProtocol
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationReadiness
/-! Actual body origins seed a fixed selected physical frame and its stable
authenticated native token. Reached pool authority provides the current ghost
receipt at each allocation; no ghost-history transport law is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationProducer
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

/-- A body origin supplies its fixed physical owner and stable native
authentication. This seed is independent of reached pools and heap effects. -/
def StableOwner (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program))
    (location : Location) (native : NativeFrame) : Prop :=
  ∃ selected : Fin keys.length, ∃ ghost metadata,
    keys[selected.val].frameLocation = location ∧
    Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata

theorem stableOwner_selected (selected : Fin keys.length)
    {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata) :
    StableOwner keys keys[selected.val].frameLocation native :=
  ⟨selected, ghost, metadata, rfl, stable⟩

theorem readyAt_of_stable_read {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
    (selected : Fin keys.length) {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt (producer headers keys model)
      keys[selected.val].frameLocation native := by
  intro index reached read
  exact ready_of_stable_read reached selected read stable

theorem readyAt_of_owner_eq {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
    (selected : Fin keys.length) {location : Location} {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (physicalOwner : keys[selected.val].frameLocation = location)
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt (producer headers keys model) location native := by
  subst location
  exact readyAt_of_stable_read model selected stable

theorem readyAt_of_stableOwner {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
    {location : Location} {native : NativeFrame} (seed : StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt (producer headers keys model) location native := by
  obtain ⟨selected, ghost, metadata, physicalOwner, stable⟩ := seed
  exact readyAt_of_owner_eq model selected physicalOwner stable

/-- A read view is a transient Current receipt, so it cannot satisfy the
stable Carries acquisition required by ordinary snapshot production. -/
theorem not_ready_view {index : ProtectedStateTransition.Index} (state : State headers keys index)
    (location : Location) (id target : Word) (caller : Int) :
    ¬ Ready state location (.view id target caller) := by
  intro ready
  obtain ⟨selected, metadata, _physicalOwner, current, stable⟩ := ready
  rw [current] at stable
  cases stable

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationProducer
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodInvocationBounds
/-! Actual method invocation retains its independent raw source body and
complete dictionary. The real hook installs the selected physical pool row;
shared marked parameters produce the body state, whose reached pool is restored. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodInvocationBounds
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open RecursiveNamedCatalogInvocationBounds (Below)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

/-- Complete dynamic parameter receipts. The body is still an original static
origin and no execution meaning is stored in this entry. -/
structure ParameterEntry (layout : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : SourceCoreCallableIndexedFrames.Frame) (values : SourceCoreCompatibleValues.Context)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (function : Dynamic.Closure) (context : SourceSemantics.Context) (bindings : List Binding)
    (arguments : List Dynamic.Value) (before : Dynamic.Heap) (initialStore : Store)
    (initialMap : LocationMap) (initialWorld : StoreTyping) (administrative actualContext : Core.Context)
    (actual : Environment) (ξ : Renaming) (parameterCode body : Expr) where
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  actualBody : Environment
  store : Store
  mapping : LocationMap
  world : StoreTyping
  embedding : Renaming
  allocation : Dynamic.BindersAllocate [] before function.parameters arguments environment heap
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative)
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical ambient.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before heap
  lookups : EnvironmentsAgree embedding canonical actualBody
  actualTyped : RuntimeEnvironmentHasTypes world actualBody
    (CallableIndexedParameterTyped.prefixContext bindings actualContext) ambient.definitions
  reference : canonical[(bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + globals]? =
    some (.cellRef layout.type contextLocation)
  read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native)
  unmapped : contextLocation ∉ mapping
  agreement : ContinuationAgreement actual initialStore (parameterCode.rename ξ) actualBody store (body.rename embedding)

section Parameters
theorem parameter_entry_with_state
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
    (producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys) layouts layout
      (CompatibleAmbientHeap.payloadModel values.checked registry functions))
    (initial : State headers keys ⟨[], mapping, world, before, store, canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary contextLocation native) :
    ∃ entry : ParameterEntry layout globals contextLocation native values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body,
      ∃ added : Environment, added.length = bindings.length ∧
        entry.canonical = added ++ DataPatternValues.packValues nativeArguments :: canonical ∧
        ProtectedStateTransition.Transition (protocol headers keys) initial
          ⟨bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := by
  have tree := CallableIndexedParameterCertificates.of_accepted onError accepted
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) canonical
      (DataPatternValues.packValues nativeArguments :: canonical) := by
    intro index value found; exact found
  have length : (bindings.map Prod.snd).length = nativeArguments.length := by simpa using represented.length.2
  obtain ⟨environment, heap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding,
      allocated, finalEnvironments, finalHeaps, maps, worlds, preservation, _, lookups, spine, finalTyped, agreement, reached, related⟩ :=
    CallableIndexedParameterTyped.Stateful.prefix_typed tree (protocol headers keys) producer definitions registered represented environments heaps
      sourceLayout actualLayout actualTyped (allTypes := bindings.map Prod.snd) (named := true) rfl (by simp) length
      (fun {_ _} found => by simpa using found) (CallableIndexedParameters.inputKinds inputs)
      (by simpa using reference) read unmapped initial readyAt
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have bundleTyped := (CallableIndexedParameters.Arguments.pack_typed represented).weaken worlds
  have finalWithBundle := CallableIndexedParameterTyped.insert_administrative_receipt finalEnvironments bundleTyped
  have scopeLength : (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) []).length = bindings.length := by simp
  have exactEnvironment : Environment.insertAt finalCanonical bindings.length
      (DataPatternValues.packValues nativeArguments) = finalLogical := by
    rw [canonicalEq, ← prefixLength, CallableIndexedParameterTyped.insert_at_suffix_receipt, logicalEq]
  rw [scopeLength, exactEnvironment, CallableIndexedParameters.scope_eq] at finalWithBundle
  have finalReference : finalLogical[(bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + globals]? =
      some (.cellRef layout.type contextLocation) := by
    rw [logicalEq]
    simp only [List.length_map, List.length_reverse]
    have index : bindings.length + 1 + globals = added.length + (globals + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using reference
  obtain ⟨finalUnmapped, unchanged⟩ := preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1
  rw [← parameters] at allocated
  have mono := FunctionCallBody.mono_binders extended
  exact ⟨⟨environment, heap, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding,
    allocated, by simpa using finalWithBundle, finalHeaps,
    GenericLexicalContext.binders_agree mono.1 mono.2 initialLocals allocated,
    maps, worlds, preservation, GenericLexicalContext.binders_metadata allocated, lookups, finalTyped,
    finalReference, unchanged.trans read, finalUnmapped, agreement⟩, added, prefixLength, logicalEq, reached, related⟩


theorem parameter_prefix_with_state
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
    (producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys) layouts layout
      (CompatibleAmbientHeap.payloadModel values.checked registry functions))
    (initial : State headers keys ⟨[], mapping, world, before, store, canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary contextLocation native)
    {size : Nat} {result : Value} {afterStore : Store}
    (completed : EvaluationSize size actual store (parameterCode.rename ξ) result afterStore) :
    ∃ entry : Prefix layout globals contextLocation native values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body size result afterStore,
      ∃ added : Environment, added.length = bindings.length ∧
        entry.canonical = added ++ DataPatternValues.packValues nativeArguments :: canonical ∧
        ProtectedStateTransition.Transition (protocol headers keys) initial
          ⟨bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := by
  have tree := CallableIndexedParameterCertificates.of_accepted onError accepted
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) canonical
      (DataPatternValues.packValues nativeArguments :: canonical) := by
    intro index value found; exact found
  have length : (bindings.map Prod.snd).length = nativeArguments.length := by simpa using represented.length.2
  obtain ⟨environment, heap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding, child,
      allocated, finalEnvironments, finalHeaps, maps, worlds, preservation, _, lookups, spine, finalTyped, bodyCompletion, childLe, childStrict, reached, related⟩ :=
    RecursiveNamedCallBounds.Stateful.parameter_prefix tree (protocol headers keys) producer definitions registered represented environments heaps
      sourceLayout actualLayout actualTyped (allTypes := bindings.map Prod.snd) (named := true) rfl (by simp) length
      (fun {_ _} found => by simpa using found) (CallableIndexedParameters.inputKinds inputs)
      (by simpa using reference) read unmapped initial readyAt completed
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have bundleTyped := (CallableIndexedParameters.Arguments.pack_typed represented).weaken worlds
  have finalWithBundle := CallableIndexedParameterTyped.insert_administrative_receipt finalEnvironments bundleTyped
  have scopeLength : (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) []).length = bindings.length := by simp
  have exactEnvironment : Environment.insertAt finalCanonical bindings.length
      (DataPatternValues.packValues nativeArguments) = finalLogical := by
    rw [canonicalEq, ← prefixLength, CallableIndexedParameterTyped.insert_at_suffix_receipt, logicalEq]
  rw [scopeLength, exactEnvironment, CallableIndexedParameters.scope_eq] at finalWithBundle
  have finalReference : finalLogical[(bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + globals]? =
      some (.cellRef layout.type contextLocation) := by
    rw [logicalEq]
    simp only [List.length_map, List.length_reverse]
    have index : bindings.length + 1 + globals = added.length + (globals + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using reference
  obtain ⟨finalUnmapped, unchanged⟩ := preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1
  rw [← parameters] at allocated
  have mono := FunctionCallBody.mono_binders extended
  refine ⟨⟨environment, heap, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding,
    allocated, by simpa using finalWithBundle, finalHeaps,
    GenericLexicalContext.binders_agree mono.1 mono.2 initialLocals allocated,
    maps, worlds, preservation, GenericLexicalContext.binders_metadata allocated, lookups, finalTyped,
    finalReference, unchanged.trans read, finalUnmapped, child, bodyCompletion, childLe, childStrict⟩, added, prefixLength, ?_, reached, related⟩
  exact logicalEq

end Parameters

section Method
variable {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {code : Expr} (generation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {expressionSyntax : ExpressionId → Prop} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : CallablePreparedMethodCatalogHookMeaning.ProfileFor generation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) sourceBody dictionary administrative registry faults
    expressionSyntax certificates validity diagnosticPolicy)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (escaped : faults .controlEscapedFunction generation.own.table.escapedReason)
  (extend : ∀ {context next binder}, validity context → BinderExtends sourceBody.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context →
    CompatibleRuntimeContextValidity.Valid named.specialized.function.solvedRequirements context dictionary)

/-- This is the original independent method source and dictionary, with its
complete static kernel profile. No ordinary source instantiation is inferred. -/
abbrev origin := CallableRuntimeBodyStaticOrigins.method generation profile escaped extend runtimeOf

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : Installed generation (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := sourceBody) (administrative := administrative)
    functions mapping world before store callerEnvironment)
  (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world named.inputs arguments payloads)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (sameFrame : installed.frameLocation = owner.key.frameLocation)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)

private theorem rename_prefix (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

private theorem next_evaluates (index : Int) (actual : Environment) (initialStore : Store) (saved : Value) :
    Evaluates (saved :: actual) initialStore
      ((SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)).weakenAt 0)
      (encode compiled.indexed.ancestry.layout.frame (.state index)) initialStore := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

include profile in
private theorem accepted_parameters : SourceCoreSourceCells.bindParameters
    (CallableIndexedNamedGeneration.allocator compiled.indexed named) sourceBody.source [] named.inputs
    named.signature.resultType SourceCoreFunctions.argumentProjection generation.body = .ok generation.parameterCode := by
  rw [profile.sameSource]
  exact generation.parametersCompiled

include sameFrame in
/-- Both original reads refer to the same physical cell. Its saved native
frame therefore agrees with the actual selected pool row; no ghost-history
substitution or equality of record lists is assumed. -/
theorem installed_current_eq : installed.current = (caller.rows owner.position).authority.current := by
  have physical : (caller.rows owner.position).authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  have poolRead : store.read? owner.key.frameLocation = some
      (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current) := by
    simpa only [physical] using (caller.rows owner.position).authority.frame.read
  have originalRead : store.read? owner.key.frameLocation = some
      (encode compiled.indexed.ancestry.layout.frame installed.current) := by
    simpa only [sameFrame] using installed.caller.read
  have encoded := Option.some.inj (originalRead.symm.trans poolRead)
  have decoded := congrArg (decode compiled.indexed.ancestry.layout.frame) encoded
  rw [decode_encode, decode_encode] at decoded
  exact Option.some.inj decoded

include profile installed represented sameFrame heaps in
/-- The actual pool is installed at the method's real physical frame before
shared marked parameters allocate every snapshot. Complete method captures and
ordered canonical spines accompany the actual parameter post witness. -/
theorem parameters_with_state :
    ∃ originId index metadata,
      compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some originId ∧
      Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table (.state index) (.named originId) (some metadata) ∧
      generation.output = withFrame (.var (compiled.indexed.base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)) generation.parameterCode ∧
    ∃ entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) profile.context named.inputs arguments before
      (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative (.unit :: compiled.indexed.ancestry.layout.frame.type :: named.signature.parameterType :: installed.capturedContext)
      (.unit :: encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current ::
        DataPatternValues.packValues payloads :: installed.captured)
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) installed.embedding.lift))
      generation.parameterCode generation.body,
    ∃ added : Environment, added.length = named.inputs.length ∧
      entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
          entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := by
  obtain ⟨originId, index, metadata, owned, history, emitted⟩ :=
    CallableIndexedFormation.namedBody_history compiled.indexed.ancestry generation.hook
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  have read : store.read? owner.key.frameLocation = some (encode compiled.indexed.ancestry.layout.frame authority.current) := by
    simpa only [physical] using authority.frame.read
  have unmapped : owner.key.frameLocation ∉ mapping := by simpa only [physical] using authority.unmapped
  have typed : world[owner.key.frameLocation]? = some compiled.indexed.ancestry.layout.frame.type := by
    simpa only [physical] using authority.typed
  let installedPool := install caller owner.position (.stable history)
  let initial : State headers keys ⟨[], mapping, world, before,
      store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)), installed.canonical⟩ := installedPool
  obtain ⟨installedHeaps, nextCell⟩ := CallableIndexedBodyFrames.install profile.registered heaps unmapped typed
    (show CellState compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame owner.key.frameLocation authority.current authority.ghost store from
      by simpa only [physical] using authority.frame) (.stable history)
  let producer := CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary owner.key.frameLocation (.state index) :=
    CallableIndexedOwnedAllocationProducer.readyAt_of_stable_read
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) owner.position history
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues payloads) named.signature.parameterType
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
    profile.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons
    (RuntimeValueHasType.unit (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions))
    (.cons (encode_runtime_typed world profile.registered authority.current) (.cons packTyped installed.captureTyped))
  have actualLayout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) installed.embedding.lift))
      (DataPatternValues.packValues payloads :: installed.canonical)
      (.unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: installed.captured) :=
    GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
      (encode compiled.indexed.ancestry.layout.frame authority.current)) .unit
  obtain ⟨entry, added, length, spine, reached, related⟩ := parameter_entry_with_state
    (compiled := compiled) (program := program) (headers := headers) (keys := keys)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (registry := registry) (layouts := compiled.indexed.layouts) (owner := named.signature.key) (active := [])
    (layout := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
    (function := methodFunction generation sourceBody dictionary) functions
    (fun error => .sourceAllocation (reprStr error)) (accepted_parameters generation profile)
    profile.parameters profile.parameters profile.extended profile.definitions profile.registered represented
    installed.environments installedHeaps installed.locals actualLayout actualTyped
    (by simpa only [sameFrame] using installed.canonicalReference) nextCell.read unmapped producer initial readyAt
  exact ⟨originId, index, metadata, owned, history, emitted, entry, added, length, spine, reached,
    (install_related caller owner.position (.stable history)).trans related⟩

include profile installed represented sameFrame heaps in
/-- Original native hook inversion selects its strict parameter child; the
shared parameter fold produces the actual body pool and keeps the exact final
saved-frame write from that same completion. -/
theorem body_prefix_with_state {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: installed.captured) store
      (generation.output.rename installed.embedding.lift) value finalStore) :
    ∃ originId index metadata prefixSize bodyStore,
      compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some originId ∧
      Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table (.state index) (.named originId) (some metadata) ∧
      prefixSize < size ∧
      finalStore = bodyStore.set owner.key.frameLocation
        (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current) ∧
    ∃ entry : Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) profile.context named.inputs arguments before
      (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative (.unit :: compiled.indexed.ancestry.layout.frame.type :: named.signature.parameterType :: installed.capturedContext)
      (.unit :: encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current ::
        DataPatternValues.packValues payloads :: installed.captured)
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) installed.embedding.lift))
      generation.parameterCode generation.body prefixSize value bodyStore,
    ∃ added : Environment, added.length = named.inputs.length ∧
      entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
          entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := by
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  have read : store.read? owner.key.frameLocation = some (encode compiled.indexed.ancestry.layout.frame authority.current) := by
    simpa only [physical] using authority.frame.read
  have unmapped : owner.key.frameLocation ∉ mapping := by simpa only [physical] using authority.unmapped
  have typed : world[owner.key.frameLocation]? = some compiled.indexed.ancestry.layout.frame.type := by
    simpa only [physical] using authority.typed
  have reference : (DataPatternValues.packValues payloads :: installed.captured)[installed.embedding.lift
      (compiled.indexed.base.globals.length + 1)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    simpa only [sameFrame, Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using installed.capturedReference
  obtain ⟨originId, index, metadata, owned, history, emitted⟩ :=
    CallableIndexedFormation.namedBody_history compiled.indexed.ancestry generation.hook
  have renamed : generation.output.rename installed.embedding.lift = withFrame
      (.var (installed.embedding.lift (compiled.indexed.base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index))
      (generation.parameterCode.rename installed.embedding.lift) := by
    rw [emitted, NamedCalls.withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  rw [renamed] at completed
  obtain ⟨nextSize, prefixSize, nextValue, nextStore, bodyStore, nextCompletion, prefixCompletion,
    _sizeBound, smaller, restored⟩ := RecursiveNamedCallBounds.with_frame (.var reference) read completed
  obtain ⟨nextEq, nextStoreEq⟩ := evaluation_deterministic nextCompletion.sound
    (next_evaluates index (DataPatternValues.packValues payloads :: installed.captured) store
      (encode compiled.indexed.ancestry.layout.frame authority.current))
  rw [nextEq, nextStoreEq, ← rename_prefix] at prefixCompletion
  let installedPool := install caller owner.position (.stable history)
  let initial : State headers keys ⟨[], mapping, world, before,
      store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)), installed.canonical⟩ := installedPool
  obtain ⟨installedHeaps, nextCell⟩ := CallableIndexedBodyFrames.install profile.registered heaps unmapped typed
    (show CellState compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame owner.key.frameLocation authority.current authority.ghost store from
      by simpa only [physical] using authority.frame) (.stable history)
  let producer := CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary owner.key.frameLocation (.state index) :=
    CallableIndexedOwnedAllocationProducer.readyAt_of_stable_read
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) owner.position history
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues payloads) named.signature.parameterType
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
    profile.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons
    (RuntimeValueHasType.unit (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions))
    (.cons (encode_runtime_typed world profile.registered authority.current) (.cons packTyped installed.captureTyped))
  have actualLayout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) installed.embedding.lift))
      (DataPatternValues.packValues payloads :: installed.canonical)
      (.unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: installed.captured) :=
    GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
      (encode compiled.indexed.ancestry.layout.frame authority.current)) .unit
  obtain ⟨entry, added, length, spine, reached, related⟩ := parameter_prefix_with_state
    (compiled := compiled) (program := program) (headers := headers) (keys := keys)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (registry := registry) (layouts := compiled.indexed.layouts) (owner := named.signature.key) (active := [])
    (layout := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
    (function := methodFunction generation sourceBody dictionary) functions
    (fun error => .sourceAllocation (reprStr error)) (accepted_parameters generation profile)
    profile.parameters profile.parameters profile.extended profile.definitions profile.registered represented
    installed.environments installedHeaps installed.locals actualLayout actualTyped
    (by simpa only [sameFrame] using installed.canonicalReference) nextCell.read unmapped producer initial readyAt prefixCompletion
  exact ⟨originId, index, metadata, prefixSize, bodyStore, owned, history, smaller, restored,
    entry, added, length, spine, reached, (install_related caller owner.position (.stable history)).trans related⟩

/-- All actual parameter fields are projected verbatim into the method origin.
The state and gate identify the genuine selected frame at that reached index. -/
def parameter_entry_origin {location : Location} {native : NativeFrame}
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      location native (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) profile.context named.inputs arguments before store mapping world
      administrative actualContext actual ξ generation.parameterCode generation.body)
    (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (gate : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    CallableRuntimeBodyOrigins.Stateful.Entry (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin generation profile escaped extend runtimeOf) functions where
  mapping := entry.mapping
  world := entry.world
  environment := entry.environment
  canonical := entry.canonical
  actual := entry.actualBody
  heap := entry.heap
  store := entry.store
  embedding := entry.embedding
  actualContext := CallableIndexedParameterTyped.prefixContext named.inputs actualContext
  frameLocation := location
  native := native
  environments := entry.environments
  heaps := entry.heaps
  locals := entry.locals
  lookups := entry.lookups
  actualTyped := entry.actualTyped
  reference := entry.reference
  read := entry.read
  unmapped := entry.unmapped
  initial := reached
  gate := gate

/-- Native prefix fields identify the same original method origin, with the
body witness and pool returned by the actual measured prefix. -/
def prefix_entry_origin {location : Location} {native : NativeFrame}
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {size : Nat} {value : Value} {finalStore : Store}
    (entry : Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      location native (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) profile.context named.inputs arguments before store mapping world
      administrative actualContext actual ξ generation.parameterCode generation.body size value finalStore)
    (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (gate : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    CallableRuntimeBodyOrigins.Stateful.Entry (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin generation profile escaped extend runtimeOf) functions where
  mapping := entry.mapping
  world := entry.world
  environment := entry.environment
  canonical := entry.canonical
  actual := entry.actualBody
  heap := entry.heap
  store := entry.store
  embedding := entry.embedding
  actualContext := CallableIndexedParameterTyped.prefixContext named.inputs actualContext
  frameLocation := location
  native := native
  environments := entry.environments
  heaps := entry.heaps
  locals := entry.locals
  lookups := entry.lookups
  actualTyped := entry.actualTyped
  reference := entry.reference
  read := entry.read
  unmapped := entry.unmapped
  initial := reached
  gate := gate

/-- The body contract is specialized to the actual source-produced method
parameter entry, its ordered capture spine and the same reached pool. -/
def SourceContinuation (budget : Nat) : Prop :=
  ∀ {initialStore : Store} {location : Location} {native : NativeFrame}
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      location native (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) profile.context named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ generation.parameterCode generation.body)
    (added : Environment), added.length = named.inputs.length →
    entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical →
  ∀ (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (gate : CallableIndexedOwnedAllocationProducer.StableOwner keys location native),
    Below budget (CallableRuntimeBodyEntryContracts.PreservesAt
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (protocol := protocol headers keys)
      (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      functions program (parameter_entry_origin generation profile functions escaped extend runtimeOf entry reached gate))

/-- Original native parameter inversion retains its full ordered capture
spine and independent strict body grade at the actual reached pool. -/
def NativeContinuation (budget : Nat) : Prop :=
  ∀ {initialStore : Store} {location : Location} {native : NativeFrame}
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {size : Nat} {value : Value} {finalStore : Store}
    (entry : Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      location native (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) profile.context named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ generation.parameterCode generation.body size value finalStore)
    (added : Environment), added.length = named.inputs.length →
    entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical →
  ∀ (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (gate : CallableIndexedOwnedAllocationProducer.StableOwner keys location native),
    Below budget (CallableRuntimeBodyEntryContracts.ReflectsAt
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (protocol := protocol headers keys)
      (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      functions program (prefix_entry_origin generation profile functions escaped extend runtimeOf entry reached gate))

/-- Actual hook ownership and the original named ghost accompany the complete
Source parameter post. The original caller relation and every prefix field are
available before selecting that actual body's continuation. -/
def SourceContinuationWithHistory (budget : Nat) : Prop :=
  ∀ (originId : Word) (index : Int) (metadata : MetadataState)
    (_selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named named.signature.key) = some originId)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named originId) (some metadata))
    (_emitted : generation.output = withFrame (.var (compiled.indexed.base.globals.length + 1))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)) generation.parameterCode)
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) profile.context named.inputs arguments before
      (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative (.unit :: compiled.indexed.ancestry.layout.frame.type :: named.signature.parameterType :: installed.capturedContext)
      (.unit :: encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current ::
        DataPatternValues.packValues payloads :: installed.captured)
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) installed.embedding.lift))
      generation.parameterCode generation.body)
    (added : Environment), added.length = named.inputs.length →
    entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical →
  ∀ (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩),
    Relates caller reached →
    Below budget (CallableRuntimeBodyEntryContracts.PreservesAt
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (protocol := protocol headers keys)
      (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      functions program (parameter_entry_origin generation profile functions escaped extend runtimeOf entry reached
        (CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position history)))

/-- Native inversion supplies the same actual hook history, measured prefix,
body completion and saved-frame write. The independent Source body contract is
selected at that exact reached parameter pool. -/
def NativeContinuationWithHistory (budget : Nat) : Prop :=
  ∀ (originId : Word) (index : Int) (metadata : MetadataState) (prefixSize : Nat) (bodyStore : Store)
    (_selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named named.signature.key) = some originId)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named originId) (some metadata))
    (_prefixWithin : prefixSize < budget)
    {value : Value} {finalStore : Store}
    (_restored : finalStore = bodyStore.set owner.key.frameLocation
      (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current))
    (entry : Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation (.state index) (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) profile.context named.inputs arguments before
      (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative (.unit :: compiled.indexed.ancestry.layout.frame.type :: named.signature.parameterType :: installed.capturedContext)
      (.unit :: encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current ::
        DataPatternValues.packValues payloads :: installed.captured)
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) installed.embedding.lift))
      generation.parameterCode generation.body prefixSize value bodyStore)
    (added : Environment), added.length = named.inputs.length →
    entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical →
  ∀ (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩),
    Relates caller reached →
    Below budget (CallableRuntimeBodyEntryContracts.ReflectsAt
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (protocol := protocol headers keys)
      (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      functions program (prefix_entry_origin generation profile functions escaped extend runtimeOf entry reached
        (CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position history)))

include profile installed represented sameFrame heaps in
/-- Independent source method invocation selects its genuine strict body
child. Actual parameters enter the origin-neutral body family, and restoration
uses that body's reached pool, retaining every complete ordered row list. -/
theorem invocation_preserves_bounded_at_with_history (budget : Nat)
    (bodyMeaning : SourceContinuationWithHistory (program := program) (headers := headers) (keys := keys)
      (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) generation profile functions escaped extend runtimeOf installed budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome program size sourceBody dictionary before arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (generation.output.rename installed.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  have arity : (methodFunction generation sourceBody dictionary).parameters.length = arguments.length := by
    change sourceBody.source.inputs.length = arguments.length
    rw [profile.parameters, List.length_map]
    exact represented.length.1
  obtain ⟨child, environment, bound, allocated, bodyTrace, smaller⟩ :=
    RecursiveNamedCallBounds.body_trace_of_fields profile.sourceFrame.source profile.sourceFrame.context
      profile.sourceFrame.parameters profile.sourceFrame.result profile.sourceFrame.roots profile.extended arity trace
  obtain ⟨originId, index, metadata, owned, history, emitted, entry, added, length, spine, parameterState, parameterRelated⟩ :=
    parameters_with_state generation profile functions installed represented owner caller sameFrame heaps
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  let actualEntry := parameter_entry_origin generation profile functions escaped extend runtimeOf entry parameterState
    (CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position history)
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, _exit, bodyState, bodyRelated⟩ :=
    bodyMeaning originId index metadata owned history emitted entry added length spine parameterState parameterRelated
      child (Nat.lt_of_lt_of_le smaller within) bodyTrace
  have prefixEvaluation := entry.agreement.wrap bodyEvaluation
  rw [rename_prefix] at prefixEvaluation
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  have read : store.read? owner.key.frameLocation = some (encode compiled.indexed.ancestry.layout.frame authority.current) := by
    simpa only [physical] using authority.frame.read
  have reference : (DataPatternValues.packValues payloads :: installed.captured)[installed.embedding.lift
      (compiled.indexed.base.globals.length + 1)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    simpa only [sameFrame, Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using installed.capturedReference
  have evaluated := CallableContextFrames.withFrame_evaluates (.var reference) read
    (next_evaluates index (DataPatternValues.packValues payloads :: installed.captured) store
      (encode compiled.indexed.ancestry.layout.frame authority.current)) prefixEvaluation
  have renamed : generation.output.rename installed.embedding.lift = withFrame
      (.var (installed.embedding.lift (compiled.indexed.base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index))
      (generation.parameterCode.rename installed.embedding.lift) := by
    rw [emitted, NamedCalls.withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have frame := entry.frame.trans bodyFrame
  have sourceMetadata := entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := parameterRelated.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, _bodyRelated, _callerRelated, _records, returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position profile.registered
      finalHeaps worlds frame related
  refine ⟨value, _, finalMap, finalWorld, ?_, result, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata, returned⟩
  exact renamed.symm ▸ evaluated

include profile installed represented sameFrame heaps in
/-- Independent source method invocation selects its genuine strict body
child. Actual parameters enter the origin-neutral body family, and restoration
uses that body's reached pool, retaining every complete ordered row list. -/
theorem invocation_preserves_bounded_at (budget : Nat)
    (bodyMeaning : SourceContinuation (program := program) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads) generation profile functions escaped extend runtimeOf installed budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome program size sourceBody dictionary before arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (generation.output.rename installed.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  exact invocation_preserves_bounded_at_with_history generation profile functions escaped extend runtimeOf installed represented
    owner caller sameFrame heaps budget
    (fun _originId _index _metadata _selected history _emitted entry added length spine reached _related =>
      bodyMeaning entry added length spine reached
        (CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position history))
    trace within

include profile in
private theorem body_of_trace_sized {size : Nat} {environment : Dynamic.Environment} {bound after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate [] before sourceBody.source.inputs arguments environment bound)
    (trace : RecursiveNamedCallBounds.BodyTrace program size (methodFunction generation sourceBody dictionary)
      profile.context environment bound outcome after) :
    RecursiveNamedCallBounds.BodyOutcome program (SourceExecutionSize.stepSize [size]) sourceBody dictionary before arguments outcome after := by
  cases trace with
  | returned executed => exact .value (.returned profile.sourceFrame.covers profile.sourceFrame.roots profile.extended allocated executed rfl)
  | unit same executed => exact .value (.unit profile.sourceFrame.covers same profile.sourceFrame.roots profile.extended allocated executed ⟨_, rfl⟩)
  | fault failed => exact .fault (.statements profile.sourceFrame.roots profile.extended allocated failed)
  | escaped executed escape => exact .fault (.controlEscape profile.sourceFrame.roots profile.extended allocated executed escape)

include profile installed represented sameFrame heaps in
/-- Native hook reflection consumes its actual parameter and body witnesses.
The independent source method grade and full dictionary are reconstructed;
the completed body pool supplies every record retained by caller restoration. -/
theorem invocation_reflects_bounded_at_with_history (budget : Nat)
    (bodyMeaning : NativeContinuationWithHistory (program := program) (headers := headers) (keys := keys)
      (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) generation profile functions escaped extend runtimeOf installed budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: installed.captured) store
      (generation.output.rename installed.embedding.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome program sourceSize sourceBody dictionary before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  obtain ⟨originId, index, metadata, prefixSize, bodyStore, owned, history, strict, restored,
    entry, added, length, spine, parameterState, parameterRelated⟩ :=
    body_prefix_with_state generation profile functions installed represented owner caller sameFrame heaps completed
  let actualEntry := prefix_entry_origin generation profile functions escaped extend runtimeOf entry parameterState
    (CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position history)
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, bodyTrace, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, _exit, bodyState, bodyRelated⟩ :=
    bodyMeaning originId index metadata prefixSize bodyStore owned history
      (Nat.lt_of_lt_of_le strict within) restored entry added length spine parameterState parameterRelated
      entry.childSize (Nat.lt_of_le_of_lt entry.bounded (Nat.lt_of_lt_of_le strict within)) entry.completed
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have frame := entry.frame.trans bodyFrame
  have sourceMetadata := entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := parameterRelated.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, _bodyRelated, _callerRelated, _records, returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position profile.registered
      finalHeaps worlds frame related
  subst finalStore
  exact ⟨_, outcome, after, finalMap, finalWorld,
    body_of_trace_sized generation profile entry.allocation bodyTrace,
    result, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata, returned⟩

include profile installed represented sameFrame heaps in
/-- Native hook reflection consumes its actual parameter and body witnesses.
The independent source method grade and full dictionary are reconstructed;
the completed body pool supplies every record retained by caller restoration. -/
theorem invocation_reflects_bounded_at (budget : Nat)
    (bodyMeaning : NativeContinuation (program := program) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads) generation profile functions escaped extend runtimeOf installed budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: installed.captured) store
      (generation.output.rename installed.embedding.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome program sourceSize sourceBody dictionary before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  exact invocation_reflects_bounded_at_with_history generation profile functions escaped extend runtimeOf installed represented
    owner caller sameFrame heaps budget
    (fun _originId _index _metadata _prefixSize _bodyStore _selected history _prefixWithin {_value} {_finalStore}
      _restored entry added length spine reached _related =>
      bodyMeaning entry added length spine reached
        (CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position history))
    completed within

include profile installed represented sameFrame heaps in
/-- Independent source method invocation selects its genuine strict body
child. Actual parameters enter the origin-neutral body family, and restoration
uses that body's reached pool, retaining every complete ordered row list. -/
theorem invocation_preserves_bounded_with (budget : Nat)
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program
      (origin generation profile escaped extend runtimeOf)))
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome program size sourceBody dictionary before arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (generation.output.rename installed.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  exact invocation_preserves_bounded_at generation profile functions escaped extend runtimeOf installed represented
    owner caller sameFrame heaps budget
    (fun entry _added _length _spine reached gate child strict =>
      bodyMeaning child strict (parameter_entry_origin generation profile functions escaped extend runtimeOf entry reached gate))
    trace within

include profile installed represented sameFrame heaps in
/-- Native hook reflection consumes its actual parameter and body witnesses.
The independent source method grade and full dictionary are reconstructed;
the completed body pool supplies every record retained by caller restoration. -/
theorem invocation_reflects_bounded_with (budget : Nat)
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program
      (origin generation profile escaped extend runtimeOf)))
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: installed.captured) store
      (generation.output.rename installed.embedding.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome program sourceSize sourceBody dictionary before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  exact invocation_reflects_bounded_at generation profile functions escaped extend runtimeOf installed represented
    owner caller sameFrame heaps budget
    (fun entry _added _length _spine reached gate child strict =>
      bodyMeaning child strict (prefix_entry_origin generation profile functions escaped extend runtimeOf entry reached gate))
    completed within

end Method

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodInvocationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedInvocationBounds
/-! Actual named invocation retains the installed pool through parameter
snapshots and body completion, then restores the caller in that reached pool.
The measured children come from the original Source and Core derivations. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedFunctionState

section Authorization
open CallableAncestryPairedLookup
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}

/-- Authorize a real body entry at the selected physical frame. The original
hook, history and code receipts remain independent inputs. -/
def BodyAuthorizationAt
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (header : Header prepared values ambient.definitions program) (selectedFrame : Location)
    (condition : BodyCondition (headers := headers) (locations := locations)
      (capturePrefix := capturePrefix) functions registry header) : Prop :=
  ∀ {origin index metadata arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation},
    frameLocation = selectedFrame →
    prepared.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin →
    Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) →
    header.code = withFrame (.var (base.globals.length + 1))
      (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) header.parameterCode →
    ∀ entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation (.state index) (.named origin), condition entry

/-- Legacy authorization can be used when it already proves the condition
at every frame. Actual ownership-sensitive callers use the selected receipt. -/
theorem BodyAuthorizationAt.of_universal
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {header : Header prepared values ambient.definitions program} {selectedFrame : Location}
    {condition : BodyCondition (headers := headers) (locations := locations)
      (capturePrefix := capturePrefix) functions registry header}
    (authorized : BodyAuthorization functions registry header condition) :
    BodyAuthorizationAt functions registry header selectedFrame condition := by
  intro origin index metadata arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation _physical owned history emitted entry
  exact authorized owned history emitted entry
end Authorization

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {locations : CallableIndexedOwnedFunctionValues.Header compiled program → Location}
  {capturePrefix : Nat} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store}

/-- The allocation gate retains a physical owner and its authentic carried
history, independently of the parameter entry's observer catalog. -/
def stableOwnerCondition
    (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry)
    (header : CallableIndexedOwnedFunctionValues.Header compiled program) :
    BodyCondition (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers)
      (locations := locations) (capturePrefix := capturePrefix) functions registry header :=
  fun {_ _ _ _ _ _ _ _ _ frameLocation current _} _ =>
    CallableIndexedOwnedAllocationProducer.StableOwner keys frameLocation current

/-- Actual selected-frame authorization supplies the concrete allocation gate.
No body execution law or arbitrary-frame authorization is needed. -/
theorem stable_owner_authorized
    (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry)
    (header : CallableIndexedOwnedFunctionValues.Header compiled program)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) :
    BodyAuthorizationAt (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers)
      (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header owner.key.frameLocation
      (stableOwnerCondition (keys := keys) functions registry header) := by
  intro origin index metadata arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation physical _owned history _emitted _entry
  exact ⟨owner.position, .named origin, some metadata, physical.symm, history⟩

private theorem insert_at_suffix (added suffix : Environment) (value : Value) :
    Environment.insertAt (added ++ suffix) added.length value = added ++ value :: suffix := by
  induction added with
  | nil => simp [Environment.insertAt]
  | cons head tail ih => simpa [Environment.insertAt] using congrArg (List.cons head) ih

private theorem insert_administrative {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    {value : Value} {type : Ty} (typed : RuntimeValueHasType world value type (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions) :
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked.catalog) mapping world
      (type :: administrative) scope environment (Environment.insertAt canonical scope.length value) (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions := by
  induction related with
  | nil suffixTyped => exact .nil (by simpa [Environment.insertAt] using RuntimeEnvironmentHasTypes.cons typed suffixTyped)
  | cons reference _ ih => exact .cons reference ih
  | internal reference absent _ ih => exact .internal reference absent ih

theorem parameters_with_state (authority : Authority (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers locations capturePrefix mapping world heap store)
    {header : Header (compiled.indexed.ancestry) (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions program}
    {administrative : Core.Context} {canonical : Environment}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked.catalog)
      mapping world administrative [] [] canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (locals : Dynamic.EnvironmentAgrees heap header.function.context.locals [])
    (reference : canonical[header.globals]? = some (.cellRef (compiled.indexed.ancestry).layout.frame.type authority.frameLocation))
    (coherent : ∀ target, target ∈ headers → canonical[capturePrefix + target.slot]? = some
      (.cellRef (OptionalCell.cellType target.named.signature.functionType) (locations target)))
    {functions : FunctionModel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)} {registry : SourceCoreRawMetadata.Registry}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked registry functions mapping world heap store)
    {actual actualContext ξ}
    (agrees : EnvironmentsAgree ξ (DataPatternValues.packValues payloads :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys)
      header.layouts (compiled.indexed.ancestry).layout.frame (CompatibleAmbientHeap.payloadModel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked registry functions))
    (initial : State headers keys ⟨[], mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary authority.frameLocation authority.current) :
    ∃ entry : BodyState (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers locations capturePrefix functions registry header arguments heap store mapping world
      administrative actualContext actual ξ authority.frameLocation authority.current authority.ghost,
      ProtectedStateTransition.Transition (protocol headers keys) initial
        ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ ∧
      ContinuationAgreement actual store (header.parameterCode.rename ξ) entry.actualBody entry.store
        (header.body.rename entry.embedding) := by
  have tree := CallableIndexedParameterCertificates.of_accepted header.onError header.acceptedPrefix
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) canonical
      (DataPatternValues.packValues payloads :: canonical) := by
    intro index value found; exact found
  have length : (header.bindings.map Prod.snd).length = payloads.length := by simpa using represented.length.2
  obtain ⟨environment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding,
    allocated, finalEnvironments, finalHeaps, maps, worlds, preservation, _, lookups, spine, finalTyped, agreement, reached, related⟩ :=
    CallableIndexedParameterTyped.Stateful.prefix_typed tree (protocol headers keys) producer header.definitions_eq header.registered represented environments heaps
      sourceLayout agrees actualTyped (allTypes := header.bindings.map Prod.snd) (named := true) rfl (by simp) length
      (fun {_ _} found => by simpa using found) (CallableIndexedParameters.inputKinds header.inputs)
      (by simpa using reference) authority.frame.read authority.unmapped initial readyAt
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have bundleTyped := (CallableIndexedParameters.Arguments.pack_typed represented).weaken worlds
  have finalWithBundle := insert_administrative finalEnvironments bundleTyped
  have scopeLength : (header.bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) []).length = header.bindings.length := by simp
  have exactEnvironment : Environment.insertAt finalCanonical header.bindings.length
      (DataPatternValues.packValues payloads) = finalLogical := by
    rw [canonicalEq, ← prefixLength, insert_at_suffix, logicalEq]
  rw [scopeLength, exactEnvironment, CallableIndexedParameters.scope_eq] at finalWithBundle
  rw [← header.parameters] at allocated
  have metadata := GenericLexicalContext.binders_metadata allocated
  let catalog : Entry (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers locations capturePrefix (capturePrefix + 1)
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld finalHeap finalStore finalLogical := by
    refine ⟨authority.extend maps worlds preservation metadata, ?_⟩
    intro target targetMember
    rw [logicalEq]
    simp only [List.length_map, List.length_reverse]
    have index : header.bindings.length + (capturePrefix + 1) + target.slot =
        added.length + (capturePrefix + target.slot + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using coherent target targetMember
  have finalReference : finalLogical[header.bindings.length + 1 + header.globals]? =
      some (.cellRef (compiled.indexed.ancestry).layout.frame.type authority.frameLocation) := by
    rw [logicalEq]
    have index : header.bindings.length + 1 + header.globals = added.length + (header.globals + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using reference
  have current := CallableIndexedBodyFrames.body_current authority.unmapped authority.frame preservation
  have mono := FunctionCallBody.mono_binders header.extended
  exact ⟨BodyState.of_receipts environment  finalHeap  finalLogical  finalActual  finalStore  finalMap  finalWorld  embedding
    allocated (by simpa only [List.append_nil, CallableIndexedAmbient.ambientDefinitions] using finalWithBundle) finalHeaps
    (GenericLexicalContext.binders_agree mono.1 mono.2 locals allocated)
    maps  worlds  preservation  metadata  lookups  finalTyped  catalog  finalReference  current  (by rfl)  (by rfl)  (by
      change (authority.extend maps worlds preservation metadata).ghost = authority.ghost
      rfl), ⟨reached, related⟩, agreement⟩

theorem parameters_sized_with_state (authority : Authority (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers locations capturePrefix mapping world heap store)
    {header : Header (compiled.indexed.ancestry) (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions program} (_member : header ∈ headers)
    (capture : Capture headers locations capturePrefix authority.frameLocation header mapping world heap store)
    {functions : FunctionModel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)} {registry : SourceCoreRawMetadata.Registry}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked registry functions mapping world heap store)
    {actual actualContext ξ}
    (agrees : EnvironmentsAgree ξ (DataPatternValues.packValues payloads :: capture.canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    {size : Nat} {result : Value} {afterStore : Store}
    (completed : EvaluationSize size actual store (header.parameterCode.rename ξ) result afterStore)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys)
      header.layouts (compiled.indexed.ancestry).layout.frame (CompatibleAmbientHeap.payloadModel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked registry functions))
    (initial : State headers keys ⟨[], mapping, world, heap, store, capture.canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary authority.frameLocation authority.current) :
    ∃ entry : BodyState headers locations capturePrefix functions registry header arguments heap store mapping world
      capture.administrative actualContext actual ξ authority.frameLocation authority.current authority.ghost,
      ∃ child, EvaluationSize child entry.actualBody entry.store (header.body.rename entry.embedding) result afterStore ∧
        child ≤ size ∧ (header.bindings ≠ [] → child < size) ∧
        ProtectedStateTransition.Transition (protocol headers keys) initial
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := by
  have tree := CallableIndexedParameterCertificates.of_accepted header.onError header.acceptedPrefix
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) capture.canonical
      (DataPatternValues.packValues payloads :: capture.canonical) := by
    intro index value found; exact found
  have length : (header.bindings.map Prod.snd).length = payloads.length := by simpa using represented.length.2
  obtain ⟨environment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding, child,
    allocated, finalEnvironments, finalHeaps, maps, worlds, preservation, _, lookups, spine, finalTyped, bodyCompletion, childLe, childStrict, reached, related⟩ :=
    RecursiveNamedCallBounds.Stateful.parameter_prefix tree (protocol headers keys) producer header.definitions_eq header.registered represented capture.environments heaps
      sourceLayout agrees actualTyped (allTypes := header.bindings.map Prod.snd) (named := true) rfl (by simp) length
      (fun {_ _} found => by simpa using found) (CallableIndexedParameters.inputKinds header.inputs)
      (by simpa using capture.reference) authority.frame.read authority.unmapped initial readyAt completed
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have bundleTyped := (CallableIndexedParameters.Arguments.pack_typed represented).weaken worlds
  have finalWithBundle := insert_administrative finalEnvironments bundleTyped
  have scopeLength : (header.bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) []).length = header.bindings.length := by simp
  have exactEnvironment : Environment.insertAt finalCanonical header.bindings.length
      (DataPatternValues.packValues payloads) = finalLogical := by
    rw [canonicalEq, ← prefixLength, insert_at_suffix, logicalEq]
  rw [scopeLength, exactEnvironment, CallableIndexedParameters.scope_eq] at finalWithBundle
  rw [← header.parameters] at allocated
  have metadata := GenericLexicalContext.binders_metadata allocated
  let catalog : Entry (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers locations capturePrefix (capturePrefix + 1)
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld finalHeap finalStore finalLogical := by
    refine ⟨authority.extend maps worlds preservation metadata, ?_⟩
    intro target targetMember
    rw [logicalEq]
    simp only [List.length_map, List.length_reverse]
    have index : header.bindings.length + (capturePrefix + 1) + target.slot =
        added.length + (capturePrefix + target.slot + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using capture.coherent target targetMember
  have finalReference : finalLogical[header.bindings.length + 1 + header.globals]? =
      some (.cellRef (compiled.indexed.ancestry).layout.frame.type authority.frameLocation) := by
    rw [logicalEq]
    have index : header.bindings.length + 1 + header.globals = added.length + (header.globals + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using capture.reference
  have current := CallableIndexedBodyFrames.body_current authority.unmapped authority.frame preservation
  have mono := FunctionCallBody.mono_binders header.extended
  refine ⟨BodyState.of_receipts environment  finalHeap  finalLogical  finalActual  finalStore  finalMap  finalWorld  embedding
    allocated (by simpa only [List.append_nil, CallableIndexedAmbient.ambientDefinitions] using finalWithBundle) finalHeaps
    (GenericLexicalContext.binders_agree mono.1 mono.2 capture.locals allocated)
    maps  worlds  preservation  metadata  lookups  finalTyped  catalog  finalReference  current  (by rfl)  (by rfl)  (by
      change (authority.extend maps worlds preservation metadata).ghost = authority.ghost
      rfl), child, bodyCompletion, childLe, childStrict, reached, related⟩


private theorem rename_prefix (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

private theorem next_evaluates (index : Int) (actual : Environment) (store : Store) (saved : Value) :
    Evaluates (saved :: actual) store
      ((SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)).weakenAt 0)
      (encode compiled.indexed.ancestry.layout.frame (.state index)) store := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

private theorem related_cast_frame
    {initial : ProtectedStateTransition.Index} (saved : State headers keys initial)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {first second : Location} {next : Value} (same : first = second)
    (state : State headers keys ⟨scope, mapping, world, heap, store.set first next, canonical⟩)
    (related : Relates saved state) :
    Relates saved (Eq.mp (congrArg (fun location => State headers keys
      ⟨scope, mapping, world, heap, store.set location next, canonical⟩) same) state) := by
  cases same
  exact related

private theorem readyAt_cast
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {first second : SourceCoreAllocationLayouts.Prepared}
    {frame : SourceCoreCallableIndexedFrames.Layout}
    (same : first = second)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys) second frame model)
    {location : Location} {native : NativeFrame}
    (ready : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      ((same.symm ▸ producer).toOrdinary) location native := by
  cases same
  exact ready


section Continuations
variable {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}

/-- A body producer is specialized at one complete actual parameter entry. -/
def SourceBodyAt
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    (reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) (size : Nat) : Prop :=
  ∀ {outcome after},
    RecursiveNamedCallBounds.BodyTrace program size header.function header.context entry.environment entry.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) reached
        ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          finalMap, finalWorld, after, finalStore, entry.canonical⟩

/-- Native completion retains its independent Source grade at that same entry. -/
def NativeBodyAt
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    (reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) (size : Nat) : Prop :=
  ∀ {value finalStore}, EvaluationSize size entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) reached
        ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          finalMap, finalWorld, after, finalStore, entry.canonical⟩

/-- The same actual Source body tuple also carries its literal fault post. -/
def SourceBodyAtWithPost (post : NamedInvocationFaultPostContracts.BodyFaultPost)
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    (reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) (size : Nat) : Prop :=
  ∀ {outcome after},
    RecursiveNamedCallBounds.BodyTrace program size header.function header.context entry.environment entry.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) reached
        ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          finalMap, finalWorld, after, finalStore, entry.canonical⟩ ∧
      NamedInvocationFaultPostContracts.OutcomePost post program header.function header.context
        entry.environment entry.heap entry.actualBody entry.store (header.body.rename entry.embedding)
        header.output outcome after value finalMap finalWorld finalStore

/-- Native completion carries the post at its actual body store. -/
def NativeBodyAtWithPost (post : NamedInvocationFaultPostContracts.BodyFaultPost)
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    (reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) (size : Nat) : Prop :=
  ∀ {value finalStore}, EvaluationSize size entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) reached
        ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          finalMap, finalWorld, after, finalStore, entry.canonical⟩ ∧
      NamedInvocationFaultPostContracts.OutcomePost post program header.function header.context
        entry.environment entry.heap entry.actualBody entry.store (header.body.rename entry.embedding)
        header.output outcome after value finalMap finalWorld finalStore

/-- Preserve the extra fact at the same completed body state. -/
def SourceBodyAtWithExtra (post : NamedInvocationFaultPostContracts.BodyFaultPost)
    (extra : NamedInvocationFaultPostContracts.BodyExtra (headers := headers) (keys := keys)
      (functions := functions) (registry := registry) (header := header))
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    (reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) (size : Nat) : Prop :=
  ∀ {outcome after},
    RecursiveNamedCallBounds.BodyTrace program size header.function header.context entry.environment entry.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      (∃ bodyState : State headers keys
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, after, finalStore, entry.canonical⟩,
        Relates reached bodyState ∧
        extra entry reached outcome after value finalMap finalWorld finalStore bodyState) ∧
      NamedInvocationFaultPostContracts.OutcomePost post program header.function header.context
        entry.environment entry.heap entry.actualBody entry.store (header.body.rename entry.embedding)
        header.output outcome after value finalMap finalWorld finalStore

/-- Reflect the extra fact at the same completed body state. -/
def NativeBodyAtWithExtra (post : NamedInvocationFaultPostContracts.BodyFaultPost)
    (extra : NamedInvocationFaultPostContracts.BodyExtra (headers := headers) (keys := keys)
      (functions := functions) (registry := registry) (header := header))
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    (reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) (size : Nat) : Prop :=
  ∀ {value finalStore}, EvaluationSize size entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      (∃ bodyState : State headers keys
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, after, finalStore, entry.canonical⟩,
        Relates reached bodyState ∧
        extra entry reached outcome after value finalMap finalWorld finalStore bodyState) ∧
      NamedInvocationFaultPostContracts.OutcomePost post program header.function header.context
        entry.environment entry.heap entry.actualBody entry.store (header.body.rename entry.embedding)
        header.output outcome after value finalMap finalWorld finalStore

variable (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  {arguments : List Dynamic.Value}
  (condition : BodyCondition (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header)

/-- Genuine hook history and the real parameter post precede the strict Source body. -/
def SourceContinuation (budget : Nat) : Prop :=
  ∀ {origin index metadata administrative actualContext actual ξ frameLocation},
    frameLocation = owner.key.frameLocation →
    compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin →
    Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table (.state index) (.named origin) (some metadata) →
    header.code = withFrame (.var (compiled.indexed.base.globals.length + 1))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)) header.parameterCode →
  ∀ entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations owner.key.capturePrefix functions registry header arguments heap
    (store.set frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
    administrative actualContext actual ξ frameLocation (.state index) (.named origin),
    ContinuationAgreement actual
      (store.set frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)))
      (header.parameterCode.rename ξ) entry.actualBody entry.store (header.body.rename entry.embedding) →
  ∀ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩,
    Relates caller reached → condition entry →
    Below budget (SourceBodyAt (faults := faults) entry reached)

/-- The same actual measured parameter prefix retains its strict child and saved-frame write. -/
def NativeContinuation (budget : Nat) : Prop :=
  ∀ {origin index metadata administrative actualContext actual ξ frameLocation prefixSize bodyStore value finalStore},
    frameLocation = owner.key.frameLocation →
    compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin →
    Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table (.state index) (.named origin) (some metadata) →
    header.code = withFrame (.var (compiled.indexed.base.globals.length + 1))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)) header.parameterCode →
    EvaluationSize prefixSize actual
      (store.set frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)))
      (header.parameterCode.rename ξ) value bodyStore → prefixSize < budget →
    finalStore = bodyStore.set frameLocation
      (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current) →
  ∀ entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations owner.key.capturePrefix functions registry header arguments heap
    (store.set frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
    administrative actualContext actual ξ frameLocation (.state index) (.named origin),
  ∀ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩,
    Relates caller reached → condition entry →
    Below budget (NativeBodyAt (faults := faults) entry reached)

/-- The strict actual Source child supplies its own post. -/
def SourceContinuationWithPost (post : NamedInvocationFaultPostContracts.BodyFaultPost) (budget : Nat) : Prop :=
  ∀ {origin index metadata administrative actualContext actual ξ frameLocation},
    frameLocation = owner.key.frameLocation →
    compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin →
    Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table (.state index) (.named origin) (some metadata) →
    header.code = withFrame (.var (compiled.indexed.base.globals.length + 1))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)) header.parameterCode →
  ∀ entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations owner.key.capturePrefix functions registry header arguments heap
    (store.set frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
    administrative actualContext actual ξ frameLocation (.state index) (.named origin),
    ContinuationAgreement actual
      (store.set frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)))
      (header.parameterCode.rename ξ) entry.actualBody entry.store (header.body.rename entry.embedding) →
  ∀ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩,
    Relates caller reached → condition entry →
    Below budget (SourceBodyAtWithPost post (faults := faults) entry reached)

/-- The actual measured native child supplies its own post. -/
def NativeContinuationWithPost (post : NamedInvocationFaultPostContracts.BodyFaultPost) (budget : Nat) : Prop :=
  ∀ {origin index metadata administrative actualContext actual ξ frameLocation prefixSize bodyStore value finalStore},
    frameLocation = owner.key.frameLocation →
    compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin →
    Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table (.state index) (.named origin) (some metadata) →
    header.code = withFrame (.var (compiled.indexed.base.globals.length + 1))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)) header.parameterCode →
    EvaluationSize prefixSize actual
      (store.set frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)))
      (header.parameterCode.rename ξ) value bodyStore → prefixSize < budget →
    finalStore = bodyStore.set frameLocation
      (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current) →
  ∀ entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations owner.key.capturePrefix functions registry header arguments heap
    (store.set frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
    administrative actualContext actual ξ frameLocation (.state index) (.named origin),
  ∀ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩,
    Relates caller reached → condition entry →
    Below budget (NativeBodyAtWithPost post (faults := faults) entry reached)

/-- The strict actual Source child supplies its own post. -/
def SourceContinuationWithExtra (post : NamedInvocationFaultPostContracts.BodyFaultPost)
    (extra : NamedInvocationFaultPostContracts.BodyExtra (headers := headers) (keys := keys)
      (functions := functions) (registry := registry) (header := header)) (budget : Nat) : Prop :=
  ∀ {origin index metadata administrative actualContext actual ξ frameLocation},
    frameLocation = owner.key.frameLocation →
    compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin →
    Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table (.state index) (.named origin) (some metadata) →
    header.code = withFrame (.var (compiled.indexed.base.globals.length + 1))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)) header.parameterCode →
  ∀ entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations owner.key.capturePrefix functions registry header arguments heap
    (store.set frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
    administrative actualContext actual ξ frameLocation (.state index) (.named origin),
    ContinuationAgreement actual
      (store.set frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)))
      (header.parameterCode.rename ξ) entry.actualBody entry.store (header.body.rename entry.embedding) →
  ∀ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩,
    Relates caller reached → condition entry →
    Below budget (SourceBodyAtWithExtra post extra (faults := faults) entry reached)

/-- The actual measured native child supplies its own post. -/
def NativeContinuationWithExtra (post : NamedInvocationFaultPostContracts.BodyFaultPost)
    (extra : NamedInvocationFaultPostContracts.BodyExtra (headers := headers) (keys := keys)
      (functions := functions) (registry := registry) (header := header)) (budget : Nat) : Prop :=
  ∀ {origin index metadata administrative actualContext actual ξ frameLocation prefixSize bodyStore value finalStore},
    frameLocation = owner.key.frameLocation →
    compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin →
    Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table (.state index) (.named origin) (some metadata) →
    header.code = withFrame (.var (compiled.indexed.base.globals.length + 1))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)) header.parameterCode →
    EvaluationSize prefixSize actual
      (store.set frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)))
      (header.parameterCode.rename ξ) value bodyStore → prefixSize < budget →
    finalStore = bodyStore.set frameLocation
      (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current) →
  ∀ entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations owner.key.capturePrefix functions registry header arguments heap
    (store.set frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
    administrative actualContext actual ξ frameLocation (.state index) (.named origin),
  ∀ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩,
    Relates caller reached → condition entry →
    Below budget (NativeBodyAtWithExtra post extra (faults := faults) entry reached)


end Continuations

/-- The original strictly smaller Source body child consumes the real parameter
pool. Returning restores the saved caller in that body's actual reached pool. -/
theorem invocation_preserves_bounded_at_with_extra
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (condition : BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation condition)
    (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (_member : header ∈ headers)
    (capture : Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix (caller.rows owner.position).authority.frameLocation header mapping world heap store)
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    (post : NamedInvocationFaultPostContracts.BodyFaultPost)
    (extra : NamedInvocationFaultPostContracts.BodyExtra (headers := headers) (keys := keys)
      (functions := functions) (registry := registry) (header := header))
    (bodyMeaning : SourceContinuationWithExtra (post := post) (extra := extra) (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) owner caller condition budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome program size header.sourceBody header.function.evidence heap arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
        (header.code.rename capture.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      NamedInvocationFaultPostContracts.ReturnedAtWithExtra (header := header) (functions := functions)
        (registry := registry) post extra size (none) owner caller arguments outcome after value finalMap finalWorld finalStore := by
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  change authority.frameLocation = keys[owner.position.val].frameLocation at physical
  let liveCapture : Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix authority.frameLocation
      header mapping world heap store := capture
  have arity : header.function.parameters.length = arguments.length := by
    rw [header.parameters, List.length_map]; exact represented.length.1
  obtain ⟨child, environment, bound, allocated, bodyTrace, smaller⟩ :=
    RecursiveNamedCallBounds.body_trace header.frame header.extended arity trace
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ :=
    CallableIndexedFormation.namedBody_history compiled.indexed.ancestry header.hook
  let installed := CallableIndexedOwnedFunctionState.install caller owner.position (.stable history)
  let installedAuthority := authority.install (.stable history)
  have written : store.write? authority.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)) =
      some (store.set authority.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp authority.frame.read).1, rfl⟩
  let nextCapture : Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix authority.frameLocation header mapping world heap
      (store.set authority.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) :=
    { liveCapture with read := (Store.write?_preserves_other written liveCapture.distinct).trans liveCapture.read }
  have installedHeaps := (CallableIndexedBodyFrames.install header.registered heaps authority.unmapped authority.typed
    authority.frame (.stable history)).1
  have layout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) liveCapture.embedding.lift))
      (DataPatternValues.packValues payloads :: liveCapture.canonical)
      (.unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: liveCapture.captured) :=
    GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift liveCapture.layout (DataPatternValues.packValues payloads))
        (encode compiled.indexed.ancestry.layout.frame authority.current)) .unit
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues payloads)
      header.named.signature.parameterType (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
    header.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons
    (RuntimeValueHasType.unit (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions))
    (.cons (encode_runtime_typed world header.registered authority.current) (.cons packTyped liveCapture.typed))
  let producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys)
      header.layouts compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
    sameLayouts.symm ▸ CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary authority.frameLocation (.state index) := by
    exact readyAt_cast sameLayouts _ (CallableIndexedOwnedAllocationProducer.readyAt_of_owner_eq
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) owner.position physical.symm history)
  let parameterInitial : State headers keys
      ⟨[], mapping, world, heap, store.set authority.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)), liveCapture.canonical⟩ :=
    Eq.mp (congrArg (fun location => State headers keys
      ⟨[], mapping, world, heap, store.set location (encode compiled.indexed.ancestry.layout.frame (.state index)), liveCapture.canonical⟩)
      physical.symm) installed
  obtain ⟨entry, parameterTransition, agreement⟩ := parameters_with_state installedAuthority
    nextCapture.environments nextCapture.locals nextCapture.reference nextCapture.coherent represented installedHeaps
    layout actualTyped producer parameterInitial readyAt
  obtain ⟨parameterState, parameterRelated⟩ := parameterTransition
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  have installedRelated : Relates caller parameterInitial := by
    exact related_cast_frame caller physical.symm installed
      (CallableIndexedOwnedFunctionState.install_related caller owner.position (.stable history))
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyTransition, bodyPost⟩ :=
    bodyMeaning physical owned history emitted entry agreement parameterState
      (installedRelated.trans parameterRelated) (authorized physical owned history emitted entry)
      child (Nat.lt_of_lt_of_le smaller within) bodyTrace
  obtain ⟨bodyState, bodyRelated, bodyExtra⟩ := bodyTransition
  have prefixEvaluation := agreement.wrap bodyEvaluation
  rw [rename_prefix] at prefixEvaluation
  have reference : (DataPatternValues.packValues payloads :: liveCapture.captured)[liveCapture.embedding.lift
      (compiled.indexed.base.globals.length + 1)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type authority.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using liveCapture.capturedReference
  have evaluation := CallableContextFrames.withFrame_evaluates (.var reference) authority.frame.read
    (next_evaluates index (DataPatternValues.packValues payloads :: liveCapture.captured) store
      (encode compiled.indexed.ancestry.layout.frame authority.current)) prefixEvaluation
  have renamed : header.code.rename liveCapture.embedding.lift = withFrame
      (.var (liveCapture.embedding.lift (compiled.indexed.base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index))
      (header.parameterCode.rename liveCapture.embedding.lift) := by
    rw [emitted, NamedCalls.withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have frame := entry.frame.trans bodyFrame
  have sourceMetadata := entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := installedRelated.trans (parameterRelated.trans bodyRelated)
  obtain ⟨restoredHeaps, restoredFrame, restoredCell, restoredBodyRelated, restoredCallerRelated, restoredRecords, returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position header.registered finalHeaps worlds
      (by simpa only [physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using frame) related
  refine ⟨value, _, finalMap, finalWorld, ?_, result, restoredHeaps,
    maps, worlds, restoredFrame, sourceMetadata, returned, ?_⟩
  simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical, authority, liveCapture] using
    (renamed.symm ▸ evaluation)
  refine ⟨origin, index, metadata, _, _, _, _, entry, parameterState, child, bodyStore, bodyState,
    owned, history, emitted, installedRelated.trans parameterRelated, bodyRelated, bodyTrace,
    smaller, bodyEvaluation, bodyPost, agreement, related, rfl, restoredCell,
    restoredBodyRelated, restoredCallerRelated, restoredRecords, bodyExtra, restoredFrame⟩

/-- Retain the legacy post-only interface through the same actual body witness. -/
theorem invocation_preserves_bounded_at_with_post
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (condition : BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation condition)
    (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (_member : header ∈ headers)
    (capture : Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix (caller.rows owner.position).authority.frameLocation header mapping world heap store)
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    (post : NamedInvocationFaultPostContracts.BodyFaultPost)
    (bodyMeaning : SourceContinuationWithPost (post := post) (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) owner caller condition budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome program size header.sourceBody header.function.evidence heap arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
        (header.code.rename capture.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      NamedInvocationFaultPostContracts.ReturnedAt (header := header) (functions := functions)
        (registry := registry) post size (none) owner caller arguments outcome after value finalMap finalWorld finalStore := by
  have strongMeaning : SourceContinuationWithExtra
      (post := post) (extra := NamedInvocationFaultPostContracts.TrivialExtra)
      (functions := functions) (registry := registry) (faults := faults) (header := header)
      (arguments := arguments) owner caller condition budget := by
    intro origin index metadata administrative actualContext actual ξ frameLocation
      physical owned history emitted entry agreement reached related allowed child strict outcome after trace
    obtain ⟨value, bodyStore, finalMap, finalWorld, evaluation, result, finalHeaps,
      maps, worlds, frame, metadata, transition, bodyPost⟩ :=
      bodyMeaning physical owned history emitted entry agreement reached related allowed child strict trace
    obtain ⟨bodyState, bodyRelated⟩ := transition
    exact ⟨value, bodyStore, finalMap, finalWorld, evaluation, result, finalHeaps,
      maps, worlds, frame, metadata, ⟨bodyState, bodyRelated, trivial⟩, bodyPost⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluation, result, finalHeaps,
    maps, worlds, frame, metadata, returned, receipt⟩ :=
    invocation_preserves_bounded_at_with_extra (faults := faults) owner sameLayouts condition authorized budget caller
      _member capture represented heaps post NamedInvocationFaultPostContracts.TrivialExtra strongMeaning trace within
  exact ⟨value, finalStore, finalMap, finalWorld, evaluation, result, finalHeaps,
    maps, worlds, frame, metadata, returned, NamedInvocationFaultPostContracts.ReturnedAtWithExtra.forget receipt⟩

theorem invocation_preserves_bounded_at
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (condition : BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation condition)
    (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (_member : header ∈ headers)
    (capture : Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix (caller.rows owner.position).authority.frameLocation header mapping world heap store)
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    (bodyMeaning : SourceContinuation (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) owner caller condition budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome program size header.sourceBody header.function.evidence heap arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
        (header.code.rename capture.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have strongMeaning : SourceContinuationWithPost (post := NamedInvocationFaultPostContracts.Trivial)
      (functions := functions) (registry := registry) (faults := faults) (header := header)
      (arguments := arguments) owner caller condition budget := by
    intro origin index metadata administrative actualContext actual ξ frameLocation
      physical owned history emitted entry agreement reached related allowed child strict outcome after trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluation, result, finalHeaps,
      maps, worlds, frame, metadata, returned⟩ :=
      bodyMeaning physical owned history emitted entry agreement reached related allowed child strict trace
    exact ⟨value, finalStore, finalMap, finalWorld, evaluation, result, finalHeaps,
      maps, worlds, frame, metadata, returned, NamedInvocationFaultPostContracts.trivial_of_result result⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluation, result, finalHeaps, maps, worlds, frame, metadata, returned, _post⟩ :=
    invocation_preserves_bounded_at_with_post (faults := faults) owner sameLayouts condition authorized budget caller _member capture represented heaps
      NamedInvocationFaultPostContracts.Trivial strongMeaning trace within
  exact ⟨value, finalStore, finalMap, finalWorld, evaluation, result, finalHeaps,
    maps, worlds, frame, metadata, returned⟩

theorem invocation_preserves_bounded_with
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (condition : BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation condition)
    (budget : Nat)
    (bodyMeaning : Below budget (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) condition))
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (_member : header ∈ headers)
    (capture : Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix (caller.rows owner.position).authority.frameLocation header mapping world heap store)
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome program size header.sourceBody header.function.evidence heap arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
        (header.code.rename capture.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  apply invocation_preserves_bounded_at owner sameLayouts condition authorized budget caller _member capture represented heaps
  · intro origin index metadata administrative actualContext actual ξ frameLocation physical owned history emitted entry
      _agreement reached _related allowed child strict outcome after trace
    exact bodyMeaning child strict entry reached allowed trace
  · exact trace
  · exact within

private theorem body_of_trace_sized {header : CallableIndexedOwnedFunctionValues.Header compiled program} {size : Nat} {arguments : List Dynamic.Value}
    {environment : Dynamic.Environment} {before bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.BodyTrace program size header.function header.context environment bound outcome after) :
    RecursiveNamedCallBounds.BodyOutcome program (SourceExecutionSize.stepSize [size]) header.sourceBody
      header.function.evidence before arguments outcome after := by
  have extension : MonoBindersExtend header.sourceBody.source.owner header.sourceBody.context header.sourceBody.source.inputs header.types header.context := by
    simpa only [header.frame.source, header.frame.context, header.frame.parameters] using header.extended
  have allocation := header.frame.parameters ▸ allocated
  cases trace with
  | returned executed => exact .value (.returned header.frame.covers header.frame.roots extension allocation (header.frame.source ▸ executed) rfl)
  | unit same executed => exact .value (.unit header.frame.covers (header.frame.result ▸ same) header.frame.roots extension allocation
      (header.frame.source ▸ executed) ⟨_, rfl⟩)
  | fault failed => exact .fault (.statements header.frame.roots extension allocation (header.frame.source ▸ failed))
  | escaped executed escape => exact .fault (.controlEscape header.frame.roots extension allocation (header.frame.source ▸ executed) escape)

theorem invocation_reflects_bounded_at_with_extra
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (condition : BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation condition)
    (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (_member : header ∈ headers)
    (capture : Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix (caller.rows owner.position).authority.frameLocation header mapping world heap store)
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    (post : NamedInvocationFaultPostContracts.BodyFaultPost)
    (extra : NamedInvocationFaultPostContracts.BodyExtra (headers := headers) (keys := keys)
      (functions := functions) (registry := registry) (header := header))
    (bodyMeaning : NativeContinuationWithExtra (post := post) (extra := extra) (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) owner caller condition budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome program sourceSize header.sourceBody header.function.evidence heap arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      NamedInvocationFaultPostContracts.ReturnedAtWithExtra (header := header) (functions := functions)
        (registry := registry) post extra sourceSize (some size) owner caller arguments outcome after value finalMap finalWorld finalStore := by
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  change authority.frameLocation = keys[owner.position.val].frameLocation at physical
  let liveCapture : Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix authority.frameLocation
      header mapping world heap store := capture
  obtain ⟨origin, index, owned, selected, emitted⟩ :=
    CallableIndexedFormation.namedBody_receipt compiled.indexed.ancestry header.hook
  obtain ⟨metadata, history⟩ : ∃ metadata,
      Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table (.state index) (.named origin) (some metadata) := by
    cases found : compiled.indexed.ancestry.graph.table.namedAt? origin with
    | none => simp [SourceCoreCallableIndexedDispatch.namedFrame, found] at selected
    | some position =>
      obtain ⟨metadata, history⟩ := named_history compiled.indexed.ancestry.graph found
      exact ⟨metadata, selected ▸ history⟩
  have reference : (DataPatternValues.packValues payloads :: liveCapture.captured)[liveCapture.embedding.lift
      (compiled.indexed.base.globals.length + 1)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type authority.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using liveCapture.capturedReference
  obtain ⟨actualOrigin, actualIndex, prefixSize, bodyStore, actualOwned, actualSelected, prefixCompleted, prefixSmaller, restored⟩ :=
    RecursiveNamedCallBounds.named_hook_body compiled.indexed.ancestry header.hook reference authority.frame.read completed
  have sameOrigin : actualOrigin = origin := Option.some.inj (actualOwned.symm.trans owned)
  subst actualOrigin
  have sameIndex : actualIndex = index := by
    have same := actualSelected.symm.trans selected
    injection same
  subst actualIndex
  rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at prefixCompleted
  let installed := CallableIndexedOwnedFunctionState.install caller owner.position (.stable history)
  let installedAuthority := authority.install (.stable history)
  have written : store.write? authority.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)) =
      some (store.set authority.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp authority.frame.read).1, rfl⟩
  let nextCapture : Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix authority.frameLocation header mapping world heap
      (store.set authority.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) :=
    { liveCapture with read := (Store.write?_preserves_other written liveCapture.distinct).trans liveCapture.read }
  have installedHeaps := (CallableIndexedBodyFrames.install header.registered heaps authority.unmapped authority.typed
    authority.frame (.stable history)).1
  have layout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) liveCapture.embedding.lift))
      (DataPatternValues.packValues payloads :: liveCapture.canonical)
      (.unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: liveCapture.captured) :=
    GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift liveCapture.layout (DataPatternValues.packValues payloads))
        (encode compiled.indexed.ancestry.layout.frame authority.current)) .unit
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues payloads)
      header.named.signature.parameterType (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
    header.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons
    (RuntimeValueHasType.unit (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions))
    (.cons (encode_runtime_typed world header.registered authority.current) (.cons packTyped liveCapture.typed))
  let producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys)
      header.layouts compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
    sameLayouts.symm ▸ CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary authority.frameLocation (.state index) := by
    exact readyAt_cast sameLayouts _ (CallableIndexedOwnedAllocationProducer.readyAt_of_owner_eq
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) owner.position physical.symm history)
  let parameterInitial : State headers keys
      ⟨[], mapping, world, heap, store.set authority.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)), liveCapture.canonical⟩ :=
    Eq.mp (congrArg (fun location => State headers keys
      ⟨[], mapping, world, heap, store.set location (encode compiled.indexed.ancestry.layout.frame (.state index)), liveCapture.canonical⟩)
      physical.symm) installed
  obtain ⟨entry, child, bodyCompleted, childLe, _childStrict, parameterTransition⟩ :=
    parameters_sized_with_state installedAuthority _member nextCapture represented installedHeaps
      layout actualTyped prefixCompleted producer parameterInitial readyAt
  obtain ⟨parameterState, parameterRelated⟩ := parameterTransition
  have installedRelated : Relates caller parameterInitial := by
    exact related_cast_frame caller physical.symm installed
      (CallableIndexedOwnedFunctionState.install_related caller owner.position (.stable history))
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyTransition, bodyPost⟩ :=
    bodyMeaning physical owned history emitted prefixCompleted (Nat.lt_of_lt_of_le prefixSmaller within)
      restored entry parameterState (installedRelated.trans parameterRelated)
      (authorized physical owned history emitted entry)
      child (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt childLe prefixSmaller) within) bodyCompleted
  obtain ⟨bodyState, bodyRelated, bodyExtra⟩ := bodyTransition
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have frame := entry.frame.trans bodyFrame
  have sourceMetadata := entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := installedRelated.trans (parameterRelated.trans bodyRelated)
  obtain ⟨restoredHeaps, restoredFrame, restoredCell, restoredBodyRelated, restoredCallerRelated, restoredRecords, returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position header.registered finalHeaps worlds
      (by simpa only [physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using frame) related
  subst finalStore
  refine ⟨_, outcome, after, finalMap, finalWorld, body_of_trace_sized entry.allocation trace, result, ?_,
    maps, worlds, ?_, sourceMetadata, ?_, ?_⟩
  · simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical, authority] using restoredHeaps
  · simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical, authority] using restoredFrame
  · simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical, authority] using returned
  · refine ⟨origin, index, metadata, _, _, _, _, entry, parameterState, sourceSize, bodyStore, bodyState,
      owned, history, emitted, installedRelated.trans parameterRelated, bodyRelated, trace,
      SourceExecutionSize.child_lt_stepSize (by simp), bodyCompleted.sound, bodyPost,
      ⟨prefixSize, child, prefixCompleted, bodyCompleted, childLe, prefixSmaller⟩, related, ?_, ?_,
      restoredBodyRelated, restoredCallerRelated, restoredRecords, bodyExtra, ?_⟩
    · simp only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical, authority]
    · simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical, authority] using restoredCell
    · simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical, authority] using restoredFrame

/-- Retain the legacy post-only interface through the same actual body witness. -/
theorem invocation_reflects_bounded_at_with_post
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (condition : BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation condition)
    (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (_member : header ∈ headers)
    (capture : Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix (caller.rows owner.position).authority.frameLocation header mapping world heap store)
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    (post : NamedInvocationFaultPostContracts.BodyFaultPost)
    (bodyMeaning : NativeContinuationWithPost (post := post) (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) owner caller condition budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome program sourceSize header.sourceBody header.function.evidence heap arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      NamedInvocationFaultPostContracts.ReturnedAt (header := header) (functions := functions)
        (registry := registry) post sourceSize (some size) owner caller arguments outcome after value finalMap finalWorld finalStore := by
  have strongMeaning : NativeContinuationWithExtra
      (post := post) (extra := NamedInvocationFaultPostContracts.TrivialExtra)
      (functions := functions) (registry := registry) (faults := faults) (header := header)
      (arguments := arguments) owner caller condition budget := by
    intro origin index metadata administrative actualContext actual ξ frameLocation prefixSize bodyStore value finalStore
      physical owned history emitted prefixCompleted prefixWithin restored entry reached related allowed child strict
      bodyValue bodyFinalStore bodyCompleted
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
      maps, worlds, frame, metadata, transition, bodyPost⟩ :=
      bodyMeaning physical owned history emitted prefixCompleted prefixWithin restored entry reached related allowed child strict bodyCompleted
    obtain ⟨bodyState, bodyRelated⟩ := transition
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
      maps, worlds, frame, metadata, ⟨bodyState, bodyRelated, trivial⟩, bodyPost⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
    maps, worlds, frame, metadata, returned, receipt⟩ :=
    invocation_reflects_bounded_at_with_extra (faults := faults) owner sameLayouts condition authorized budget caller
      _member capture represented heaps post NamedInvocationFaultPostContracts.TrivialExtra strongMeaning completed within
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
    maps, worlds, frame, metadata, returned, NamedInvocationFaultPostContracts.ReturnedAtWithExtra.forget receipt⟩

theorem invocation_reflects_bounded_at
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (condition : BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation condition)
    (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (_member : header ∈ headers)
    (capture : Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix (caller.rows owner.position).authority.frameLocation header mapping world heap store)
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    (bodyMeaning : NativeContinuation (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) owner caller condition budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome program sourceSize header.sourceBody header.function.evidence heap arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have strongMeaning : NativeContinuationWithPost (post := NamedInvocationFaultPostContracts.Trivial)
      (functions := functions) (registry := registry) (faults := faults) (header := header)
      (arguments := arguments) owner caller condition budget := by
    intro origin index metadata administrative actualContext actual ξ frameLocation prefixSize bodyStore value finalStore
      physical owned history emitted prefixCompleted prefixWithin restored entry reached related allowed child strict
      bodyValue bodyFinalStore bodyCompleted
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
      maps, worlds, frame, metadata, returned⟩ :=
      bodyMeaning physical owned history emitted prefixCompleted prefixWithin restored entry reached related allowed child strict bodyCompleted
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
      maps, worlds, frame, metadata, returned, NamedInvocationFaultPostContracts.trivial_of_result result⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata, returned, _post⟩ :=
    invocation_reflects_bounded_at_with_post (faults := faults) owner sameLayouts condition authorized budget caller _member capture represented heaps
      NamedInvocationFaultPostContracts.Trivial strongMeaning completed within
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
    maps, worlds, frame, metadata, returned⟩

theorem invocation_reflects_bounded_with
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (condition : BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation condition)
    (budget : Nat)
    (bodyMeaning : Below budget (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) condition))
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (_member : header ∈ headers)
    (capture : Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix (caller.rows owner.position).authority.frameLocation header mapping world heap store)
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome program sourceSize header.sourceBody header.function.evidence heap arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  apply invocation_reflects_bounded_at owner sameLayouts condition authorized budget caller _member capture represented heaps
  · intro origin index metadata administrative actualContext actual ξ frameLocation prefixSize bodyStore value finalStore
      physical owned history emitted _prefix _prefixWithin _restored entry reached _related allowed child strict
      bodyValue bodyFinalStore bodyCompleted
    exact bodyMeaning child strict entry reached allowed bodyCompleted
  · exact completed
  · exact within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedInvocationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedCallBodyFaultPostContracts
/-! A named call retains its actual argument route and selected body receipt.
The body post stays at the body store; returning a caller wrapper retains the
same physically restored pool. Source and native grades remain independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedCallBodyFaultPostContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open NamedInvocationFaultPostContracts
universe u

/-- Only measured native callers supply a strict native child grade. -/
def CompletionBelow (parent : Option Nat) (actual : Environment) (before : Store)
    (expression : Expr) (value : Value) (after : Store) : Prop :=
  match parent with
  | none => True
  | some size => ∃ child, EvaluationSize child actual before expression value after ∧ child < size

/-- The exact body receipt uses the actual invocation grade on native reflection. -/
def InvocationBelow (parent child : Option Nat) : Prop :=
  match parent, child with
  | none, none => True
  | some parent, some child => child < parent
  | _, _ => False

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
  {codes : List SourceCoreBasic.LoweredExpr} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical actual : Environment} {ξ : Renaming}
  {slots : ProtectedStateTransition.Index → Prop}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}

/-- Each constructor comes from one actual branch of the original call core.
The successful route retains its live capture, exact child receipt, and the
literal equality between the outer returned wrapper and invocation pool. -/
inductive CallRouteAt (post : BodyFaultPost)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) slots callerProtocol)
    (caller : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sourceParent : Nat) (nativeParent : Option Nat) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Value → LocationMap → StoreTyping → Store → Prop where
  | argumentFailure {child reason token after finalMap finalWorld finalStore}
      (failed : SourceExecutionSize.ExpressionsFault program child context evidence source environment before ids reason after)
      (smaller : child < sourceParent)
      (evaluation : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore)
      (measured : CompletionBelow nativeParent actual store
        ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates caller reached) :
      CallRouteAt post owner bridge caller sourceParent nativeParent (.fault reason) after
        (.inLeft header.output (.word token)) finalMap finalWorld finalStore
  | bodyApplied {argumentsSize callSize bodySourceSize arguments payloads middle middleMap middleWorld middleStore
      outcome after value finalMap finalWorld finalStore}
      (evaluated : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment before ids arguments middle)
      (argumentsSmaller : argumentsSize < sourceParent)
      (called : RecursiveNamedCallBounds.CallOutcome program callSize context evidence header.function.evidence middle
        (.global ⟨header.instantiation, header.function.evidence⟩) arguments outcome after)
      (callSmaller : callSize < sourceParent)
      (argumentEvaluation : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (DataPatternValues.packValues payloads)) middleStore)
      (argumentMeasured : CompletionBelow nativeParent actual store
        ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (DataPatternValues.packValues payloads)) middleStore)
      (argumentState : callerProtocol.State ⟨scope, middleMap, middleWorld, middle, middleStore, canonical⟩)
      (argumentRelated : callerProtocol.Relates caller argumentState)
      (argumentMaps : LocationMap.Extends mapping middleMap)
      (argumentWorlds : WorldExtends world middleWorld)
      (argumentFrame : AdministrativePreserved mapping store middleMap middleStore)
      (argumentMetadata : Dynamic.HeapMetadataExtend before middle)
      (capture : Capture (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers owner.key.locations owner.key.capturePrefix ((bridge.pool argumentState).rows owner.position).authority.frameLocation
        header middleMap middleWorld middle middleStore)
      (represented : CallableIndexedParameterMeaning.Arguments
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        middleMap middleWorld header.bindings arguments payloads)
      (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions middleMap middleWorld middle middleStore)
      (bodyTrace : RecursiveNamedCallBounds.BodyOutcome program bodySourceSize header.sourceBody header.function.evidence middle arguments outcome after)
      (bodySmaller : bodySourceSize < callSize)
      (bodyEvaluation : Evaluates (DataPatternValues.packValues payloads :: capture.captured) middleStore
        (header.code.rename capture.embedding.lift) value finalStore)
      (bodyNative : Option Nat)
      (bodyMeasured : InvocationBelow nativeParent bodyNative)
      (receipt : ReturnedAt (header := header) (functions := functions) (registry := registry)
        post bodySourceSize bodyNative owner (bridge.pool argumentState) arguments outcome after value finalMap finalWorld finalStore)
      (finalState : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (bodyRelated : Relates (bridge.pool argumentState) finalState)
      (bodyMaps : LocationMap.Extends middleMap finalMap)
      (bodyWorlds : WorldExtends middleWorld finalWorld)
      (bodyFrame : AdministrativePreserved middleMap middleStore finalMap finalStore)
      (bodyMetadata : Dynamic.HeapMetadataExtend middle after)
      (returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (samePool : bridge.pool returned = finalState)
      (relatedCaller : callerProtocol.Relates caller returned) :
      CallRouteAt post owner bridge caller sourceParent nativeParent outcome after value finalMap finalWorld finalStore

section Legacy
variable {faults : FunctionCalls.FaultRep} {arguments : List Dynamic.Value}
  {owner : CallableIndexedOwnedFunctionValues.OwnedKey keys}
  {caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩}
  {condition : BodyCondition (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header}
  {budget : Nat}

/-- A legacy child supplies only the trivial sidecar on its same actual result. -/
theorem source_trivial
    (meaning : CallableIndexedOwnedInvocationBounds.SourceContinuation (functions := functions) (registry := registry)
      (faults := faults) (header := header) (arguments := arguments) owner caller condition budget) :
    CallableIndexedOwnedInvocationBounds.SourceContinuationWithPost (post := Trivial)
      (functions := functions) (registry := registry) (faults := faults) (header := header)
      (arguments := arguments) owner caller condition budget := by
  intro origin index metadata administrative actualContext actual ξ frameLocation
    physical owned history emitted entry agreement reached related allowed child strict outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluation, result, finalHeaps,
    maps, worlds, frame, metadata, returned⟩ :=
    meaning physical owned history emitted entry agreement reached related allowed child strict trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluation, result, finalHeaps,
    maps, worlds, frame, metadata, returned, trivial_of_result result⟩

/-- The actual legacy reflected result receives no new fault attribution. -/
theorem native_trivial
    (meaning : CallableIndexedOwnedInvocationBounds.NativeContinuation (functions := functions) (registry := registry)
      (faults := faults) (header := header) (arguments := arguments) owner caller condition budget) :
    CallableIndexedOwnedInvocationBounds.NativeContinuationWithPost (post := Trivial)
      (functions := functions) (registry := registry) (faults := faults) (header := header)
      (arguments := arguments) owner caller condition budget := by
  intro origin index metadata administrative actualContext actual ξ frameLocation prefixSize bodyStore value finalStore
    physical owned history emitted prefixCompleted prefixWithin restored entry reached related allowed child strict
    bodyValue bodyFinalStore bodyCompleted
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
    maps, worlds, frame, metadata, returned⟩ :=
    meaning physical owned history emitted prefixCompleted prefixWithin restored entry reached related allowed child strict bodyCompleted
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
    maps, worlds, frame, metadata, returned, trivial_of_result result⟩
end Legacy

end Solcore.SourceSemantics.CoreLowering.NamedCallBodyFaultPostContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedExpressionBodyFaultPostContracts
/-! A selected ordinary/direct call keeps its original root Source trace and
the low call route at the same returned tuple. Reflection's two Source grades
remain separate. The body post stays at the receipt's actual body store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedExpressionBodyFaultPostContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open NamedInvocationFaultPostContracts NamedCallBodyFaultPostContracts
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {ξ : Renaming}
  {slots : ProtectedStateTransition.Index → Prop}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}

/-- The selected emission, root trace and low route describe one actual call.
The low call grade is retained independently from the reconstructed root grade. -/
def OuterCallRouteAt (post : BodyFaultPost)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) slots callerProtocol)
    (caller : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (callerPrefix : Nat) (reason : Word) (rootSize : Nat) (nativeSize : Option Nat)
    (id : ExpressionId) (root : ExpressionNode) (lowered : SourceCoreBasic.LoweredExpr)
    (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (value : Value)
    (finalMap : LocationMap) (finalWorld : StoreTyping) (finalStore : Store) : Prop :=
  ∃ header : CallableIndexedOwnedFunctionValues.Header compiled program,
    ∃ callee ids codes callSize,
      header ∈ headers ∧
      root.form = .call callee ids (.declaration header.instantiation) ∧
      root.type = header.function.resultType ∧ lowered.type = header.output ∧
      lowered.expression.rename ξ = SourceCoreCalls.call header.named.signature
        (ξ (scope.length + callerPrefix + header.slot))
        ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason ∧
      RecursiveNamedCallBounds.ExpressionOutcome program rootSize context evidence source environment before id outcome after ∧
      RecursiveNamedArgumentTraceBounds.TraceAt program context evidence header.function.evidence
        source environment before ids header.instantiation callSize outcome after ∧
      CallRouteAt (functions := functions) (registry := registry) (header := header)
        (source := source) (context := context) (evidence := evidence) (environment := environment)
        (ids := ids) (codes := codes) (actual := actual) (ξ := ξ)
        post owner bridge caller callSize nativeSize outcome after value finalMap finalWorld finalStore

/-- A fault token is obtained from that genuine route and its actual body/list
branch, preserving the emitted output type. -/
theorem fault_word {post : BodyFaultPost}
    {owner : CallableIndexedOwnedFunctionValues.OwnedKey keys}
    {bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) slots callerProtocol}
    {caller : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩}
    {callerPrefix rootSize : Nat} {reason : Word} {nativeSize : Option Nat}
    {id : ExpressionId} {root : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    {fault : Dynamic.SemanticFault} {after : Dynamic.Heap} {value : Value}
    {finalMap : LocationMap} {finalWorld : StoreTyping} {finalStore : Store}
    (route : OuterCallRouteAt (functions := functions) (registry := registry)
      (source := source) (context := context) (evidence := evidence) (environment := environment)
      (actual := actual) (ξ := ξ) post owner bridge caller callerPrefix reason rootSize nativeSize
      id root lowered (.fault fault) after value finalMap finalWorld finalStore) :
    ∃ token, value = .inLeft lowered.type (.word token) := by
  obtain ⟨header, callee, ids, codes, callSize, member, form, sourceType, output,
    emitted, sourceTrace, trace, retained⟩ := route
  cases retained with
  | argumentFailure failed smaller evaluation measured reached related =>
    exact ⟨_, by rw [output]⟩
  | bodyApplied evaluated argumentsSmaller called callSmaller argumentEvaluation argumentMeasured
      argumentState argumentRelated argumentMaps argumentWorlds argumentFrame argumentMetadata
      capture represented heaps bodyTrace bodySmaller bodyEvaluation bodyNative bodyMeasured receipt
      finalState bodyRelated bodyMaps bodyWorlds bodyFrame bodyMetadata returned samePool relatedCaller =>
    obtain ⟨origin, index, metadata, administrative, actualContext, actual, embedding, entry,
      parameterState, bodySize, bodyStore, bodyState, selected, history, bodyEmitted, parameterRelated,
      bodyRelated, trace, strict, completed, post, rest⟩ := receipt
    obtain ⟨token, same, bodyPost⟩ := post
    exact ⟨token, by simpa only [output] using same⟩

end Solcore.SourceSemantics.CoreLowering.NamedExpressionBodyFaultPostContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedValueInvocationBounds
/-! Named function values apply their complete retained closure directly. The
same reached owner pool supplies live Source locals; a read of a global slot is
not part of this application. Original frame installation, measured parameter
allocation and caller restoration are retained. Strict body continuations remain
explicit, and are supplied by the direct typed Header profile. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedValueInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedInvocationBounds
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
private theorem insert_at_suffix (added suffix : Environment) (value : Value) :
    Environment.insertAt (added ++ suffix) added.length value = added ++ value :: suffix := by
  induction added with
  | nil => simp [Environment.insertAt]
  | cons head tail ih => simpa [Environment.insertAt] using congrArg (List.cons head) ih

private theorem insert_administrative {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    {value : Value} {type : Ty} (typed : RuntimeValueHasType world value type (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions) :
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked.catalog) mapping world
      (type :: administrative) scope environment (Environment.insertAt canonical scope.length value) (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions := by
  induction related with
  | nil suffixTyped => exact .nil (by simpa [Environment.insertAt] using RuntimeEnvironmentHasTypes.cons typed suffixTyped)
  | cons reference _ ih => exact .cons reference ih
  | internal reference absent _ ih => exact .internal reference absent ih

private theorem parameters_sized_with_state (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (authority : Authority (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers owner.key.locations owner.key.capturePrefix mapping world heap store)
    {header : Header (compiled.indexed.ancestry) (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions program} (_member : header ∈ headers)
    (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
    (locals : Dynamic.EnvironmentAgrees heap header.function.context.locals [])
    (reference : capture.canonical[header.globals]? = some (.cellRef compiled.indexed.ancestry.layout.frame.type authority.frameLocation))
    {functions : FunctionModel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)} {registry : SourceCoreRawMetadata.Registry}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked registry functions mapping world heap store)
    {actual actualContext ξ}
    (agrees : EnvironmentsAgree ξ (DataPatternValues.packValues payloads :: capture.canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    {size : Nat} {result : Value} {afterStore : Store}
    (completed : EvaluationSize size actual store (header.parameterCode.rename ξ) result afterStore)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys)
      header.layouts (compiled.indexed.ancestry).layout.frame (CompatibleAmbientHeap.payloadModel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked registry functions))
    (initial : State headers keys ⟨[], mapping, world, heap, store, capture.canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary authority.frameLocation authority.current) :
    ∃ entry : BodyState headers owner.key.locations owner.key.capturePrefix functions registry header arguments heap store mapping world
      capture.administrative actualContext actual ξ authority.frameLocation authority.current authority.ghost,
      ∃ child, EvaluationSize child entry.actualBody entry.store (header.body.rename entry.embedding) result afterStore ∧
        child ≤ size ∧ (header.bindings ≠ [] → child < size) ∧
        ProtectedStateTransition.Transition (protocol headers keys) initial
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := by
  have tree := CallableIndexedParameterCertificates.of_accepted header.onError header.acceptedPrefix
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) capture.canonical
      (DataPatternValues.packValues payloads :: capture.canonical) := by
    intro index value found; exact found
  have length : (header.bindings.map Prod.snd).length = payloads.length := by simpa using represented.length.2
  obtain ⟨environment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding, child,
    allocated, finalEnvironments, finalHeaps, maps, worlds, preservation, _, lookups, spine, finalTyped, bodyCompletion, childLe, childStrict, reached, related⟩ :=
    RecursiveNamedCallBounds.Stateful.parameter_prefix tree (protocol headers keys) producer header.definitions_eq header.registered represented capture.environments heaps
      sourceLayout agrees actualTyped (allTypes := header.bindings.map Prod.snd) (named := true) rfl (by simp) length
      (fun {_ _} found => by simpa using found) (CallableIndexedParameters.inputKinds header.inputs)
      (by simpa using reference) authority.frame.read authority.unmapped initial readyAt completed
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have bundleTyped := (CallableIndexedParameters.Arguments.pack_typed represented).weaken worlds
  have finalWithBundle := insert_administrative finalEnvironments bundleTyped
  have scopeLength : (header.bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) []).length = header.bindings.length := by simp
  have exactEnvironment : Environment.insertAt finalCanonical header.bindings.length
      (DataPatternValues.packValues payloads) = finalLogical := by
    rw [canonicalEq, ← prefixLength, insert_at_suffix, logicalEq]
  rw [scopeLength, exactEnvironment, CallableIndexedParameters.scope_eq] at finalWithBundle
  rw [← header.parameters] at allocated
  have metadata := GenericLexicalContext.binders_metadata allocated
  let catalog : Entry (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers owner.key.locations owner.key.capturePrefix (owner.key.capturePrefix + 1)
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld finalHeap finalStore finalLogical := by
    refine ⟨authority.extend maps worlds preservation metadata, ?_⟩
    intro target targetMember
    rw [logicalEq]
    simp only [List.length_map, List.length_reverse]
    have index : header.bindings.length + (owner.key.capturePrefix + 1) + target.slot =
        added.length + (owner.key.capturePrefix + target.slot + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using capture.coherent target targetMember
  have finalReference : finalLogical[header.bindings.length + 1 + header.globals]? =
      some (.cellRef (compiled.indexed.ancestry).layout.frame.type authority.frameLocation) := by
    rw [logicalEq]
    have index : header.bindings.length + 1 + header.globals = added.length + (header.globals + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using reference
  have current := CallableIndexedBodyFrames.body_current authority.unmapped authority.frame preservation
  have mono := FunctionCallBody.mono_binders header.extended
  refine ⟨BodyState.of_receipts environment  finalHeap  finalLogical  finalActual  finalStore  finalMap  finalWorld  embedding
    allocated (by simpa only [List.append_nil, CallableIndexedAmbient.ambientDefinitions] using finalWithBundle) finalHeaps
    (GenericLexicalContext.binders_agree mono.1 mono.2 locals allocated)
    maps  worlds  preservation  metadata  lookups  finalTyped  catalog  finalReference  current  (by rfl)  (by rfl)  (by
      change (authority.extend maps worlds preservation metadata).ghost = authority.ghost
      rfl), child, bodyCompletion, childLe, childStrict, reached, related⟩

private theorem rename_prefix (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

private theorem next_evaluates (index : Int) (actual : Environment) (store : Store) (saved : Value) :
    Evaluates (saved :: actual) store
      ((SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)).weakenAt 0)
      (encode compiled.indexed.ancestry.layout.frame (.state index)) store := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

private theorem related_cast_frame
    {initial : ProtectedStateTransition.Index} (saved : State headers keys initial)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {first second : Location} {next : Value} (same : first = second)
    (state : State headers keys ⟨scope, mapping, world, heap, store.set first next, canonical⟩)
    (related : Relates saved state) :
    Relates saved (Eq.mp (congrArg (fun location => State headers keys
      ⟨scope, mapping, world, heap, store.set location next, canonical⟩) same) state) := by
  cases same
  exact related

private theorem readyAt_cast
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {first second : SourceCoreAllocationLayouts.Prepared}
    {frame : SourceCoreCallableIndexedFrames.Layout}
    (same : first = second)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys) second frame model)
    {location : Location} {native : NativeFrame}
    (ready : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      ((same.symm ▸ producer).toOrdinary) location native := by
  cases same
  exact ready

private theorem body_of_trace_sized {header : CallableIndexedOwnedFunctionValues.Header compiled program} {size : Nat} {arguments : List Dynamic.Value}
    {environment : Dynamic.Environment} {before bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.BodyTrace program size header.function header.context environment bound outcome after) :
    RecursiveNamedCallBounds.BodyOutcome program (SourceExecutionSize.stepSize [size]) header.sourceBody
      header.function.evidence before arguments outcome after := by
  have extension : MonoBindersExtend header.sourceBody.source.owner header.sourceBody.context header.sourceBody.source.inputs header.types header.context := by
    simpa only [header.frame.source, header.frame.context, header.frame.parameters] using header.extended
  have allocation := header.frame.parameters ▸ allocated
  cases trace with
  | returned executed => exact .value (.returned header.frame.covers header.frame.roots extension allocation (header.frame.source ▸ executed) rfl)
  | unit same executed => exact .value (.unit header.frame.covers (header.frame.result ▸ same) header.frame.roots extension allocation
      (header.frame.source ▸ executed) ⟨_, rfl⟩)
  | fault failed => exact .fault (.statements header.frame.roots extension allocation (header.frame.source ▸ failed))
  | escaped executed escape => exact .fault (.controlEscape header.frame.roots extension allocation (header.frame.source ▸ executed) escape)

theorem invocation_preserves_bounded_at
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (condition : BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation condition)
    (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (_member : header ∈ headers)
    (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    (bodyMeaning : SourceContinuation (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) owner caller condition budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome program size header.sourceBody header.function.evidence heap arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
        (header.code.rename capture.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  change authority.frameLocation = keys[owner.position.val].frameLocation at physical
  let liveCapture := capture
  have liveLocals : Dynamic.EnvironmentAgrees heap header.function.context.locals [] := by
    obtain ⟨original⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool caller owner _member
    exact original.locals
  have liveReference : capture.canonical[header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type authority.frameLocation) := by
    simpa only [physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using capture.reference
  have arity : header.function.parameters.length = arguments.length := by
    rw [header.parameters, List.length_map]; exact represented.length.1
  obtain ⟨child, environment, bound, allocated, bodyTrace, smaller⟩ :=
    RecursiveNamedCallBounds.body_trace header.frame header.extended arity trace
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ :=
    CallableIndexedFormation.namedBody_history compiled.indexed.ancestry header.hook
  let installed := CallableIndexedOwnedFunctionState.install caller owner.position (.stable history)
  let installedAuthority := authority.install (.stable history)
  have installedHeaps := (CallableIndexedBodyFrames.install header.registered heaps authority.unmapped authority.typed
    authority.frame (.stable history)).1
  have layout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) liveCapture.embedding.lift))
      (DataPatternValues.packValues payloads :: liveCapture.canonical)
      (.unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: liveCapture.captured) :=
    GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift liveCapture.layout (DataPatternValues.packValues payloads))
        (encode compiled.indexed.ancestry.layout.frame authority.current)) .unit
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues payloads)
      header.named.signature.parameterType (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
    header.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons
    (RuntimeValueHasType.unit (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions))
    (.cons (encode_runtime_typed world header.registered authority.current) (.cons packTyped liveCapture.typed))
  let producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys)
      header.layouts compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
    sameLayouts.symm ▸ CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary authority.frameLocation (.state index) := by
    exact readyAt_cast sameLayouts _ (CallableIndexedOwnedAllocationProducer.readyAt_of_owner_eq
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) owner.position physical.symm history)
  let parameterInitial : State headers keys
      ⟨[], mapping, world, heap, store.set authority.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)), liveCapture.canonical⟩ :=
    Eq.mp (congrArg (fun location => State headers keys
      ⟨[], mapping, world, heap, store.set location (encode compiled.indexed.ancestry.layout.frame (.state index)), liveCapture.canonical⟩)
      physical.symm) installed
  obtain ⟨entry, parameterTransition, agreement⟩ := parameters_with_state installedAuthority
    liveCapture.environments liveLocals liveReference liveCapture.coherent represented installedHeaps
    layout actualTyped producer parameterInitial readyAt
  obtain ⟨parameterState, parameterRelated⟩ := parameterTransition
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  have installedRelated : Relates caller parameterInitial := by
    exact related_cast_frame caller physical.symm installed
      (CallableIndexedOwnedFunctionState.install_related caller owner.position (.stable history))
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyTransition⟩ :=
    bodyMeaning physical owned history emitted entry agreement parameterState
      (installedRelated.trans parameterRelated) (authorized physical owned history emitted entry)
      child (Nat.lt_of_lt_of_le smaller within) bodyTrace
  obtain ⟨bodyState, bodyRelated⟩ := bodyTransition
  have prefixEvaluation := agreement.wrap bodyEvaluation
  rw [rename_prefix] at prefixEvaluation
  have reference : (DataPatternValues.packValues payloads :: liveCapture.captured)[liveCapture.embedding.lift
      (compiled.indexed.base.globals.length + 1)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type authority.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ, physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using liveCapture.capturedReference
  have evaluation := CallableContextFrames.withFrame_evaluates (.var reference) authority.frame.read
    (next_evaluates index (DataPatternValues.packValues payloads :: liveCapture.captured) store
      (encode compiled.indexed.ancestry.layout.frame authority.current)) prefixEvaluation
  have renamed : header.code.rename liveCapture.embedding.lift = withFrame
      (.var (liveCapture.embedding.lift (compiled.indexed.base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index))
      (header.parameterCode.rename liveCapture.embedding.lift) := by
    rw [emitted, NamedCalls.withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have frame := entry.frame.trans bodyFrame
  have sourceMetadata := entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := installedRelated.trans (parameterRelated.trans bodyRelated)
  obtain ⟨restoredHeaps, restoredFrame, restoredCell, restoredBodyRelated, restoredCallerRelated, restoredRecords, returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position header.registered finalHeaps worlds
      (by simpa only [physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using frame) related
  refine ⟨value, _, finalMap, finalWorld, ?_, result, restoredHeaps,
    maps, worlds, restoredFrame, sourceMetadata, returned⟩
  simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical, authority, liveCapture] using
    (renamed.symm ▸ evaluation)


theorem invocation_reflects_bounded_at
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (condition : BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations)
      (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation condition)
    (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (_member : header ∈ headers)
    (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    (bodyMeaning : NativeContinuation (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) owner caller condition budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome program sourceSize header.sourceBody header.function.evidence heap arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  change authority.frameLocation = keys[owner.position.val].frameLocation at physical
  let liveCapture := capture
  have liveLocals : Dynamic.EnvironmentAgrees heap header.function.context.locals [] := by
    obtain ⟨original⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool caller owner _member
    exact original.locals
  have liveReference : capture.canonical[header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type authority.frameLocation) := by
    simpa only [physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using capture.reference
  obtain ⟨origin, index, owned, selected, emitted⟩ :=
    CallableIndexedFormation.namedBody_receipt compiled.indexed.ancestry header.hook
  obtain ⟨metadata, history⟩ : ∃ metadata,
      Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table (.state index) (.named origin) (some metadata) := by
    cases found : compiled.indexed.ancestry.graph.table.namedAt? origin with
    | none => simp [SourceCoreCallableIndexedDispatch.namedFrame, found] at selected
    | some position =>
      obtain ⟨metadata, history⟩ := named_history compiled.indexed.ancestry.graph found
      exact ⟨metadata, selected ▸ history⟩
  have reference : (DataPatternValues.packValues payloads :: liveCapture.captured)[liveCapture.embedding.lift
      (compiled.indexed.base.globals.length + 1)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type authority.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ, physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using liveCapture.capturedReference
  obtain ⟨actualOrigin, actualIndex, prefixSize, bodyStore, actualOwned, actualSelected, prefixCompleted, prefixSmaller, restored⟩ :=
    RecursiveNamedCallBounds.named_hook_body compiled.indexed.ancestry header.hook reference authority.frame.read completed
  have sameOrigin : actualOrigin = origin := Option.some.inj (actualOwned.symm.trans owned)
  subst actualOrigin
  have sameIndex : actualIndex = index := by
    have same := actualSelected.symm.trans selected
    injection same
  subst actualIndex
  rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at prefixCompleted
  let installed := CallableIndexedOwnedFunctionState.install caller owner.position (.stable history)
  let installedAuthority := authority.install (.stable history)
  have installedHeaps := (CallableIndexedBodyFrames.install header.registered heaps authority.unmapped authority.typed
    authority.frame (.stable history)).1
  have layout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) liveCapture.embedding.lift))
      (DataPatternValues.packValues payloads :: liveCapture.canonical)
      (.unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: liveCapture.captured) :=
    GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift liveCapture.layout (DataPatternValues.packValues payloads))
        (encode compiled.indexed.ancestry.layout.frame authority.current)) .unit
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues payloads)
      header.named.signature.parameterType (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
    header.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons
    (RuntimeValueHasType.unit (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions))
    (.cons (encode_runtime_typed world header.registered authority.current) (.cons packTyped liveCapture.typed))
  let producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys)
      header.layouts compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
    sameLayouts.symm ▸ CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary authority.frameLocation (.state index) := by
    exact readyAt_cast sameLayouts _ (CallableIndexedOwnedAllocationProducer.readyAt_of_owner_eq
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) owner.position physical.symm history)
  let parameterInitial : State headers keys
      ⟨[], mapping, world, heap, store.set authority.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)), liveCapture.canonical⟩ :=
    Eq.mp (congrArg (fun location => State headers keys
      ⟨[], mapping, world, heap, store.set location (encode compiled.indexed.ancestry.layout.frame (.state index)), liveCapture.canonical⟩)
      physical.symm) installed
  obtain ⟨entry, child, bodyCompleted, childLe, _childStrict, parameterTransition⟩ :=
    parameters_sized_with_state owner installedAuthority _member liveCapture liveLocals liveReference represented installedHeaps
      layout actualTyped prefixCompleted producer parameterInitial readyAt
  obtain ⟨parameterState, parameterRelated⟩ := parameterTransition
  have installedRelated : Relates caller parameterInitial := by
    exact related_cast_frame caller physical.symm installed
      (CallableIndexedOwnedFunctionState.install_related caller owner.position (.stable history))
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyTransition⟩ :=
    bodyMeaning physical owned history emitted prefixCompleted (Nat.lt_of_lt_of_le prefixSmaller within)
      restored entry parameterState (installedRelated.trans parameterRelated)
      (authorized physical owned history emitted entry)
      child (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt childLe prefixSmaller) within) bodyCompleted
  obtain ⟨bodyState, bodyRelated⟩ := bodyTransition
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have frame := entry.frame.trans bodyFrame
  have sourceMetadata := entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := installedRelated.trans (parameterRelated.trans bodyRelated)
  obtain ⟨restoredHeaps, restoredFrame, restoredCell, restoredBodyRelated, restoredCallerRelated, restoredRecords, returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position header.registered finalHeaps worlds
      (by simpa only [physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using frame) related
  subst finalStore
  refine ⟨_, outcome, after, finalMap, finalWorld, body_of_trace_sized entry.allocation trace, result, ?_,
    maps, worlds, ?_, sourceMetadata, ?_⟩
  · simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical, authority] using restoredHeaps
  · simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical, authority] using restoredFrame
  · simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical, authority] using returned

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedValueInvocationBounds
end
