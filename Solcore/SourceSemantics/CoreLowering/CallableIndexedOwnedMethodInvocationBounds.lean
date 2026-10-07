import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMarkedAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestoration
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyStaticOrigins

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
  have arity : (methodFunction generation sourceBody dictionary).parameters.length = arguments.length := by
    change sourceBody.source.inputs.length = arguments.length
    rw [profile.parameters, List.length_map]
    exact represented.length.1
  obtain ⟨child, environment, bound, allocated, bodyTrace, smaller⟩ :=
    RecursiveNamedCallBounds.body_trace_of_fields profile.sourceFrame.source profile.sourceFrame.context
      profile.sourceFrame.parameters profile.sourceFrame.result profile.sourceFrame.roots profile.extended arity trace
  obtain ⟨originId, index, metadata, _owned, history, emitted, entry, _added, _length, _spine, parameterState, parameterRelated⟩ :=
    parameters_with_state generation profile functions installed represented owner caller sameFrame heaps
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  let actualEntry := parameter_entry_origin generation profile functions escaped extend runtimeOf entry parameterState
    (CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position history)
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, _exit, bodyState, bodyRelated⟩ :=
    bodyMeaning child (Nat.lt_of_lt_of_le smaller within) actualEntry bodyTrace
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
  obtain ⟨originId, index, metadata, prefixSize, bodyStore, _owned, history, strict, restored,
    entry, _added, _length, _spine, parameterState, parameterRelated⟩ :=
    body_prefix_with_state generation profile functions installed represented owner caller sameFrame heaps completed
  let actualEntry := prefix_entry_origin generation profile functions escaped extend runtimeOf entry parameterState
    (CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position history)
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, bodyTrace, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, _exit, bodyState, bodyRelated⟩ :=
    bodyMeaning entry.childSize (Nat.lt_of_le_of_lt entry.bounded (Nat.lt_of_lt_of_le strict within)) actualEntry entry.completed
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

end Method

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodInvocationBounds
