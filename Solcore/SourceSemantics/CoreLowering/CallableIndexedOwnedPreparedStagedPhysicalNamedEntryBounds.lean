import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEntryBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalGlobals

/-! Native completion of an actual retained named Header selects the original
hook and marked parameter prefix. The literal captured environment, installed
history, reached owned pool, strict native body grade and physical caller
restoration equation are retained. No Source body trace or application meaning
is required or produced by this independent entry producer. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedEntryBounds
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
            entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ ∧
        ∃ added : Environment, added.length = header.bindings.length ∧
          entry.canonical = added ++ DataPatternValues.packValues payloads :: capture.canonical := by
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
      rfl), child, bodyCompletion, childLe, childStrict, ⟨reached, related⟩, added, prefixLength, logicalEq⟩

theorem parameters_with_state_spine {locations : Locations} {capturePrefix : Nat} (authority : Authority (prepared := compiled.indexed.ancestry)
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
        (header.body.rename entry.embedding) ∧
      ∃ added : Environment, added.length = header.bindings.length ∧
        entry.canonical = added ++ DataPatternValues.packValues payloads :: canonical := by
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
      rfl), ⟨reached, related⟩, agreement, added, prefixLength, logicalEq⟩

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


variable {functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (header : CallableIndexedOwnedFunctionValues.Header compiled program)
  (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
  (arguments : List Dynamic.Value) (payloads : List Value)

/-- All fields belong to one original completed named invocation, before its
body meaning is established. The saved caller cell is restored literally. -/
structure Prefix (size : Nat) (value : Value) (finalStore : Store)
    extends CallableIndexedOwnedPreparedStagedNamedEntryBounds.Prefix
      (functions := functions) (registry := registry) owner caller header capture arguments payloads size value finalStore where
  spine : ∃ added : Environment, added.length = header.bindings.length ∧
    entry.canonical = added ++ DataPatternValues.packValues payloads :: capture.canonical

variable {arguments payloads}
include owner caller header capture in
/-- The real retained closure completion exposes its authentic strict body
child through the original hook, install and marked allocation producers. -/
theorem native_prefix
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (member : header ∈ headers)
    (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    Nonempty (Prefix (functions := functions) (registry := registry) owner caller header capture arguments payloads
      size value finalStore) := by
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  change authority.frameLocation = keys[owner.position.val].frameLocation at physical
  let liveCapture := capture
  have liveLocals : Dynamic.EnvironmentAgrees heap header.function.context.locals [] := by
    obtain ⟨original⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool caller owner member
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
  obtain ⟨entry, child, bodyCompleted, childLe, _childStrict, parameterTransition, spine⟩ :=
    parameters_sized_with_state owner installedAuthority member liveCapture liveLocals liveReference represented installedHeaps
      layout actualTyped prefixCompleted producer parameterInitial readyAt
  obtain ⟨parameterState, parameterRelated⟩ := parameterTransition
  have installedRelated : Relates caller parameterInitial := by
    exact related_cast_frame caller physical.symm installed
      (CallableIndexedOwnedFunctionState.install_related caller owner.position (.stable history))
  exact ⟨⟨⟨origin, index, metadata, owned, history, emitted, _, entry,
    child, bodyStore, bodyCompleted, Nat.lt_of_le_of_lt childLe prefixSmaller, restored,
    parameterState, installedRelated.trans parameterRelated⟩, spine⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedEntryBounds
