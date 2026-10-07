import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMarkedAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestoration

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

end Continuations

/-- The original strictly smaller Source body child consumes the real parameter
pool. Returning restores the saved caller in that body's actual reached pool. -/
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
  obtain ⟨restoredHeaps, restoredFrame, _cell, _bodyRelated, _callerRelated, _records, returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position header.registered finalHeaps worlds
      (by simpa only [physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using frame) related
  refine ⟨value, _, finalMap, finalWorld, ?_, result, restoredHeaps,
    maps, worlds, restoredFrame, sourceMetadata, returned⟩
  simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical, authority, liveCapture] using
    (renamed.symm ▸ evaluation)

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
  obtain ⟨restoredHeaps, restoredFrame, _cell, _bodyRelated, _callerRelated, _records, returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position header.registered finalHeaps worlds
      (by simpa only [physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using frame) related
  subst finalStore
  refine ⟨_, outcome, after, finalMap, finalWorld, body_of_trace_sized entry.allocation trace, result, ?_,
    maps, worlds, ?_, sourceMetadata, ?_⟩
  · simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical, authority] using restoredHeaps
  · simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical, authority] using restoredFrame
  · simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical, authority] using returned


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
