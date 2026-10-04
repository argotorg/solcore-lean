import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogEntries
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBoundedContracts

/-! Real parameter prefixes retain the whole installed catalog and the original
body subderivation. Body contracts are pointwise runtime interfaces; static
headers and profiles remain unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning RecursiveNamedCatalog
abbrev Scope := SourceCoreLocalCell.Scope
abbrev Below := RecursiveNamedBoundedContracts.Below
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix callerPrefix : Nat} {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
  {heap after : Dynamic.Heap} {store futureStore : Store}

structure BodyState (headers : Inventory prepared values ambient.definitions program)
    (locations : Locations) (capturePrefix : Nat)
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (header : Header prepared values ambient.definitions program)
    (arguments : List Dynamic.Value) (before : Dynamic.Heap) (initialStore : Store)
    (initialMap : LocationMap) (initialWorld : StoreTyping) (administrative actualContext : Core.Context)
    (actual : Environment) (ξ : Renaming) (frameLocation : Location) (current : NativeFrame) (ghost : GhostFrame) where private mk ::
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  actualBody : Environment
  store : Store
  mapping : LocationMap
  world : StoreTyping
  embedding : Renaming
  allocation : Dynamic.BindersAllocate [] before header.function.parameters arguments environment heap
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical ambient.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap header.context.locals environment
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before heap
  lookups : EnvironmentsAgree embedding canonical actualBody
  actualTyped : RuntimeEnvironmentHasTypes world actualBody
    (CallableIndexedParameterTyped.prefixContext header.bindings actualContext) ambient.definitions
  catalog : Entry headers locations capturePrefix (capturePrefix + 1)
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) mapping world heap store canonical
  reference : canonical[header.bindings.length + 1 + header.globals]? =
    some (.cellRef prepared.layout.frame.type frameLocation)
  state : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame frameLocation current ghost store
  catalog_frame : catalog.authority.frameLocation = frameLocation
  catalog_current : catalog.authority.current = current
  catalog_ghost : catalog.authority.ghost = ghost


def BodyState.of_entry
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {header : Header prepared values ambient.definitions program} {arguments : List Dynamic.Value}
    {before : Dynamic.Heap} {initialStore : Store} {initialMap : LocationMap} {initialWorld : StoreTyping}
    {administrative actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (entry : ParameterEntry headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost) :
    BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost :=
  { environment := entry.environment,
    heap := entry.heap,
    canonical := entry.canonical,
    actualBody := entry.actualBody,
    store := entry.store,
    mapping := entry.mapping,
    world := entry.world,
    embedding := entry.embedding,
    allocation := entry.allocation,
    environments := entry.environments,
    heaps := entry.heaps,
    locals := entry.locals,
    maps := entry.maps,
    worlds := entry.worlds,
    frame := entry.frame,
    metadata := entry.metadata,
    lookups := entry.lookups,
    actualTyped := entry.actualTyped,
    catalog := entry.catalog,
    reference := entry.reference,
    state := entry.state,
    catalog_frame := entry.catalog_frame,
    catalog_current := entry.catalog_current,
    catalog_ghost := entry.catalog_ghost }

private theorem insert_at_suffix (added suffix : Environment) (value : Value) :
    Environment.insertAt (added ++ suffix) added.length value = added ++ value :: suffix := by
  induction added with
  | nil => simp [Environment.insertAt]
  | cons head tail ih => simpa [Environment.insertAt] using congrArg (List.cons head) ih

private theorem insert_administrative {administrative : Core.Context} {scope : Scope}
    {environment : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    {value : Value} {type : Ty} (typed : RuntimeValueHasType world value type ambient.definitions) :
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      (type :: administrative) scope environment (Environment.insertAt canonical scope.length value) ambient.definitions := by
  induction related with
  | nil values => exact .nil (by simpa [Environment.insertAt] using RuntimeEnvironmentHasTypes.cons typed values)
  | cons reference _ ih => exact .cons reference ih
  | internal reference absent _ ih => exact .internal reference absent ih


theorem parameters_sized (authority : Authority headers locations capturePrefix mapping world heap store)
    {header : Header prepared values ambient.definitions program} (_member : header ∈ headers)
    (capture : Capture headers locations capturePrefix authority.frameLocation header mapping world heap store)
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    {actual actualContext ξ}
    (agrees : EnvironmentsAgree ξ (DataPatternValues.packValues payloads :: capture.canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {size : Nat} {result : Value} {afterStore : Store}
    (completed : EvaluationSize size actual store (header.parameterCode.rename ξ) result afterStore) :
    ∃ entry : BodyState headers locations capturePrefix functions registry header arguments heap store mapping world
      capture.administrative actualContext actual ξ authority.frameLocation authority.current authority.ghost,
      ∃ child, EvaluationSize child entry.actualBody entry.store (header.body.rename entry.embedding) result afterStore ∧
        child ≤ size ∧ (header.bindings ≠ [] → child < size) := by
  have tree := CallableIndexedParameterCertificates.of_accepted header.onError header.acceptedPrefix
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) capture.canonical
      (DataPatternValues.packValues payloads :: capture.canonical) := by
    intro index value found; exact found
  have length : (header.bindings.map Prod.snd).length = payloads.length := by simpa using represented.length.2
  obtain ⟨environment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding, child,
    allocated, finalEnvironments, finalHeaps, maps, worlds, preservation, _, lookups, spine, finalTyped, bodyCompletion, childLe, childStrict⟩ :=
    RecursiveNamedCallBounds.parameter_prefix tree header.definitions_eq header.registered represented capture.environments heaps
      sourceLayout agrees actualTyped (allTypes := header.bindings.map Prod.snd) (named := true) rfl (by simp) length
      (fun {_ _} found => by simpa using found) (CallableIndexedParameters.inputKinds header.inputs)
      (by simpa using capture.reference) authority.frame.read authority.unmapped completed
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
  let catalog : Entry headers locations capturePrefix (capturePrefix + 1)
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
      some (.cellRef prepared.layout.frame.type authority.frameLocation) := by
    rw [logicalEq]
    have index : header.bindings.length + 1 + header.globals = added.length + (header.globals + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using capture.reference
  have current := CallableIndexedBodyFrames.body_current authority.unmapped authority.frame preservation
  have mono := FunctionCallBody.mono_binders header.extended
  refine ⟨⟨environment, finalHeap, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding,
    allocated, by simpa using finalWithBundle, finalHeaps,
    GenericLexicalContext.binders_agree mono.1 mono.2 capture.locals allocated,
    maps, worlds, preservation, metadata, lookups, finalTyped, catalog, finalReference, current, (by rfl), (by rfl), (by
      change (authority.extend maps worlds preservation metadata).ghost = authority.ghost
      rfl)⟩, child, bodyCompletion, childLe, childStrict⟩


theorem named_parameters_sized (authority : Authority headers locations capturePrefix mapping world heap store)
    {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    (capture : Capture headers locations capturePrefix authority.frameLocation header mapping world heap store)
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) result finalStore) :
    ∃ origin index metadata,
      prepared.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      header.code = withFrame (.var (base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) header.parameterCode ∧
      ∃ entry : BodyState headers locations capturePrefix functions registry header arguments heap
        (store.set authority.frameLocation (encode prepared.layout.frame (.state index))) mapping world
        capture.administrative
        (.unit :: prepared.layout.frame.type :: header.named.signature.parameterType :: capture.capturedContext)
        (.unit :: encode prepared.layout.frame authority.current :: DataPatternValues.packValues payloads :: capture.captured)
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift))
        authority.frameLocation (.state index) (.named origin),
      ∃ child bodyStore, EvaluationSize child entry.actualBody entry.store (header.body.rename entry.embedding) result bodyStore ∧
        child < size ∧ finalStore = bodyStore.set authority.frameLocation (encode prepared.layout.frame authority.current) := by
  obtain ⟨origin, index, owned, selected, emitted⟩ := CallableIndexedFormation.namedBody_receipt prepared header.hook
  obtain ⟨metadata, history⟩ : ∃ metadata, Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) := by
    cases found : prepared.graph.table.namedAt? origin with
    | none => simp [SourceCoreCallableIndexedDispatch.namedFrame, found] at selected
    | some position =>
      obtain ⟨metadata, history⟩ := named_history prepared.graph found
      exact ⟨metadata, selected ▸ history⟩
  have reference : (DataPatternValues.packValues payloads :: capture.captured)[capture.embedding.lift (base.globals.length + 1)]? =
      some (.cellRef prepared.layout.frame.type authority.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using capture.capturedReference
  obtain ⟨actualOrigin, actualIndex, prefixSize, bodyStore, actualOwned, actualSelected, prefixCompleted, prefixSmaller, restored⟩ :=
    RecursiveNamedCallBounds.named_hook_body prepared header.hook reference authority.frame.read completed
  have sameOrigin : actualOrigin = origin := Option.some.inj (actualOwned.symm.trans owned)
  subst actualOrigin
  have sameIndex : actualIndex = index := by
    have same := actualSelected.symm.trans selected
    injection same
  subst actualIndex
  rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at prefixCompleted
  have written : store.write? authority.frameLocation (encode prepared.layout.frame (.state index)) =
      some (store.set authority.frameLocation (encode prepared.layout.frame (.state index))) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp authority.frame.read).1, rfl⟩
  let installed := authority.install (.stable history)
  let nextCapture : Capture headers locations capturePrefix authority.frameLocation header mapping world heap
      (store.set authority.frameLocation (encode prepared.layout.frame (.state index))) :=
    { capture with read := (Store.write?_preserves_other written capture.distinct).trans capture.read }
  have installedHeaps := (CallableIndexedBodyFrames.install header.registered heaps authority.unmapped authority.typed
    authority.frame (.stable history)).1
  have layout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift))
      (DataPatternValues.packValues payloads :: capture.canonical)
      (.unit :: encode prepared.layout.frame authority.current :: DataPatternValues.packValues payloads :: capture.captured) :=
    GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift capture.layout (DataPatternValues.packValues payloads))
      (encode prepared.layout.frame authority.current)) .unit
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues payloads)
      header.named.signature.parameterType ambient.definitions :=
    header.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (definitions := ambient.definitions))
    (.cons (encode_runtime_typed world header.registered authority.current) (.cons packTyped capture.typed))
  obtain ⟨entry, child, bodyCompleted, childLe, _⟩ :=
    parameters_sized installed member nextCapture represented installedHeaps layout actualTyped prefixCompleted
  exact ⟨origin, index, metadata, owned, history, emitted, entry, child, bodyStore, bodyCompleted,
    Nat.lt_of_le_of_lt childLe prefixSmaller, restored⟩



variable (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
  (header : Header prepared values ambient.definitions program) (faults : FunctionCalls.FaultRep)

/-- A static predicate at the original, fully retained body state. It does not
contain an execution law or recover a source history from native typing. -/
abbrev BodyCondition :=
  ∀ {arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost},
    BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost → Prop

/-- Actual hook ownership and its carried history authorize precisely the
state reached by the named parameter prefix. Arbitrary body states are excluded. -/
def BodyAuthorization (condition : BodyCondition (headers := headers) (locations := locations)
    (capturePrefix := capturePrefix) functions registry header) : Prop :=
  ∀ {origin index metadata arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation},
    prepared.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin →
    Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) →
    header.code = withFrame (.var (base.globals.length + 1))
      (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) header.parameterCode →
    ∀ entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation (.state index) (.named origin), condition entry

/-- A pointwise body obligation at the real parameter entry. The independent
source context is the one retained by this header and its marked prefix. -/
def BodyPreservesAt (size : Nat) : Prop :=
  ∀ {arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost}
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    {outcome after},
    RecursiveNamedCallBounds.BodyTrace program size header.function header.context entry.environment entry.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after

/-- Reflection consumes the original body subderivation. Its independent source
cost is an output and is never compared with the native input cost. -/
def BodyReflectsAt (size : Nat) : Prop :=
  ∀ {arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost}
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    {value finalStore},
    EvaluationSize size entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after

/-- A pointwise body obligation at the real parameter entry. The independent
source context is the one retained by this header and its marked prefix. -/
def BodyPreservesAtWith (condition : BodyCondition (headers := headers) (locations := locations)
    (capturePrefix := capturePrefix) functions registry header) (size : Nat) : Prop :=
  ∀ {arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost}
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    {outcome after}, condition entry →
    RecursiveNamedCallBounds.BodyTrace program size header.function header.context entry.environment entry.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after

/-- Reflection consumes the original body subderivation. Its independent source
cost is an output and is never compared with the native input cost. -/
def BodyReflectsAtWith (condition : BodyCondition (headers := headers) (locations := locations)
    (capturePrefix := capturePrefix) functions registry header) (size : Nat) : Prop :=
  ∀ {arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost}
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    {value finalStore}, condition entry →
    EvaluationSize size entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after

variable {functions registry header faults}

theorem body_preserves_of_pointwise {size : Nat} {certificate : FunctionCode.BodyCertificate}
    (certified : certificate header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body header.output header.body)
    {finalContext facts} (typed : StatementsHaveType header.function.source
      {returnType := header.function.resultType, loopDepth := 0} header.context header.function.body finalContext facts)
    (meaning : RecursiveNamedBoundedContracts.BodyPreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program header.function certificate faults
      (protectedEntry headers locations capturePrefix (capturePrefix + 1))) :
    BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry outcome after trace
  exact meaning certified typed entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped ⟨entry.catalog⟩ trace

theorem body_reflects_of_pointwise {size : Nat} {certificate : FunctionCode.BodyCertificate}
    (certified : certificate header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body header.output header.body)
    {finalContext facts} (typed : StatementsHaveType header.function.source
      {returnType := header.function.resultType, loopDepth := 0} header.context header.function.body finalContext facts)
    (meaning : RecursiveNamedBoundedContracts.BodyReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program header.function certificate faults
      (protectedEntry headers locations capturePrefix (capturePrefix + 1))) :
    BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry value finalStore completed
  exact meaning certified typed entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped ⟨entry.catalog⟩ completed

private theorem body_of_trace_sized {size : Nat} {arguments : List Dynamic.Value}
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

private theorem rename_prefix (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

private theorem next_evaluates (index : Int) (actual : Environment) (store : Store) (saved : Value) :
    Evaluates (saved :: actual) store
      ((SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)).weakenAt 0)
      (encode prepared.layout.frame (.state index)) store := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

/-- Only the real strictly smaller source body child selects the body IH. -/
theorem invocation_preserves_bounded_with
    (condition : BodyCondition (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header)
    (authorized : BodyAuthorization (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header condition)
    (budget : Nat)
    (bodyMeaning : Below budget (BodyPreservesAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults condition))
    {scope : Scope} {canonical : Environment}
    (caller : Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    (member : header ∈ headers) {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome program size header.sourceBody header.function.evidence heap arguments outcome after)
    (within : size ≤ budget) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world heap store,
      ∃ value finalStore finalMap finalWorld,
        Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
          (header.code.rename capture.embedding.lift) value finalStore ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  have arity : header.function.parameters.length = arguments.length := by
    rw [header.parameters, List.length_map]; exact represented.length.1
  obtain ⟨child, environment, bound, allocated, bodyTrace, smaller⟩ :=
    RecursiveNamedCallBounds.body_trace header.frame header.extended arity trace
  obtain ⟨origin, index, metadata, owned, history, emitted, capture, entry⟩ := named_parameters caller.authority member represented heaps
  obtain ⟨entry⟩ := entry
  let state := BodyState.of_entry entry
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same state.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps, bodyMaps, bodyWorlds, bodyFrame, bodyMetadata⟩ :=
    bodyMeaning child (Nat.lt_of_lt_of_le smaller within) state (authorized owned history emitted state) bodyTrace
  have prefixEvaluation := entry.agreement.wrap bodyEvaluation
  rw [rename_prefix] at prefixEvaluation
  have reference : (DataPatternValues.packValues payloads :: capture.captured)[capture.embedding.lift (base.globals.length + 1)]? =
      some (.cellRef prepared.layout.frame.type caller.authority.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using capture.capturedReference
  have evaluation := CallableContextFrames.withFrame_evaluates (.var reference) caller.authority.frame.read
    (next_evaluates index (DataPatternValues.packValues payloads :: capture.captured) store (encode prepared.layout.frame caller.authority.current)) prefixEvaluation
  have renamed : header.code.rename capture.embedding.lift = withFrame
      (.var (capture.embedding.lift (base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) (header.parameterCode.rename capture.embedding.lift) := by
    rw [emitted, NamedCalls.withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  have maps := state.maps.trans bodyMaps
  have worlds := state.worlds.trans bodyWorlds
  have frame := state.frame.trans bodyFrame
  have sourceMetadata := state.metadata.trans bodyMetadata
  obtain ⟨restoredHeaps, restoredFrame, _⟩ := CallableIndexedBodyFrames.restore header.registered caller.authority.unmapped caller.authority.typed
    caller.authority.frame finalHeaps worlds frame
  exact ⟨capture, value, _, finalMap, finalWorld, renamed.symm ▸ evaluation, result, restoredHeaps, maps, worlds,
    restoredFrame, sourceMetadata, ⟨caller.extend maps worlds restoredFrame sourceMetadata⟩⟩

theorem invocation_preserves_bounded (budget : Nat)
    (bodyMeaning : Below budget (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults))
    {scope : Scope} {canonical : Environment}
    (caller : Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    (member : header ∈ headers) {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome program size header.sourceBody header.function.evidence heap arguments outcome after)
    (within : size ≤ budget) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world heap store,
      ∃ value finalStore finalMap finalWorld,
        Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
          (header.code.rename capture.embedding.lift) value finalStore ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact invocation_preserves_bounded_with (fun _ => True) (by unfold BodyAuthorization; intros; trivial) budget
    (by
      intro child smaller arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry result after _ trace
      exact bodyMeaning child smaller entry trace) caller member represented heaps trace within
/-- Original hook and parameter sizes choose the reflected body IH. -/
theorem invocation_reflects_bounded_with
    (condition : BodyCondition (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header)
    (authorized : BodyAuthorization (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header condition)
    (budget : Nat)
    (bodyMeaning : Below budget (BodyReflectsAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults condition))
    {scope : Scope} {canonical : Environment}
    (caller : Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    (member : header ∈ headers) {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world heap store)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome program sourceSize header.sourceBody header.function.evidence heap arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  obtain ⟨origin, index, metadata, owned, history, emitted, entry, child, bodyStore, bodyCompleted, smaller, restored⟩ :=
    named_parameters_sized caller.authority member represented heaps capture completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, bodyMaps, bodyWorlds, bodyFrame, bodyMetadata⟩ :=
    bodyMeaning child (Nat.lt_of_lt_of_le smaller within) entry (authorized owned history emitted entry) bodyCompleted
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have frame := entry.frame.trans bodyFrame
  have sourceMetadata := entry.metadata.trans bodyMetadata
  obtain ⟨restoredHeaps, restoredFrame, _⟩ := CallableIndexedBodyFrames.restore header.registered caller.authority.unmapped caller.authority.typed
    caller.authority.frame finalHeaps worlds frame
  subst finalStore
  exact ⟨_, outcome, after, finalMap, finalWorld, body_of_trace_sized entry.allocation trace, result, restoredHeaps,
    maps, worlds, restoredFrame, sourceMetadata, ⟨caller.extend maps worlds restoredFrame sourceMetadata⟩⟩

theorem invocation_reflects_bounded (budget : Nat)
    (bodyMeaning : Below budget (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults))
    {scope : Scope} {canonical : Environment}
    (caller : Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    (member : header ∈ headers) {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world heap store)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome program sourceSize header.sourceBody header.function.evidence heap arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact invocation_reflects_bounded_with (fun _ => True) (by unfold BodyAuthorization; intros; trivial) budget
    (by
      intro child smaller arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry result after _ trace
      exact bodyMeaning child smaller entry trace) caller member represented heaps capture completed within

private theorem finish_rename (type : Ty) (flow : Expr) (fellThrough escaped : Word) (ξ : Renaming) :
    (CompatibleStatements.finish type flow fellThrough escaped).rename ξ =
      CompatibleStatements.finish type (flow.rename ξ) fellThrough escaped := by
  unfold CompatibleStatements.finish
  split <;> simp [LocalControl.finish, LocalLoop.toControl, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.rename, Renaming.lift]

/-- The accepted finish wrapper supplies another original strict child. -/
theorem body_flow_sized {flow : Expr} (emitted : header.body =
      CompatibleStatements.finish header.output flow header.fellThrough header.escaped)
    {size : Nat} {actual : Environment} {store finalStore : Store} {ξ : Renaming} {value : Value}
    (completed : EvaluationSize size actual store (header.body.rename ξ) value finalStore) :
    ∃ child flowValue middle, child < size ∧ EvaluationSize child actual store (flow.rename ξ) flowValue middle := by
  rw [emitted, finish_rename] at completed
  exact RecursiveNamedCallBounds.finish_flow completed

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogInvocationBounds
