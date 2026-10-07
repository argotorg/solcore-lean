import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionEntries

/-! Consumers of actual owned-value producers and reached-pool restoration.
The value receipts retain source dictionaries and complete native captures;
restoration keeps records produced during the body in every original row. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedOwnedFunctions
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CallableIndexedHistory
open CallableIndexedLambdaValues CallableIndexedOwnedFunctionValues

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}

/-- A named value exposes the ordered source dictionary, exact source frame,
and both canonical and actual references to its immutable physical owner. -/
theorem named_source_and_capture {sourceType : TypeSystem.Ty} {source : Dynamic.GlobalFunction}
    {native : Value} {type : Ty}
    (related : CallableIndexedOwnedFunctionValues.Represents headers keys bodyRegistry faults
      mapping world sourceType (.global source) native type) :
    ∃ owner : OwnedKey keys, ∃ header : CallableIndexedOwnedFunctionValues.Header compiled program, ∃ identity,
      ∃ capture : NamedCapture headers owner.key header mapping world,
      ∃ descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
          (.named header.named.signature.key),
        header ∈ headers ∧
        header.function.evidence = source.evidence ∧
        NamedCalls.SourceFrame program source.instantiation header.sourceBody header.function ∧
        LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
          header.named.signature.key [] header.function.source ∧
        NodeOccurrencesUnique header.function.source ∧
        capture.canonical[header.globals]? = some
          (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) ∧
        capture.captured[capture.embedding compiled.indexed.base.globals.length]? = some
          (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) ∧
        NamedInstalledCode capture ∧
        compiled.compatible.checked.catalog.project sourceType = .ok type ∧
        native = .pair (.pair (.inRight .unit (.word identity)) (.closure header.named.signature.parameterType
          (LanguageResult.resultType header.named.signature.resultType)
          (header.code.rename capture.embedding.lift) capture.captured)) (.word descriptor.id) := by
  obtain ⟨owner, header, _, identity, capture, descriptor, member, sourceAt, installed,
    _, projected, _, sourceType, native, type⟩ :=
    CallableIndexedOwnedFunctionValues.Represents.named_payload_inv related
  refine ⟨owner, header, identity, capture, descriptor, member, sourceAt.dictionary, sourceAt.frame,
    sourceAt.sourceOrigin, sourceAt.unique, capture.reference, capture.capturedReference, installed, ?_, native⟩
  simpa only [sourceType, type] using projected

/-- Anonymous inversion keeps the body registry, source origin, physical
owner reference, and the complete environment in the emitted closure. -/
theorem lambda_source_and_capture {sourceType : TypeSystem.Ty} {function : Dynamic.Closure}
    {native : Value} {type : Ty}
    (related : CallableIndexedOwnedFunctionValues.Represents headers keys bodyRegistry faults
      mapping world sourceType (.closure function) native type) :
    ∃ owner : OwnedKey keys, ∃ scope actual,
      ∃ (captured : Captures compiled.indexed mapping world scope function.captured actual)
        (code : Code compiled.indexed function scope captured.administrative)
        (history : History code) (body : StaticSupport headers bodyRegistry faults code),
        LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
          code.compilation.owner code.active function.source ∧
        NodeOccurrencesUnique function.source ∧
        history.metadata = CallableIndexedNamedGeneration.state body.1.named ∧
        captured.canonical[code.referenceIndex]? = some
          (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) ∧
        sourceType = FunctionValues.sourceType function ∧
        native = .pair (.pair (.inLeft .word .unit)
          (.closure code.receipt.parameterCore (LanguageResult.resultType code.receipt.resultCore)
            (code.body.rename captured.embedding.lift.lift)
            (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame history.native :: actual)))
          (.word code.descriptor.id) ∧
        type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore := by
  obtain ⟨owner, scope, actual, _, captured, code, history, body, origin,
    globals, referenceIndex, sourceType, native, type⟩ :=
    CallableIndexedOwnedFunctionValues.Represents.closure_inv related
  refine ⟨owner, scope, actual, captured, code, history, body, origin.source,
    origin.unique, origin.historyMetadata, ?_, sourceType, native, type⟩
  rw [referenceIndex]
  exact globals.reference

/-- A valid weak representation or native type cannot create an owned named
value when no catalogue key has been registered. -/
theorem no_named_owner_without_registered_key {sourceType : TypeSystem.Ty}
    {source : Dynamic.GlobalFunction} {native : Value} {type : Ty} :
    ¬ CallableIndexedOwnedFunctionValues.Represents headers [] bodyRegistry faults
      mapping world sourceType (.global source) native type := by
  intro related
  obtain ⟨owner, _⟩ := CallableIndexedOwnedFunctionValues.Represents.named_inv related
  exact Nat.not_lt_zero _ owner.position.isLt

/-- An anonymous value has the same registration boundary even if a native
closure is independently well typed and has a decodable descriptor. -/
theorem no_lambda_owner_without_registered_key {sourceType : TypeSystem.Ty}
    {function : Dynamic.Closure} {native : Value} {type : Ty} :
    ¬ CallableIndexedOwnedFunctionValues.Represents headers [] bodyRegistry faults
      mapping world sourceType (.closure function) native type := by
  intro related
  obtain ⟨owner, _⟩ := CallableIndexedOwnedFunctionValues.Represents.closure_inv related
  exact Nat.not_lt_zero _ owner.position.isLt

/-- A reached owned row supplies the complete named capture and its live
closure read, tying the pure owner token to actual pool authority. -/
theorem reached_owner_supplies_full_capture
    (pool : CallableIndexedOwnedFunctionEntries.OwnedPool headers keys mapping world heap store)
    (owner : OwnedKey keys) {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (member : header ∈ headers) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
      store.read? (owner.key.locations header) = some (.inRight .unit
        (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
          (header.code.rename capture.embedding.lift) capture.captured)) ∧
      capture.captured[capture.embedding compiled.indexed.base.globals.length]? = some
        (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) ∧
      Dynamic.EnvironmentAgrees heap header.function.context.locals [] := by
  obtain ⟨capture⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool pool owner member
  exact ⟨NamedCapture.of_capture capture, capture.read, capture.capturedReference, capture.locals⟩

section NamedRead
variable {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {identity internalReason : Word} {callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope}
  {canonical actual : Environment} {xi : Renaming}

/-- A real catalogue read produces an owned function with equality support.
Static installed code is checked against the cached template, while the
source dictionary comes from the actual named row and its header. -/
theorem qualified_named_read_is_owned
    (owner : OwnedKey keys) (member : header ∈ headers)
    (entry : RecursiveNamedCatalog.Entry (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix callerPrefix scope mapping world heap store canonical)
    (capture : RecursiveNamedCatalog.Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix owner.key.frameLocation header mapping world heap store)
    (agrees : EnvironmentsAgree xi canonical actual)
    (row : CallableIndexedNamedValues.Row compiled.indexed header.slot
      header.named.signature header.named.specialized rawD)
    (canonicalHeader : header.instantiation = CallableNamedMetadata.instantiation header.named.specialized)
    (dictionary : header.function.evidence = (CallableNamedMetadata.global header.named.specialized rawD).evidence)
    (cached : compiled.indexed.secondPass.closures[header.slot]? = some
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code))
    (embedding : capture.embedding = RecursiveGlobalInitializationMeaning.shift header.slot)
    (number : Word.ofNat? (header.slot + 1) = some identity)
    (projection : compiled.compatible.checked.catalog.project header.named.specialized.function.type = .ok
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType))
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key))
    (typed : RuntimeValueHasType world (.closure header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType) (header.code.rename capture.embedding.lift) capture.captured)
      header.named.signature.functionType compiled.indexed.layouts.definitions)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    let source := CallableNamedReversal.global (CallableNamedMetadata.global header.named.specialized rawD)
    let carrier := .pair (.pair (.inRight .unit (.word identity)) (.closure header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType)
      (header.code.rename capture.embedding.lift) capture.captured)) (.word descriptor.id)
    let expression := LanguageResult.bind
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType)
      (SourceCoreFunctions.namedReference header.named.signature
        (xi (scope.length + callerPrefix + header.slot)) identity internalReason)
      (LanguageResult.success (descriptor.wrap (.var 0)))
    Evaluates actual store expression (.inRight .word carrier) store ∧
    CallableIndexedOwnedFunctionValues.Represents headers keys bodyRegistry faults mapping world
      header.named.specialized.function.type (.global source) carrier
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType) ∧
    Observation compiled.compatible.checked.catalog bodyRegistry
      (CallableIndexedLambdaValues.Identity compiled.indexed)
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType)
      (.global source) carrier ∧
    (∀ result finalStore, Evaluates actual store expression result finalStore →
      result = .inRight .word carrier ∧ finalStore = store) := by
  dsimp only
  have sourceAt := NamedSourceAt.of_canonical_header row canonicalHeader dictionary
  have installed := NamedInstalledCode.of_cached (NamedCapture.of_capture capture) cached embedding
  obtain ⟨evaluation, related, deterministic⟩ := CallableIndexedOwnedFunctionValues.named_of_read
    (bodyRegistry := bodyRegistry) (faults := faults) owner member entry capture agrees sourceAt
    installed number projection descriptor typed
  exact ⟨evaluation, related,
    CallableIndexedOwnedFunctionValues.observations keys bodyRegistry faults profile related, deterministic⟩
end NamedRead

section LambdaFormation
variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {actual : Environment} {callerPrefix : Nat}

/-- Formation consumes a reached owner row and generated static support.
The resulting value supports source runtime guards and remains owned when
the explicit key domain grows. -/
theorem literal_formation_retains_owner
    (pool : CallableIndexedAuthorityPool.Pool (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers keys mapping world heap store)
    (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
    (code : Code compiled.indexed function scope captured.administrative) (history : History code)
    (body : StaticSupport headers bodyRegistry faults code)
    (metadata : history.metadata = CallableIndexedNamedGeneration.state body.1.named)
    (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation)
    (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
    (current : (pool.rows owner.position).authority.current = history.native)
    (ghost : (pool.rows owner.position).authority.ghost = history.ghost)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = [])
    (extra : List (CallableIndexedOwnedFunctionValues.Key compiled program)) :
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source function.captured heap
      code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding history.native actual)) store ∧
    CallableIndexedOwnedFunctionValues.Represents headers keys bodyRegistry faults mapping world
      (FunctionValues.sourceType function) (.closure function) (value code captured.embedding history.native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
    CallableIndexedOwnedFunctionValues.Represents headers (keys ++ extra) bodyRegistry faults mapping world
      (FunctionValues.sourceType function) (.closure function) (value code captured.embedding history.native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
    Dynamic.ValueRuntimeTypeMatches (.closure function) (FunctionValues.sourceType function) ∧
    (KeyEmbedding.append keys extra |>.map owner).key = owner.key := by
  have origin := ActualSourceOrigin.of_support history body metadata
  obtain ⟨sourceTrace, nativeTrace, related, _⟩ := CallableIndexedOwnedFunctionValues.lambda_of_formation
    pool owner captured code history body origin globals referenceIndex current ghost profile stored ordinary coercions
  exact ⟨sourceTrace, nativeTrace, related,
    CallableIndexedOwnedFunctionValues.Represents.map_keys (KeyEmbedding.append keys extra) related,
    CallableIndexedOwnedFunctionValues.runtime_views keys bodyRegistry faults profile (registry := bodyRegistry) related,
    (KeyEmbedding.append keys extra).same owner⟩
end LambdaFormation

section OwnedPrefixes
open CallableIndexedOwnedFunctionEntries

/-- Actual named parameter allocation uses the represented capture's full
canonical environment and administrative context. The generated prefix
retains its owner's original snapshots without an extra catalogue read. -/
theorem named_parameters_keep_original_capture
    (pool : OwnedPool headers keys mapping world heap store) (owner : OwnedKey keys)
    {header : CallableIndexedOwnedFunctionValues.Header compiled program} (member : header ∈ headers)
    (capture : NamedCapture headers owner.key header mapping world)
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {payloads : List Value}
    {actual : Environment} {actualContext : Core.Context} {xi : Renaming}
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree xi (DataPatternValues.packValues payloads :: capture.canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (record : CallableIndexedSnapshots.Record)
    (recordMember : record ∈ (pool.rows owner.position).authority.records) :
    ∃ entry : RecursiveNamedCatalog.ParameterEntry (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix functions registry header arguments heap store mapping world
      capture.administrative actualContext actual xi owner.key.frameLocation
      (pool.rows owner.position).authority.current (pool.rows owner.position).authority.ghost,
      DataHeap.EnvRepresents (storageCatalog compiled.compatible.checked.catalog) entry.mapping entry.world
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.administrative)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.canonical
        compiled.indexed.layouts.definitions ∧
      (named_parameter_catalog pool owner capture entry).authority.frameLocation = owner.key.frameLocation ∧
      (named_parameter_catalog pool owner capture entry).authority.records = (pool.rows owner.position).authority.records ∧
      CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        compiled.indexed.ancestry.layout.frame entry.mapping entry.store record := by
  obtain ⟨entry⟩ := named_parameters pool owner member capture represented heaps agrees actualTyped
  have retained : record ∈ ((named_parameter_pool pool owner capture entry).rows owner.position).authority.records := by
    rw [named_parameter_pool_records]; exact recordMember
  refine ⟨entry, entry.environments, named_parameter_catalog_owner_frame pool owner capture entry, ?_,
    ((named_parameter_pool pool owner capture entry).rows owner.position).authority.snapshots record retained⟩
  rw [named_parameter_catalog_records, named_parameter_pool_records]

/-- The actual sized lambda prefix keeps its generated source history and
full metadata, with the same selected records as its reached pool. -/
theorem sized_lambda_prefix_keeps_source_history
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
    {captured : Captures compiled.indexed mapping world scope function.captured actual}
    {code : Code compiled.indexed function scope captured.administrative} {history : History code}
    {inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code}
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value}
    (pool : OwnedPool headers keys mapping world heap store) (owner : OwnedKey keys)
    (reached : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments heap store owner.key.frameLocation
      (pool.rows owner.position).authority.current)
    {callerPrefix : Nat}
    (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation)
    (record : CallableIndexedSnapshots.Record)
    (recordMember : record ∈ (pool.rows owner.position).authority.records) :
    let sourceEntry := ordinary_source_entry_sized pool owner reached globals
    sourceEntry.catalog.authority.records = ((ordinary_pool_sized pool owner reached).rows owner.position).authority.records ∧
    sourceEntry.catalog.authority.ghost = .lambda code.descriptor.id history.ghost ∧
    Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      sourceEntry.catalog.authority.current (.lambda code.descriptor.id history.ghost) (some history.metadata) ∧
    reached.canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length
        + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) ∧
    CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame reached.mapping reached.store record := by
  dsimp only
  let sourceEntry := ordinary_source_entry_sized pool owner reached globals
  have retained : record ∈ ((ordinary_pool_sized pool owner reached).rows owner.position).authority.records := by
    rw [ordinary_pool_sized_records]; exact recordMember
  refine ⟨ordinary_source_entry_sized_records pool owner reached globals, sourceEntry.ghost,
    sourceEntry.carried, ?_, ((ordinary_pool_sized pool owner reached).rows owner.position).authority.snapshots record retained⟩
  have reference := sourceEntry.reference
  rw [ordinary_source_entry_sized_frame_eq] at reference
  exact reference
end OwnedPrefixes

section ReachedRestoration
open SourceCoreCallableIndexedFrames CallableIndexedOwnedFunctionEntries

variable {checked : SourceCoreCompatibleCatalog.Checked} {base : SourceCoreCompatibleFunctions.Prepared checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {poolHeaders : RecursiveNamedCatalog.Inventory prepared values ambient.definitions program}
  {poolKeys : List (CallableIndexedAuthorityPool.Key prepared values ambient.definitions program)}
  {futureMap : LocationMap} {futureWorld : StoreTyping} {after : Dynamic.Heap} {futureStore : Store}

/-- A record created during a body remains a protected snapshot after restore.
Every row sharing the selected physical frame receives the saved history;
a distinct physical row keeps its reached history and record list. -/
theorem restore_retains_body_records
    (saved : CallableIndexedAuthorityPool.Pool poolHeaders poolKeys mapping world heap store)
    (reached : CallableIndexedAuthorityPool.Pool poolHeaders poolKeys futureMap futureWorld after futureStore)
    (selected duplicate other row : Fin poolKeys.length)
    (same : poolKeys[duplicate.val].frameLocation = poolKeys[selected.val].frameLocation)
    (different : poolKeys[other.val].frameLocation ≠ poolKeys[selected.val].frameLocation)
    (record : CallableIndexedSnapshots.Record)
    (produced : record ∈ (reached.rows row).authority.records) :
    let restored := restored_pool saved reached selected
    record ∈ (restored.rows row).authority.records ∧
    CallableIndexedSnapshots.Holds prepared.graph.inputs prepared.graph.table prepared.layout.frame futureMap
      (futureStore.set poolKeys[selected.val].frameLocation
        (encode prepared.layout.frame (saved.rows selected).authority.current)) record ∧
    (restored.rows selected).authority.current = (saved.rows selected).authority.current ∧
    (restored.rows duplicate).authority.current = (saved.rows selected).authority.current ∧
    (restored.rows duplicate).authority.ghost = (saved.rows selected).authority.ghost ∧
    (restored.rows other).authority.current = (reached.rows other).authority.current ∧
    (restored.rows other).authority.ghost = (reached.rows other).authority.ghost ∧
    (restored.rows other).authority.records = (reached.rows other).authority.records := by
  dsimp only
  have retained : record ∈ ((restored_pool saved reached selected).rows row).authority.records := by
    rw [restored_records]
    exact produced
  refine ⟨retained, ((restored_pool saved reached selected).rows row).authority.snapshots record retained,
    ?_, ?_, ?_, ?_, ?_, restored_records saved reached selected other⟩
  · rw [restored_current]; simp
  · rw [restored_current]; simp only [same, ↓reduceIte]
  · rw [restored_ghost]; simp only [same, ↓reduceIte]
  · rw [restored_current]; simp only [different, ↓reduceIte]
  · rw [restored_ghost]; simp only [different, ↓reduceIte]

/-- The actual restore boundary also retains the final source heap and its
new snapshots, while reinstating shared history at the selected physical cell. -/
theorem actual_restore_retains_body_effects
    (saved : CallableIndexedAuthorityPool.Pool poolHeaders poolKeys mapping world heap store)
    (reached : CallableIndexedAuthorityPool.Pool poolHeaders poolKeys futureMap futureWorld after futureStore)
    (selected duplicate other row : Fin poolKeys.length)
    (same : poolKeys[duplicate.val].frameLocation = poolKeys[selected.val].frameLocation)
    (different : poolKeys[other.val].frameLocation ≠ poolKeys[selected.val].frameLocation)
    (record : CallableIndexedSnapshots.Record)
    (produced : record ∈ (reached.rows row).authority.records)
    {next : NativeFrame} {functions : FunctionModel values.checked.catalog ambient}
    {registry : SourceCoreRawMetadata.Registry}
    (registered : prepared.layout.frame.Registered ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions futureMap futureWorld after futureStore)
    (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping
      (store.set poolKeys[selected.val].frameLocation (encode prepared.layout.frame next)) futureMap futureStore) :
    let restoredStore := futureStore.set poolKeys[selected.val].frameLocation
      (encode prepared.layout.frame (saved.rows selected).authority.current)
    ∃ finalPool : CallableIndexedAuthorityPool.Pool poolHeaders poolKeys futureMap futureWorld after restoredStore,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions futureMap futureWorld after restoredStore ∧
      AdministrativePreserved mapping store futureMap restoredStore ∧
      record ∈ (finalPool.rows row).authority.records ∧
      CallableIndexedSnapshots.Holds prepared.graph.inputs prepared.graph.table prepared.layout.frame
        futureMap restoredStore record ∧
      (finalPool.rows duplicate).authority.current = (saved.rows selected).authority.current ∧
      (finalPool.rows other).authority.current = (reached.rows other).authority.current ∧
      (finalPool.rows other).authority.records = (reached.rows other).authority.records := by
  dsimp only
  obtain ⟨finalPool, _, finalHeaps, finalFrame, _, records, currents, _, _⟩ :=
    restore_reached_pool saved reached selected registered heaps worlds frame
  have retained : record ∈ (finalPool.rows row).authority.records := by
    rw [records row]; exact produced
  refine ⟨finalPool, finalHeaps, finalFrame, retained, (finalPool.rows row).authority.snapshots record retained,
    ?_, ?_, records other⟩
  · rw [currents duplicate]; simp only [same, ↓reduceIte]
  · rw [currents other]; simp only [different, ↓reduceIte]

/-- Original records and newly reached records coexist after restore, using
membership extension rather than an equality assumption on record lists. -/
theorem restore_retains_original_and_new
    (saved : CallableIndexedAuthorityPool.Pool poolHeaders poolKeys mapping world heap store)
    (reached : CallableIndexedAuthorityPool.Pool poolHeaders poolKeys futureMap futureWorld after futureStore)
    (selected row : Fin poolKeys.length) (retained : RecordsExtend saved reached)
    (original fresh : CallableIndexedSnapshots.Record)
    (oldMember : original ∈ (saved.rows row).authority.records)
    (newMember : fresh ∈ (reached.rows row).authority.records) :
    original ∈ ((restored_pool saved reached selected).rows row).authority.records ∧
    fresh ∈ ((restored_pool saved reached selected).rows row).authority.records := by
  constructor
  · exact RecordsExtend.restored saved reached selected retained row original oldMember
  · rw [restored_records]; exact newMember

/-- The body restore write preserves the exact full closure, even for a
catalogue row with a different physical owner and an unused capture suffix. -/
theorem restore_retains_full_capture
    (saved : CallableIndexedAuthorityPool.Pool poolHeaders poolKeys mapping world heap store)
    (reached : CallableIndexedAuthorityPool.Pool poolHeaders poolKeys futureMap futureWorld after futureStore)
    (selected row : Fin poolKeys.length)
    {header : RecursiveNamedCatalog.Header prepared values ambient.definitions program}
    (member : header ∈ poolHeaders)
    (capture : RecursiveNamedCatalog.Capture poolHeaders poolKeys[row.val].locations poolKeys[row.val].capturePrefix
      (reached.rows row).authority.frameLocation header futureMap futureWorld after futureStore) :
    Store.read? (futureStore.set poolKeys[selected.val].frameLocation
        (encode prepared.layout.frame (saved.rows selected).authority.current)) (poolKeys[row.val].locations header) =
      some (.inRight .unit (.closure header.named.signature.parameterType
        (LanguageResult.resultType header.named.signature.resultType)
        (header.code.rename capture.embedding.lift) capture.captured)) :=
  restored_capture_read saved reached selected row member capture
end ReachedRestoration

end Tests.SourceCoreCallableIndexedOwnedFunctions
