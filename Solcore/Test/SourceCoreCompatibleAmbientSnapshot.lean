import Solcore.SourceSemantics.CoreLowering.CallableIndexedAmbient
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceDescription
import Solcore.Frontend.SourceCoreCallableIndexedLedger
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Live snapshots use the same generic heap under the indexed compiler's real
frame/marker suffix. Source metadata stays in the base compatible catalog.
The theorem consumers retain static path receipts and independent source
reads/faults; they do not assume generated helper execution. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleAmbientSnapshot
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleEquality CompatibleMapping CompatibleMapping.MixedPaths CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces CompatiblePlaceLiveRoot

/-- No second heap relation is introduced by the live-root adapters. -/
theorem same_heap_model {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient) :
    CompatibleHeap.payloadModel checked registry functions =
      CompatibleAmbientHeap.payloadModel checked registry functions := rfl

variable {checked : Checked} (artifact : SourceCoreCallableIndexedPrograms.Prepared checked)
  {registry : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel checked.catalog (CallableIndexedAmbient.ambientDefinitions artifact)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {prepared : Prepared} {location : Dynamic.Location} {target : Location}
  {cell : Dynamic.Cell} {optional nativeRoot : Value} {sourceRoot : Dynamic.Value}
  {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
  {leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
  {keySites : List (ExpressionId × Ty)} {keys : List Value} {resolved : List Dynamic.EvaluatedProjection}
  {path : PreparedPath checked source site cell.type projections position prepared.steps keySites leaf}
  {identities : Dynamic.Value → Word → Prop}
  {environment : Environment} {context : Core.Context} {keyType : Ty} {reference keyExpression : Expr}

/-- The common represented heap supplies live initialized-root facts even
when its native values mention freshly generated definitions. -/
theorem initialized_root_under_indexed {sourceType : TypeSystem.Ty}
    (heaps : CompatibleAmbientHeap.HeapRepresents checked registry functions mapping world heap store)
    (ref : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location ⟨sourceType, some sourceRoot, none⟩) :
    ∃ native, RootRead checked registry functions mapping world prepared heap store location target
      ⟨sourceType, some sourceRoot, none⟩ (.inRight .unit native) sourceRoot native :=
  CompatibleHeap.HeapRepresents.initialized_root heaps ref read

/-- Actual virtual-root generation recovers a source empty mapping without
initializing the mapped native cell or changing the common heap relation. -/
theorem virtual_root_under_indexed {carrierContext : SourceCoreCompatibleValues.Context}
    (artifact : SourceCoreCallableIndexedPrograms.Prepared carrierContext.checked)
    {functions : FunctionModel carrierContext.checked.catalog (CallableIndexedAmbient.ambientDefinitions artifact)}
    {key valueType : TypeSystem.Ty}
    (heaps : CompatibleAmbientHeap.HeapRepresents carrierContext.checked registry functions mapping world heap store)
    (ref : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location ⟨.mapping key valueType, none, none⟩)
    (generated : VirtualRoot.Generated carrierContext prepared.route key valueType)
    (extension : SourceCoreRawMetadata.Extends carrierContext.registry registry) :
    ∃ native, RootRead carrierContext.checked registry functions mapping world prepared heap store location target
      ⟨.mapping key valueType, none, none⟩ (.inLeft prepared.route.rootType .unit) (.mapping key valueType []) native :=
  CompatibleHeap.HeapRepresents.virtual_root heaps ref read generated extension

/-- Successful live getters preserve every source cell and earlier native
administrative cell, while their real allocations extend the native world. -/
theorem snapshot_under_indexed
    (heaps : CompatibleAmbientHeap.HeapRepresents checked registry functions mapping world heap store)
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot nativeRoot)
    (arguments : Arguments checked registry functions mapping world source site keys path resolved)
    (leafProjected : checked.catalog.project leaf = .ok prepared.route.leafType)
    {selected : Dynamic.Value} (read : Dynamic.ProjectionsRead (some sourceRoot) resolved (some selected))
    (nonempty : prepared.steps ≠ []) (faithful : DataEquality.IdentityFaithful identities)
    (leaves : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (envTyped : RuntimeEnvironmentHasTypes world environment context artifact.layouts.definitions)
    (typed : HasType context (.apply (getter prepared keyType) (.pair (.loadCell reference) keyExpression))
      (LanguageResult.resultType prepared.optionalLeaf) artifact.layouts.definitions)
    (refSelected : DataEquality.Selects environment reference (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keySelected : DataEquality.Selects environment keyExpression (DataPatternValues.packValues keys)) :
    ∃ native after futureWorld,
      CompatibleAmbientHeap.HeapRepresents checked registry functions mapping futureWorld heap after ∧
      ValueRep checked registry functions mapping futureWorld leaf selected native prepared.route.leafType ∧
      FiniteRun environment store (.apply (getter prepared keyType) (.pair (.loadCell reference) keyExpression))
        (.inRight .word (.inRight .unit native)) after ∧
      after.read? target = some optional ∧ WorldExtends world futureWorld ∧
      AdministrativePreserved mapping store mapping after := by
  obtain ⟨native, after, suffix, future, _, represented, ran, extension, storeTyped, _, finalRoot, frame, appended, _⟩ :=
    read_at root arguments leafProjected read nonempty faithful leaves keyLength heaps.runtime_hasTypes envTyped typed refSelected keySelected
  exact ⟨native, after, future, CompatibleHeap.HeapRepresents.after_snapshot heaps extension storeTyped appended,
    represented, ran, finalRoot.nativeRead, extension, frame⟩

/-- Exact raw missing-default tokens and heap preservation survive the same
ambient extension. No writeback or source mutation is inferred from failure. -/
theorem fault_under_indexed
    (heaps : CompatibleAmbientHeap.HeapRepresents checked registry functions mapping world heap store)
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot nativeRoot)
    (arguments : Arguments checked registry functions mapping world source site keys path resolved)
    {reason : Dynamic.SemanticFault} (fault : Dynamic.ProjectionsFaults (some sourceRoot) resolved reason)
    (nonempty : prepared.steps ≠ []) (faithful : DataEquality.IdentityFaithful identities)
    (leaves : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (envTyped : RuntimeEnvironmentHasTypes world environment context artifact.layouts.definitions)
    (typed : HasType context (.apply (getter prepared keyType) (.pair (.loadCell reference) keyExpression))
      (LanguageResult.resultType prepared.optionalLeaf) artifact.layouts.definitions)
    (refSelected : DataEquality.Selects environment reference (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keySelected : DataEquality.Selects environment keyExpression (DataPatternValues.packValues keys)) :
    ∃ token count after futureWorld,
      FaultToken checked registry sourceRoot prepared.steps resolved reason token count ∧
      CompatibleAmbientHeap.HeapRepresents checked registry functions mapping futureWorld heap after ∧
      FiniteRun environment store (.apply (getter prepared keyType) (.pair (.loadCell reference) keyExpression))
        (.inLeft prepared.optionalLeaf (.word token)) after ∧
      after.read? target = some optional ∧ WorldExtends world futureWorld ∧
      AdministrativePreserved mapping store mapping after := by
  obtain ⟨token, count, after, suffix, future, _, receipt, ran, extension, storeTyped, _, finalRoot, frame, appended, _⟩ :=
    fault_at root arguments fault nonempty faithful leaves keyLength heaps.runtime_hasTypes envTyped typed refSelected keySelected
  exact ⟨token, count, after, future, receipt, CompatibleHeap.HeapRepresents.after_snapshot heaps extension storeTyped appended,
    ran, finalRoot.nativeRead, extension, frame⟩

private def w (n : Nat) : Word := Word.ofNatModulo n
private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Item(Word) }",
    "function probe(seed: Word) returns (Word) { let f = lam(item: Word) { return item; }; return f(seed); }",
    "function selected(root: mapping(Word => Word), key: Word) returns (Word) { return root[key]; }",
    "function missing(root: mapping(Word => Box), key: Word) returns (Box) { return root[key]; }"
  ]}] }

private def exercise (initial : SourceCoreCompatibleValues.Context)
    (ambient : AmbientDefinitions initial.checked.catalog.definitions) (inertStore : Store)
    (source : TypedSource) (carrier : SourceCoreDataValues.Value) (absent : Bool)
    (expected : Option Word) : IO Unit := do
  let (root, key) ← match source.inputs with
    | [root, key] => pure (root, key) | _ => throw (IO.userError "snapshot input layout changed")
  let keyNode ← match source.nodes.findSome? (fun
    | .expression node => match node.form with
      | .reference _ (.local id) => if id == key.id then some node else none
      | _ => none
    | _ => none) with
    | some node => pure node | none => throw (IO.userError "snapshot key occurrence missing")
  let leaf ← match root.scheme.body with
    | .mapping _ value => pure value | _ => throw (IO.userError "snapshot root type changed")
  let encoded ← match SourceCoreCompatibleValues.encode 500 initial root.scheme.body carrier with
    | .ok encoded => pure encoded | .error error => throw (IO.userError s!"snapshot encode: {reprStr error}")
  let context := encoded.context
  let assignment : AssignmentResolution := ⟨⟨root.id, [.index keyNode.id], leaf⟩, []⟩
  let route ← match described : describe context context.checked.signatures source (.occurrence keyNode.id.occurrence) assignment with
    | .ok route =>
      have _description := CompatiblePlaceDescription.of_describe described
      pure route
    | .error error => throw (IO.userError s!"snapshot describe: {reprStr error}")
  let prepared ← match preparedBy : prepare context 300 route (w 900) (fun _ => w 1000) with
    | .ok prepared =>
      have _static := CompatibleMixedPreparation.of_prepare preparedBy
      pure prepared
    | .error error => throw (IO.userError s!"snapshot prepare: {reprStr error}")
  let optional := if absent then Value.inLeft route.rootType .unit else .inRight .unit encoded.value
  let before := inertStore ++ [optional, Value.integer (-99)]
  let environment := [Value.cellRef (OptionalCell.cellType route.rootType) inertStore.length, .word (w 1)]
  let coreContext := [OptionalCell.referenceType route.rootType, .word]
  let code := Expr.apply (getter prepared .word) (.pair (.loadCell (.var 0)) (.var 1))
  require (infer? coreContext code ambient.definitions == some (LanguageResult.resultType prepared.optionalLeaf)) "ambient snapshot checker rejected getter"
  let initialState := State.initial code environment before
  let (actual, after) ← match runStateful 100000 initialState with
    | .done value after => pure (value, after)
    | other => throw (IO.userError s!"ambient snapshot did not finish: {reprStr other}")
  require (after.take before.length == before) "snapshot changed live root or existing indexed cells"
  require (after.length == before.length + initial.checked.catalog.entries.length + 1) "snapshot administrative allocation count changed"
  match expected, actual with
  | some expected, .inRight .word (.inRight .unit (.word value)) => require (value == expected) "snapshot selected wrong duplicate/default"
  | none, .inLeft _ (.word token) =>
    let header ← match encoded.value with
      | .pair (.word header) _ => pure header | _ => throw (IO.userError "snapshot mapping header missing")
    require (token == (w 1000).add header) "snapshot lost exact raw missing-default token"
  | _, _ => throw (IO.userError s!"snapshot unexpected result: {reprStr actual}")
  match runStateful 2 initialState with
  | .outOfFuel checkpoint => require (runStateful 100000 checkpoint == .done actual after) "snapshot resume changed value/store"
  | _ => throw (IO.userError "snapshot fixture did not checkpoint")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"snapshot source: {reprStr error}")
  let requests := program.signatures.functions.map (fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request))
  let plan ← match SourceSpecializationWorklist.run program requests 500 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"snapshot plan: {reprStr other}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 500 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"snapshot base: {reprStr error}")
  let artifact ← match SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"snapshot indexed: {reprStr error}")
  let probe ← match program.signatures.functions.find? (·.name == "probe") with
    | some signature => pure (⟨signature.id, []⟩ : SourceSpecialization.SpecializationKey) | none => throw (IO.userError "snapshot probe missing")
  let completion ← match artifact.runSource probe [.word (w 7)] 100000 500 with
    | .ok completed => pure completed | .error error => throw (IO.userError s!"snapshot probe: {reprStr error}")
  match completion.result.native.observation with
  | .succeeded (.word value) _ => require (value == w 7) "snapshot probe returned wrong value"
  | other => throw (IO.userError s!"snapshot probe failed: {reprStr other}")
  require (!artifact.layouts.entries.isEmpty) "snapshot actual marker suffix absent"
  let before := SourceCoreCallableIndexedLedger.store completion
  let full := CallableIndexedAmbient.ambientDefinitions artifact
  let context := SourceCoreCompatibleValues.Context.initial automatic.checked
  let selectedId ← match program.signatures.functions.find? (·.name == "selected") with
    | some signature => pure signature.id | none => throw (IO.userError "snapshot signature absent")
  let selected ← match plan.specializations.find? (·.key.declaration == selectedId) with
    | some specialized => pure specialized.function.typedBody | none => throw (IO.userError "snapshot selected missing")
  let duplicate := SourceCoreDataValues.Value.mapping (.comptime .word) (.comptime .word)
    [(.word (w 1), .word (w 7)), (.word (w 1), .word (w 9))]
  exercise context full before selected duplicate false (some (w 7))
  exercise context full before selected (.mapping .word .word []) true (some Word.zero)
  let missingId ← match program.signatures.functions.find? (·.name == "missing") with
    | some signature => pure signature.id | none => throw (IO.userError "snapshot signature absent")
  let missing ← match plan.specializations.find? (·.key.declaration == missingId) with
    | some specialized => pure specialized.function.typedBody | none => throw (IO.userError "snapshot missing function absent")
  let box ← match program.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box | none => throw (IO.userError "snapshot Box absent")
  exercise context full before missing (.mapping .word (.nominal box.id []) []) false none
  exercise context full before missing (.mapping .word (.nominal box.id []) []) true none
  IO.println "compatible ambient live-root snapshots GREEN"

end Tests.SourceCoreCompatibleAmbientSnapshot
