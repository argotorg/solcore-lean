import Solcore.Frontend.SourceCoreCallableIndexedRestoration
import Solcore.Frontend.SourceCoreCallableIndexedPrincipalAllocations
import Solcore.Frontend.SourceCoreCallableNativeSubvalues
import Solcore.Frontend.SourceCoreCompatibleOutputs

/-! Prepared output policy for the owning indexed Core runner. Function leaves
must occur in its completed result or a recorded source-cell payload; closure
saved environments are excluded. The actual finite-world typing follows that
path. Lambda code/captures and raw source metadata then use the cached finite
receipts. Named/builtin leaves use the exact installed output recipe.

All source graphs, substitutions, evidence and code templates are prepared
before execution. Runtime decoding locates native data, joins physical source
allocations and selects cached headers/recipes. This boundary does not claim
whole source/Core execution correspondence or import a source evaluator.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableIndexedOutputs
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Program := SourceCoreCallableIndexedPrograms.Prepared
abbrev Completion {checked : Checked} (program : Program checked) := SourceCoreCallableIndexedPrograms.Completion program
abbrev SourceHeap := SourceCoreAllocationLedger.SourceHeap
abbrev SourceValue := SourceTypedRuntime.Value
abbrev Ledger {checked : Checked} {program : Program checked} (completion : Completion program) (initial : SourceHeap) :=
  SourceCoreCallableIndexedLedger.Receipt completion initial
abbrev StoreOf {checked : Checked} {program : Program checked} (completion : Completion program) := SourceCoreCallableIndexedLedger.store completion
abbrev WorldOf {checked : Checked} {program : Program checked} (completion : Completion program) := SourceCoreCallableIndexedLedger.world completion

inductive Error where
  | graph (error : SourceCoreCallableAncestryPairedPreparation.Error)
  | headers (error : SourceCoreCallablePairedHeaders.Error)
  | templates (error : SourceCoreCallableIndexedTemplates.Error)
  | views (error : SourceCoreCallableIndexedReadViews.Error)
  | output (error : SourceCoreCompatibleOutputs.Error)
  | ledger (error : SourceCoreAllocationLedger.Error)
  | projection (error : SourceCoreCompatibleCatalog.Error)
  | restore (error : SourceCoreCallableIndexedRestoration.Error)
  | principal (error : SourceCoreCallableIndexedPrincipalAllocations.Error)
  | unavailableValue
  | notCallable
  | callableTypeMismatch
  | notSucceeded
  deriving Repr

structure Prepared {checked : Checked} (program : Program checked) where private mk ::
  graph : SourceCoreCallableAncestryPairedPreparation.Prepared program.base
  graphPrepared : SourceCoreCallableAncestryPairedPreparation.prepare program.base = .ok graph
  headers : SourceCoreCallablePairedHeaders.Prepared graph
  headersPrepared : SourceCoreCallablePairedHeaders.prepare graph = .ok headers
  templates : SourceCoreCallableIndexedTemplates.Cache program
  templatesPrepared : SourceCoreCallableIndexedTemplates.prepare program = .ok templates
  views : SourceCoreCallableIndexedReadViews.Cache templates
  viewsPrepared : SourceCoreCallableIndexedReadViews.prepare templates = .ok views
  recipe : SourceCoreCompatibleOutputs.Recipe checked program.layouts.definitions
  recipePrepared : SourceCoreCompatibleOutputs.prepareIndexed program = .ok recipe

def prepare {checked : Checked} (program : Program checked) : Except Error (Prepared program) := do
  let graph := program.ancestry.graph
  let graphPrepared := program.ancestry.graphPrepared
  match headersPrepared : SourceCoreCallablePairedHeaders.prepare graph with
  | .error error => throw (.headers error)
  | .ok headers =>
    match templatesPrepared : SourceCoreCallableIndexedTemplates.prepare program with
    | .error error => throw (.templates error)
    | .ok templates =>
      match viewsPrepared : SourceCoreCallableIndexedReadViews.prepare templates with
      | .error error => throw (.views error)
      | .ok views =>
        match recipePrepared : SourceCoreCompatibleOutputs.prepareIndexed program with
        | .error error => throw (.output error)
        | .ok recipe => pure ⟨graph, graphPrepared, headers, headersPrepared, templates, templatesPrepared,
            views, viewsPrepared, recipe, recipePrepared⟩


/-- A native function leaf comes from public result data or an actual source
allocation payload, never arbitrary supplied code or saved environment data. -/
inductive Origin {checked : Checked} {program : Program checked} (completion : Completion program)
    {initial : SourceHeap} (ledger : Ledger completion initial) (value : Core.Value) : Prop where
  | result {root : Core.Value}
      (observation : completion.result.native.observation = .succeeded root (StoreOf completion))
      (inside : SourceCoreCallableNativeSlots.Subvalue value root) : Origin completion ledger value
  | payload (ordinal : Fin ledger.ledger.rows.length) {root : Core.Value}
      (present : (ledger.ledger.rows[ordinal]).payload = some root)
      (inside : SourceCoreCallableNativeSlots.Subvalue value root) : Origin completion ledger value

structure Located {checked : Checked} {program : Program checked} {completion : Completion program}
    {initial : SourceHeap} (ledger : Ledger completion initial) (value : Core.Value) : Type where private mk ::
  origin : Origin completion ledger value
  typed : RuntimeValueHasType (WorldOf completion) value value.type program.layouts.definitions

private def locatePayload {checked : Checked} {program : Program checked} {completion : Completion program}
    {initial : SourceHeap} (ledger : Ledger completion initial) (value : Core.Value) : Option (Located ledger value) :=
  (List.finRange ledger.ledger.rows.length).findSome? fun ordinal =>
    match present : (ledger.ledger.rows[ordinal]).payload with
    | none => none
    | some root => match SourceCoreCallableNativeSubvalues.find value root with
      | none => none
      | some inside => some ⟨.payload ordinal present inside.related,
          SourceCoreCallableNativeSubvalues.runtime_typed inside.related
            ((ledger.ledger.rows[ordinal]).payload_typed ledger.typed present)⟩

def locate {checked : Checked} {program : Program checked} (completion : Completion program)
    {initial : SourceHeap} (ledger : Ledger completion initial) (value : Core.Value) : Except Error (Located ledger value) :=
  match observed : completion.result.native.observation with
  | .succeeded root store =>
    match SourceCoreCallableNativeSubvalues.find value root with
    | some inside =>
      have storeExact : StoreOf completion = store := by
        simp only [StoreOf, SourceCoreCallableIndexedLedger.store,
          SourceCoreCompatibleMarkedLedger.observedStore, observed]
      have rootTyped : RuntimeValueHasType (WorldOf completion) root completion.entry.native.resultType program.layouts.definitions := by
        obtain ⟨world, stored, typed⟩ := completion.result.native.success_typed observed
        have equal := stored.world_eq
        subst world
        simpa only [WorldOf, SourceCoreCallableIndexedLedger.world, ← storeExact] using typed
      .ok ⟨.result (by simpa only [storeExact] using observed) inside.related,
        SourceCoreCallableNativeSubvalues.runtime_typed inside.related rootTyped⟩
    | none => match locatePayload ledger value with | some found => .ok found | none => .error .unavailableValue
  | _ => match locatePayload ledger value with | some found => .ok found | none => .error .unavailableValue

structure SnapshotAt {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) where private mk ::
  snapshot : SourceCoreCompatibleOutputs.Snapshot prepared.recipe
  exact : snapshot.store = StoreOf completion

def snapshot {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) : Except Error (SnapshotAt prepared completion) :=
  match accepted : SourceCoreCompatibleOutputs.snapshot prepared.recipe (StoreOf completion)
      (SourceCoreCallableIndexedLedger.store_typed completion) with
  | .error error => .error (.output error)
  | .ok snapshot => .ok ⟨snapshot, SourceCoreCompatibleOutputs.snapshot_store accepted⟩

/-- Sealed source reconstructions retain the distinct native origin, code,
physical capture join and cached metadata selection of their function leaves. -/
inductive LeafRelated {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) {initial : SourceHeap} (ledger : Ledger completion initial)
    (expected : TypeSystem.Ty) (value : Core.Value) : SourceValue → Prop where
  | ordinary (located : Located ledger value)
      (authenticated : SourceCoreCallableIndexedTemplates.Authenticated prepared.templates (WorldOf completion) (StoreOf completion) value)
      (restored : SourceCoreCallableIndexedRestoration.Ordinary prepared.headers authenticated ledger) :
      LeafRelated prepared completion ledger expected value restored.source
  | read (located : Located ledger value)
      (authenticated : SourceCoreCallableIndexedReadViews.Authenticated prepared.views (WorldOf completion) (StoreOf completion) value)
      (restored : SourceCoreCallableIndexedRestoration.Read prepared.headers authenticated ledger) :
      LeafRelated prepared completion ledger expected value restored.source
  | known (located : Located ledger value) (snapshot : SnapshotAt prepared completion)
      {source : SourceValue} (decoded : SourceCoreCompatibleOutputs.decodeCallable prepared.recipe expected value = .ok source) :
      LeafRelated prepared completion ledger expected value source

structure Leaf {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} {ledger : Ledger completion initial}
    (expected : TypeSystem.Ty) (value : Core.Value) : Type where private mk ::
  source : SourceValue
  type : Core.Ty
  projected : checked.catalog.project expected = .ok type
  typed : RuntimeValueHasType (WorldOf completion) value type program.layouts.definitions
  related : LeafRelated prepared completion ledger expected value source

def decodeLeaf {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) {initial : SourceHeap} (ledger : Ledger completion initial)
    (snapshot : SnapshotAt prepared completion) (expected : TypeSystem.Ty) (value : Core.Value) :
    Except Error (Leaf (prepared := prepared) (completion := completion) (ledger := ledger) expected value) := do
  let located ← locate completion ledger value
  let .product (.product (.sum .unit .word) (.function parameter (.sum .word result))) .word := value.type
    | throw .notCallable
  match projected : checked.catalog.project expected with
  | .error error => throw (.projection error)
  | .ok type =>
    if same : type = CallableContract.functionType parameter result then
      if valueType : value.type = CallableContract.functionType parameter result then
        have typed : RuntimeValueHasType (WorldOf completion) value (CallableContract.functionType parameter result) program.layouts.definitions :=
          valueType ▸ located.typed
        have expectedTyped : RuntimeValueHasType (WorldOf completion) value type program.layouts.definitions := same.symm ▸ typed
        let stored := SourceCoreCallableIndexedLedger.store_typed completion
        match SourceCoreCallableIndexedReadViews.authenticate prepared.views stored value parameter result typed with
        | .ok authenticated =>
          let restored ← (SourceCoreCallableIndexedRestoration.restoreRead prepared.headers authenticated ledger).mapError Error.restore
          pure ⟨restored.source, type, projected, expectedTyped, .read located authenticated restored⟩
        | .error _ =>
          match SourceCoreCallableIndexedTemplates.authenticate prepared.templates stored value parameter result typed with
          | .ok authenticated =>
            let restored ← (SourceCoreCallableIndexedRestoration.restoreOrdinary prepared.headers authenticated ledger).mapError Error.restore
            pure ⟨restored.source, type, projected, expectedTyped, .ordinary located authenticated restored⟩
          | .error _ =>
            match decoded : SourceCoreCompatibleOutputs.decodeCallable prepared.recipe expected value with
            | .error error => throw (.output error)
            | .ok source => pure ⟨source, type, projected, expectedTyped, .known located snapshot decoded⟩
      else throw .callableTypeMismatch
    else throw .callableTypeMismatch

/-- Structural decoding delegates each actual function leaf to this owned
policy. Its checked `Leaf` factory can be inspected separately by consumers. -/
def leafPolicy {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) {initial : SourceHeap} (ledger : Ledger completion initial)
    (snapshot : SnapshotAt prepared completion) : SourceCoreCompatibleOutputs.LeafDecoder := fun expected value =>
  (decodeLeaf prepared completion ledger snapshot expected value).map (·.source)
    |>.mapError (fun _ => ⟨[], .callablePayloadMismatch⟩)

abbrev Data {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} (ledger : Ledger completion initial)
    (snapshot : SnapshotAt prepared completion) (expected : TypeSystem.Ty) (value : Core.Value) :=
  SourceCoreCompatibleOutputs.LeafDecoded (leafPolicy prepared completion ledger snapshot)
    prepared.recipe snapshot.snapshot completion.result.context expected value

def decodeData {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) {initial : SourceHeap} (ledger : Ledger completion initial)
    (snapshot : SnapshotAt prepared completion) (expected : TypeSystem.Ty) (value : Core.Value)
    (type : Core.Ty) (projected : checked.catalog.project expected = .ok type)
    (typed : RuntimeValueHasType (WorldOf completion) value type program.layouts.definitions)
    (fuel : Nat := 1024) : Except Error (Data ledger snapshot expected value) := do
  have actual : RuntimeValueHasType (snapshot.snapshot.store.map Core.Value.type) value type program.layouts.definitions := by
    rw [snapshot.exact]
    exact typed
  (SourceCoreCompatibleOutputs.decodeWithLeaves (leafPolicy prepared completion ledger snapshot)
    prepared.recipe snapshot.snapshot completion.result.context completion.result.contextOwner expected value type projected actual fuel)
      |>.mapError Error.output

structure Success {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) (initial : SourceHeap) (expected : TypeSystem.Ty) where private mk ::
  ledger : Ledger completion initial
  snapshot : SnapshotAt prepared completion
  core : Core.Value
  observation : completion.result.native.observation = .succeeded core (StoreOf completion)
  decoded : Data ledger snapshot expected core

/-- Consume a native successful observation without running or resuming source
code. Deep function leaves keep the same owning completion and typed ledger. -/
def decodeSuccess {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) (expected : TypeSystem.Ty)
    (projected : checked.catalog.project expected = .ok completion.entry.native.resultType)
    (initial : SourceHeap := []) (fuel : Nat := 1024) : Except Error (Success prepared completion initial expected) := do
  let ledger ← (SourceCoreCallableIndexedLedger.scan completion initial).mapError Error.ledger
  let snapshot ← snapshot prepared completion
  match observed : completion.result.native.observation with
  | .succeeded value store =>
    have storeExact : StoreOf completion = store := by
      simp only [StoreOf, SourceCoreCallableIndexedLedger.store,
        SourceCoreCompatibleMarkedLedger.observedStore, observed]
    have typed : RuntimeValueHasType (WorldOf completion) value completion.entry.native.resultType program.layouts.definitions := by
      obtain ⟨world, stored, typed⟩ := completion.result.native.success_typed observed
      have equal := stored.world_eq
      subst world
      simpa only [WorldOf, SourceCoreCallableIndexedLedger.world, ← storeExact] using typed
    let decoded ← decodeData prepared completion ledger snapshot expected value completion.entry.native.resultType projected typed fuel
    pure ⟨ledger, snapshot, value, by simpa only [storeExact] using observed, decoded⟩
  | _ => throw .notSucceeded

end Solcore.Frontend.SourceCoreCallableIndexedOutputs
