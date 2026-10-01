import Solcore.Frontend.SourceCoreCallableIndexedHeapOutputs

/-! Raw source cell reconstruction from an owned indexed program's current
typed store. This is a migration adapter, independent of seed completion.
Function leaves must be subvalues of actual allocation payloads. Cached exact
templates, read recipes, capture joins and installed named slots authenticate
their source reconstruction. No source body is traversed or evaluated.

The resulting heap still needs the existing deep source validator before it
can become an opaque inert prefix. These receipts establish reconstruction and
native provenance; they do not assert whole execution correspondence. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreIndexedHeapMigration
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Program := SourceCoreCallableIndexedPrograms.Prepared
abbrev Prepared {checked : Checked} (program : Program checked) := SourceCoreCallableIndexedHeapOutputs.Prepared program
abbrev Values := SourceCoreCompatibleValues.Context
abbrev SourceHeap := SourceCoreAllocationLedger.SourceHeap
abbrev SourceCell := SourceTypedRuntime.Cell
abbrev SourceValue := SourceTypedRuntime.Value
abbrev Ledger {checked : Checked} (program : Program checked) (initial : SourceHeap) (world : StoreTyping) (store : Store) :=
  SourceCoreAllocationLedger.TypedLedger program.layouts initial world store

inductive Error where
  | output (error : SourceCoreCompatibleOutputs.Error)
  | projection (error : SourceCoreCompatibleCatalog.Error)
  | restore (error : SourceCoreCallableIndexedRestoration.Error)
  | principal (error : SourceCoreCallableIndexedPrincipalAllocations.Error)
  | header (error : SourceCoreCallableIndexedCellHeaders.Error)
  | unavailableLeaf
  | notCallable
  | typeMismatch (expected actual : Core.Ty)
  | rawTypeMismatch (expected actual : TypeSystem.Ty)
  deriving Repr

structure Located {checked : Checked} {program : Program checked} {initial : SourceHeap}
    {world : StoreTyping} {store : Store} (ledger : Ledger program initial world store) (value : Core.Value) where private mk ::
  ordinal : Fin ledger.ledger.rows.length
  root : Core.Value
  present : (ledger.ledger.rows[ordinal]).payload = some root
  inside : SourceCoreCallableNativeSlots.Subvalue value root
  typed : RuntimeValueHasType world value value.type program.layouts.definitions

def locate {checked : Checked} {program : Program checked} {initial : SourceHeap}
    {world : StoreTyping} {store : Store} (ledger : Ledger program initial world store) (value : Core.Value) :
    Except Error (Located ledger value) :=
  match (List.finRange ledger.ledger.rows.length).findSome? (fun ordinal =>
    match present : (ledger.ledger.rows[ordinal]).payload with
    | none => none
    | some root => match SourceCoreCallableNativeSubvalues.find value root with
      | none => none
      | some inside => some (⟨ordinal, root, present, inside.related,
          SourceCoreCallableNativeSubvalues.runtime_typed inside.related
            ((ledger.ledger.rows[ordinal]).payload_typed ledger.typed present)⟩ : Located ledger value)) with
  | none => .error .unavailableLeaf
  | some located => .ok located

inductive LeafRelated {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {initial : SourceHeap} {world : StoreTyping} {store : Store} (ledger : Ledger program initial world store)
    (expected : TypeSystem.Ty) (value : Core.Value) : SourceValue → Prop where
  | ordinary (located : Located ledger value)
      (authenticated : SourceCoreCallableIndexedTemplates.Authenticated prepared.output.templates world store value)
      (restored : SourceCoreCallableIndexedRestoration.Ordinary prepared.output.headers authenticated ledger) :
      LeafRelated prepared ledger expected value restored.source
  | read (located : Located ledger value)
      (authenticated : SourceCoreCallableIndexedReadViews.Authenticated prepared.output.views world store value)
      (restored : SourceCoreCallableIndexedRestoration.Read prepared.output.headers authenticated ledger) :
      LeafRelated prepared ledger expected value restored.source
  | known (located : Located ledger value)
      {source : SourceValue}
      (decoded : SourceCoreCompatibleOutputs.decodeCallable prepared.output.recipe expected value = .ok source) :
      LeafRelated prepared ledger expected value source

structure Leaf {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {initial : SourceHeap} {world : StoreTyping} {store : Store} {ledger : Ledger program initial world store}
    (expected : TypeSystem.Ty) (value : Core.Value) where private mk ::
  source : SourceValue
  type : Core.Ty
  projected : checked.catalog.project expected = .ok type
  typed : RuntimeValueHasType world value type program.layouts.definitions
  related : LeafRelated prepared ledger expected value source

def decodeLeaf {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {initial : SourceHeap} {world : StoreTyping} {store : Store} (ledger : Ledger program initial world store)
    (expected : TypeSystem.Ty) (value : Core.Value) : Except Error (Leaf (prepared := prepared) (ledger := ledger) expected value) := do
  let located ← locate ledger value
  let .product (.product (.sum .unit .word) (.function parameter (.sum .word result))) .word := value.type
    | throw .notCallable
  match projected : checked.catalog.project expected with
  | .error error => throw (.projection error)
  | .ok type =>
    if same : type = CallableContract.functionType parameter result then
      if valueType : value.type = CallableContract.functionType parameter result then
        have typed : RuntimeValueHasType world value (CallableContract.functionType parameter result) program.layouts.definitions :=
          valueType ▸ located.typed
        have expectedTyped : RuntimeValueHasType world value type program.layouts.definitions := same.symm ▸ typed
        match SourceCoreCallableIndexedReadViews.authenticate prepared.output.views ledger.typed value parameter result typed with
        | .ok authenticated =>
          let restored ← (SourceCoreCallableIndexedRestoration.restoreRead prepared.output.headers authenticated ledger).mapError Error.restore
          pure ⟨restored.source, type, projected, expectedTyped, .read located authenticated restored⟩
        | .error _ =>
          match SourceCoreCallableIndexedTemplates.authenticate prepared.output.templates ledger.typed value parameter result typed with
          | .ok authenticated =>
            let restored ← (SourceCoreCallableIndexedRestoration.restoreOrdinary prepared.output.headers authenticated ledger).mapError Error.restore
            pure ⟨restored.source, type, projected, expectedTyped, .ordinary located authenticated restored⟩
          | .error _ =>
            match decoded : SourceCoreCompatibleOutputs.decodeCallable prepared.output.recipe expected value with
            | .error error => throw (.output error)
            | .ok source => pure ⟨source, type, projected, expectedTyped, .known located decoded⟩
      else throw (.typeMismatch (CallableContract.functionType parameter result) value.type)
    else throw (.typeMismatch (CallableContract.functionType parameter result) type)

def leafPolicy {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {initial : SourceHeap} {world : StoreTyping} {store : Store} (ledger : Ledger program initial world store) :
    SourceCoreCompatibleOutputs.LeafDecoder := fun expected value =>
  (decodeLeaf prepared ledger expected value).map (·.source) |>.mapError (fun _ => ⟨[], .callablePayloadMismatch⟩)

structure NativeSnapshot {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {world : StoreTyping} {store : Store} where private mk ::
  snapshot : SourceCoreCompatibleOutputs.Snapshot prepared.output.recipe
  exact : snapshot.store = store

def nativeSnapshot {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {world : StoreTyping} {store : Store} (stored : RuntimeStoreHasTypes world store program.layouts.definitions) :
    Except Error (NativeSnapshot (world := world) (store := store) prepared) :=
  match accepted : SourceCoreCompatibleOutputs.snapshot prepared.output.recipe store
      (by simpa only [stored.world_eq] using stored) with
  | .error error => .error (.output error)
  | .ok snapshot => .ok ⟨snapshot, SourceCoreCompatibleOutputs.snapshot_store accepted⟩

inductive CellRelated {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {initial : SourceHeap} {world : StoreTyping} {store : Store} (ledger : Ledger program initial world store)
    (snapshot : NativeSnapshot (world := world) (store := store) prepared) (values : Values)
    (row : SourceCoreAllocationLedger.Row program.layouts store) : SourceCell → Prop where
  | absent (selected : SourceCoreCallableIndexedCellHeaders.Selected prepared.headers row)
      (mono : selected.header.raw.binder.scheme.quantified = []) (absent : row.payload = none) :
      CellRelated prepared ledger snapshot values row ⟨selected.header.raw.binder.scheme.body, none⟩
  | present (selected : SourceCoreCallableIndexedCellHeaders.Selected prepared.headers row)
      (mono : selected.header.raw.binder.scheme.quantified = [])
      {value : Core.Value} (present : row.payload = some value)
      (decoded : SourceCoreCompatibleOutputs.LeafDecoded (leafPolicy prepared ledger)
        prepared.output.recipe snapshot.snapshot values selected.header.raw.binder.scheme.body value) :
      CellRelated prepared ledger snapshot values row ⟨selected.header.raw.binder.scheme.body, some decoded.source⟩
  | principal (selected : SourceCoreCallableIndexedCellHeaders.Selected prepared.headers row)
      (generic : selected.header.raw.binder.scheme.quantified ≠ [])
      (restored : SourceCoreCallableIndexedPrincipalAllocations.Restored prepared.output.headers row)
      (rawType : restored.cell.type = selected.header.raw.binder.scheme.body) :
      CellRelated prepared ledger snapshot values row restored.cell

structure CellDecoded {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {initial : SourceHeap} {world : StoreTyping} {store : Store} {ledger : Ledger program initial world store}
    {snapshot : NativeSnapshot (world := world) (store := store) prepared} {values : Values}
    (row : SourceCoreAllocationLedger.Row program.layouts store) where private mk ::
  cell : SourceCell
  related : CellRelated prepared ledger snapshot values row cell

def decodeCell {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {initial : SourceHeap} {world : StoreTyping} {store : Store} (ledger : Ledger program initial world store)
    (snapshot : NativeSnapshot (world := world) (store := store) prepared)
    (values : Values) (owner : values.checked = checked)
    (row : SourceCoreAllocationLedger.Row program.layouts store) (fuel : Nat) :
    Except Error (CellDecoded (prepared := prepared) (ledger := ledger) (snapshot := snapshot) (values := values) row) := do
  let selected ← (SourceCoreCallableIndexedCellHeaders.select prepared.headers row).mapError Error.header
  if mono : selected.header.raw.binder.scheme.quantified = [] then
    match present : row.payload with
    | none => pure ⟨⟨selected.header.raw.binder.scheme.body, none⟩, .absent selected mono present⟩
    | some value =>
      match projected : checked.catalog.project selected.header.raw.binder.scheme.body with
      | .error error => throw (.projection error)
      | .ok type =>
        if same : type = row.entry.key.payloadType then
          have typed : RuntimeValueHasType (snapshot.snapshot.store.map Core.Value.type) value type program.layouts.definitions := by
            rw [snapshot.exact, ← ledger.typed.world_eq, same]
            exact row.payload_typed ledger.typed present
          let decoded ← (SourceCoreCompatibleOutputs.decodeWithLeaves (leafPolicy prepared ledger) prepared.output.recipe
            snapshot.snapshot values owner selected.header.raw.binder.scheme.body value type projected typed fuel).mapError Error.output
          pure ⟨⟨selected.header.raw.binder.scheme.body, some decoded.source⟩, .present selected mono present decoded⟩
        else throw (.typeMismatch row.entry.key.payloadType type)
  else
    let restored ← (SourceCoreCallableIndexedPrincipalAllocations.restore prepared.output.headers row).mapError Error.principal
    if rawType : restored.cell.type = selected.header.raw.binder.scheme.body then
      pure ⟨restored.cell, .principal selected mono restored rawType⟩
    else throw (.rawTypeMismatch selected.header.raw.binder.scheme.body restored.cell.type)

inductive CellsRelated {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {initial : SourceHeap} {world : StoreTyping} {store : Store} (ledger : Ledger program initial world store)
    (snapshot : NativeSnapshot (world := world) (store := store) prepared) (values : Values) :
    List (SourceCoreAllocationLedger.Row program.layouts store) → SourceHeap → Prop where
  | nil : CellsRelated prepared ledger snapshot values [] []
  | cons {row rows cell cells} (head : CellRelated prepared ledger snapshot values row cell)
      (tail : CellsRelated prepared ledger snapshot values rows cells) :
      CellsRelated prepared ledger snapshot values (row :: rows) (cell :: cells)

theorem CellsRelated.length {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {initial : SourceHeap} {world : StoreTyping} {store : Store} {ledger : Ledger program initial world store}
    {snapshot : NativeSnapshot (world := world) (store := store) prepared} {values : Values} {rows : List _} {cells : SourceHeap}
    (related : CellsRelated prepared ledger snapshot values rows cells) : cells.length = rows.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simpa only [List.length_cons] using congrArg Nat.succ ih

structure CellsDecoded {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {initial : SourceHeap} {world : StoreTyping} {store : Store} {ledger : Ledger program initial world store}
    {snapshot : NativeSnapshot (world := world) (store := store) prepared} {values : Values}
    (rows : List (SourceCoreAllocationLedger.Row program.layouts store)) where private mk ::
  cells : SourceHeap
  related : CellsRelated prepared ledger snapshot values rows cells

def decodeCells {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {initial : SourceHeap} {world : StoreTyping} {store : Store} (ledger : Ledger program initial world store)
    (snapshot : NativeSnapshot (world := world) (store := store) prepared) (values : Values)
    (owner : values.checked = checked) (fuel : Nat) :
    (rows : List (SourceCoreAllocationLedger.Row program.layouts store)) →
    Except Error (CellsDecoded (prepared := prepared) (ledger := ledger) (snapshot := snapshot) (values := values) rows)
  | [] => pure ⟨[], .nil⟩
  | row :: rows => do
    let head ← decodeCell prepared ledger snapshot values owner row fuel
    let tail ← decodeCells prepared ledger snapshot values owner fuel rows
    pure ⟨head.cell :: tail.cells, .cons head.related tail.related⟩

structure Export {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {initial : SourceHeap} {world : StoreTyping} {store : Store} (ledger : Ledger program initial world store)
    (values : Values) where private mk ::
  snapshot : NativeSnapshot (world := world) (store := store) prepared
  decoded : CellsDecoded (prepared := prepared) (ledger := ledger) (snapshot := snapshot) (values := values) ledger.ledger.rows

def Export.heap {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {initial : SourceHeap} {world : StoreTyping} {store : Store} {ledger : Ledger program initial world store} {values : Values}
    (exported : Export prepared ledger values) : SourceHeap := initial ++ exported.decoded.cells

def exportHeap {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {initial : SourceHeap} {world : StoreTyping} {store : Store} (ledger : Ledger program initial world store)
    (values : Values) (owner : values.checked = checked) (fuel : Nat) : Except Error (Export prepared ledger values) := do
  let snapshot ← nativeSnapshot prepared ledger.typed
  let decoded ← decodeCells prepared ledger snapshot values owner fuel ledger.ledger.rows
  pure ⟨snapshot, decoded⟩

theorem Export.length {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {initial : SourceHeap} {world : StoreTyping} {store : Store} {ledger : Ledger program initial world store} {values : Values}
    (exported : Export prepared ledger values) : exported.heap.length = initial.length + ledger.ledger.rows.length := by
  simp only [Export.heap, List.length_append]
  rw [exported.decoded.related.length]

theorem Export.prefix {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {initial : SourceHeap} {world : StoreTyping} {store : Store} {ledger : Ledger program initial world store} {values : Values}
    (exported : Export prepared ledger values) : exported.heap.take initial.length = initial := by
  simp [Export.heap]

end Solcore.Frontend.SourceCoreIndexedHeapMigration
