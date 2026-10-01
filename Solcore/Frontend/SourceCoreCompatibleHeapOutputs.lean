import Solcore.Frontend.SourceCoreCompatibleOutputs
import Solcore.Frontend.SourceCoreCompatibleMarkedLedger

/-! Export the completed monomorphic source cells of an owned marked artifact.
Original binder types, source locations and capture metadata are retained.
Present values use the real compatible output decoder and actual typed store;
absent values need no native-value decoding. The initial source heap is opaque.

Generalized principal bundles and lambda reconstruction remain explicit
unsupported boundaries. No source evaluator or whole-program correspondence
is assumed or introduced. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCompatibleHeapOutputs
open SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Marked := SourceCoreCompatibleMarkedFunctions.Prepared
abbrev Completion {checked : Checked} (marked : Marked checked) :=
  SourceCoreCompatibleMarkedFunctions.Completion marked
abbrev SourceHeap := SourceCoreAllocationLedger.SourceHeap
abbrev Cell := SourceTypedRuntime.Cell
abbrev Row {checked : Checked} {marked : Marked checked} (completion : Completion marked) :=
  SourceCoreAllocationLedger.Row marked.layouts (SourceCoreCompatibleMarkedLedger.store completion)

inductive Error where
  | ledger (error : SourceCoreAllocationLedger.Error)
  | output (error : SourceCoreCompatibleOutputs.Error)
  | generalizedBinding (location : SourceTypedRuntime.Location) (binder : Resolved.LocalId)
  | projection (location : SourceTypedRuntime.Location) (error : SourceCoreCompatibleCatalog.Error)
  | payloadTypeMismatch (location : SourceTypedRuntime.Location) (projected actual : Core.Ty)
  | snapshotUnavailable
  deriving Repr

structure Prepared {checked : Checked} (marked : Marked checked) where private mk ::
  recipe : SourceCoreCompatibleOutputs.Recipe checked marked.layouts.definitions
  authenticated : SourceCoreCompatibleOutputs.prepareMarked marked = .ok recipe

def prepare {checked : Checked} (marked : Marked checked) : Except Error (Prepared marked) :=
  match authenticated : SourceCoreCompatibleOutputs.prepareMarked marked with
  | .error error => .error (.output error)
  | .ok recipe => .ok ⟨recipe, authenticated⟩

structure SnapshotAt {checked : Checked} {marked : Marked checked}
    (prepared : Prepared marked) (completion : Completion marked) where
  snapshot : SourceCoreCompatibleOutputs.Snapshot prepared.recipe
  storeExact : snapshot.store = SourceCoreCompatibleMarkedLedger.store completion

private def snapshot {checked : Checked} {marked : Marked checked}
    (prepared : Prepared marked) (completion : Completion marked) : Except Error (SnapshotAt prepared completion) :=
  match accepted : SourceCoreCompatibleOutputs.snapshot prepared.recipe
      (SourceCoreCompatibleMarkedLedger.store completion) (SourceCoreCompatibleMarkedLedger.store_typed completion) with
  | .error error => .error (.output error)
  | .ok snapshot => .ok ⟨snapshot, SourceCoreCompatibleOutputs.snapshot_store accepted⟩

def rawType {checked : Checked} {marked : Marked checked} {completion : Completion marked}
    (row : Row completion) : TypeSystem.Ty := row.entry.key.binder.scheme.body

/-- The present case retains the actual output decoder's sealed receipt.
Its source value is not inferred from native type preservation alone. -/
inductive CellDecoded {checked : Checked} {marked : Marked checked}
    (prepared : Prepared marked) (completion : Completion marked) (row : Row completion) : Cell → Prop where
  | absent (monomorphic : row.entry.key.binder.scheme.quantified = [])
      (missing : row.payload = none) : CellDecoded prepared completion row ⟨rawType row, none⟩
  | present {value : Core.Value}
      (monomorphic : row.entry.key.binder.scheme.quantified = [])
      (present : row.payload = some value)
      (snapshot : SnapshotAt prepared completion)
      (decoded : SourceCoreCompatibleOutputs.Decoded prepared.recipe snapshot.snapshot
        completion.result.context (rawType row) value) :
      CellDecoded prepared completion row ⟨rawType row, some decoded.source⟩

theorem CellDecoded.type_exact {checked : Checked} {marked : Marked checked}
    {prepared : Prepared marked} {completion : Completion marked} {row : Row completion} {cell : Cell}
    (decoded : CellDecoded prepared completion row cell) : cell.type = rawType row := by
  cases decoded <;> rfl

theorem CellDecoded.monomorphic {checked : Checked} {marked : Marked checked}
    {prepared : Prepared marked} {completion : Completion marked} {row : Row completion} {cell : Cell}
    (decoded : CellDecoded prepared completion row cell) : row.entry.key.binder.scheme.quantified = [] := by
  cases decoded with
  | absent monomorphic _ => exact monomorphic
  | present monomorphic _ _ _ => exact monomorphic

theorem CellDecoded.initialized_projection {checked : Checked} {marked : Marked checked}
    {prepared : Prepared marked} {completion : Completion marked} {row : Row completion} {cell : Cell}
    (decoded : CellDecoded prepared completion row cell) {value : Core.Value}
    (present : row.payload = some value) :
    checked.catalog.project (rawType row) = .ok row.entry.key.payloadType := by
  cases decoded with
  | absent _ missing => rw [missing] at present; contradiction
  | present _ actual snapshot decoded =>
    have same := Option.some.inj (actual.symm.trans present)
    subst value
    have original := row.payload_typed (SourceCoreCompatibleMarkedLedger.store_typed completion) actual
    have typeEq := decoded.typed.type_eq.symm.trans original.type_eq
    rw [← typeEq]
    exact decoded.projected

private def decodeCell {checked : Checked} {marked : Marked checked}
    (prepared : Prepared marked) (completion : Completion marked)
    (available : Option (SnapshotAt prepared completion)) (fuel : Nat) (row : Row completion) :
    Except Error {cell : Cell // CellDecoded prepared completion row cell} := do
  if monomorphic : row.entry.key.binder.scheme.quantified = [] then
    match present : row.payload with
    | none => pure ⟨⟨rawType row, none⟩, .absent monomorphic present⟩
    | some value =>
      match projected : checked.catalog.project (rawType row) with
      | .error error => throw (.projection row.sourceLocation error)
      | .ok type =>
        if same : type = row.entry.key.payloadType then
          let snapshot ← match available with
            | none => throw .snapshotUnavailable
            | some snapshot => pure snapshot
          let typed : Core.RuntimeValueHasType (snapshot.snapshot.store.map Core.Value.type)
              value row.entry.key.payloadType marked.layouts.definitions := by
            rw [snapshot.storeExact]
            exact row.payload_typed (SourceCoreCompatibleMarkedLedger.store_typed completion) present
          let decoded ← (SourceCoreCompatibleOutputs.decode prepared.recipe snapshot.snapshot
            completion.result.context completion.result.contextOwner (rawType row) value row.entry.key.payloadType
            (by simpa only [same] using projected) typed fuel).mapError Error.output
          pure ⟨⟨rawType row, some decoded.source⟩, .present monomorphic present snapshot decoded⟩
        else throw (.payloadTypeMismatch row.sourceLocation type row.entry.key.payloadType)
  else throw (.generalizedBinding row.sourceLocation row.entry.key.binder.id)

private def cell {checked : Checked} {marked : Marked checked}
    (prepared : Prepared marked) (completion : Completion marked)
    (available : Option (SnapshotAt prepared completion)) (fuel : Nat) (row : Row completion) : Except Error Cell :=
  (decodeCell prepared completion available fuel row).map Subtype.val

inductive CellsDecoded {checked : Checked} {marked : Marked checked}
    (prepared : Prepared marked) (completion : Completion marked) : List (Row completion) → List Cell → Prop where
  | nil : CellsDecoded prepared completion [] []
  | cons {row : Row completion} {rows : List (Row completion)} {cell : Cell} {cells : List Cell}
      (head : CellDecoded prepared completion row cell)
      (tail : CellsDecoded prepared completion rows cells) :
      CellsDecoded prepared completion (row :: rows) (cell :: cells)

private theorem cells_sound {checked : Checked} {marked : Marked checked}
    (prepared : Prepared marked) (completion : Completion marked)
    (available : Option (SnapshotAt prepared completion)) (fuel : Nat)
    {rows : List (Row completion)} {cells : List Cell}
    (accepted : rows.mapM (cell prepared completion available fuel) = .ok cells) :
    CellsDecoded prepared completion rows cells := by
  induction rows generalizing cells with
  | nil => simp at accepted; subst cells; exact .nil
  | cons row rows ih =>
    cases head : decodeCell prepared completion available fuel row with
    | error error => simp [List.mapM_cons, cell, head, Except.map, bind, Except.bind] at accepted
    | ok decoded =>
      cases tail : rows.mapM (cell prepared completion available fuel) with
      | error error => simp [List.mapM_cons, cell, head, Except.map, bind, Except.bind, tail] at accepted
      | ok rest =>
        simp only [List.mapM_cons, cell, head, Except.map, bind, Except.bind, tail, pure, Except.pure,
          Except.ok.injEq] at accepted
        subst cells
        exact .cons decoded.property (ih tail)

theorem CellsDecoded.types_exact {checked : Checked} {marked : Marked checked}
    {prepared : Prepared marked} {completion : Completion marked} {rows : List (Row completion)} {cells : List Cell}
    (decoded : CellsDecoded prepared completion rows cells) : cells.map (·.type) = rows.map rawType := by
  induction decoded with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, head.type_exact, ih]

theorem CellsDecoded.length {checked : Checked} {marked : Marked checked}
    {prepared : Prepared marked} {completion : Completion marked} {rows : List (Row completion)} {cells : List Cell}
    (decoded : CellsDecoded prepared completion rows cells) : cells.length = rows.length := by
  induction decoded <;> simp_all

theorem CellsDecoded.lookup {checked : Checked} {marked : Marked checked}
    {prepared : Prepared marked} {completion : Completion marked} {rows : List (Row completion)} {cells : List Cell}
    (decoded : CellsDecoded prepared completion rows cells) {index : Nat} {row : Row completion}
    (found : rows[index]? = some row) :
    ∃ cell, cells[index]? = some cell ∧ CellDecoded prepared completion row cell := by
  induction decoded generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst row; exact ⟨_, rfl, head⟩
    | succ index => exact ih found

structure Export {checked : Checked} {marked : Marked checked}
    (prepared : Prepared marked) (completion : Completion marked) (initial : SourceHeap) where private mk ::
  receipt : SourceCoreCompatibleMarkedLedger.Receipt completion initial
  snapshot : Option (SnapshotAt prepared completion)
  cells : List Cell
  decoded : CellsDecoded prepared completion receipt.ledger.rows cells
  private fuel : Nat
  private exported : receipt.ledger.exportHeap (cell prepared completion snapshot fuel) = .ok (initial ++ cells)

def Export.heap {checked : Checked} {marked : Marked checked}
    {prepared : Prepared marked} {completion : Completion marked} {initial : SourceHeap}
    (exported : Export prepared completion initial) : SourceHeap := initial ++ exported.cells

/-- Empty/absent cell lists need no installed callable snapshot. In
particular, early fuel checkpoints retain their opaque prefix even before
the administrative globals have finished installation. -/
def exportHeap {checked : Checked} {marked : Marked checked}
    (prepared : Prepared marked) (completion : Completion marked) (initial : SourceHeap := []) (fuel : Nat := 1024) :
    Except Error (Export prepared completion initial) := do
  let receipt ← (SourceCoreCompatibleMarkedLedger.scan completion initial).mapError Error.ledger
  let available ← if receipt.ledger.rows.any (fun row => row.payload.isSome) then
      some <$> snapshot prepared completion
    else pure none
  match accepted : receipt.ledger.rows.mapM (cell prepared completion available fuel) with
  | .error error => throw error
  | .ok cells =>
    pure ⟨receipt, available, cells, cells_sound prepared completion available fuel accepted, fuel, by
      simp [SourceCoreAllocationLedger.Ledger.exportHeap, accepted, Functor.map, Except.map]⟩

theorem Export.prefix_exact {checked : Checked} {marked : Marked checked}
    {prepared : Prepared marked} {completion : Completion marked} {initial : SourceHeap}
    (exported : Export prepared completion initial) : exported.heap.take initial.length = initial := by
  exact exported.receipt.ledger.exportHeap_prefix _ exported.exported

theorem Export.length_exact {checked : Checked} {marked : Marked checked}
    {prepared : Prepared marked} {completion : Completion marked} {initial : SourceHeap}
    (exported : Export prepared completion initial) :
    exported.heap.length = initial.length + exported.receipt.ledger.rows.length := by
  simp only [heap, List.length_append, exported.decoded.length]

theorem Export.cell_at_sourceLocation {checked : Checked} {marked : Marked checked}
    {prepared : Prepared marked} {completion : Completion marked} {initial : SourceHeap}
    (exported : Export prepared completion initial) (index : Fin exported.receipt.ledger.rows.length) :
    ∃ cell, exported.heap[(exported.receipt.ledger.rows[index]).sourceLocation.index]? = some cell ∧
      CellDecoded prepared completion (exported.receipt.ledger.rows[index]) cell := by
  obtain ⟨cell, found, decoded⟩ := exported.decoded.lookup (List.getElem?_eq_getElem index.isLt)
  refine ⟨cell, ?_, decoded⟩
  rw [exported.receipt.ledger.sourceLocation_exact]
  simpa [heap, List.getElem?_append_right] using found

end Solcore.Frontend.SourceCoreCompatibleHeapOutputs
