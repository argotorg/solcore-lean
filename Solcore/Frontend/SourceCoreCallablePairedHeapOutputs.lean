import Solcore.Frontend.SourceCoreCallablePairedOutputs
import Solcore.Frontend.SourceCoreCallablePairedCellHeaders

/-! Export actual recorded source cells, including generic principals and
deep callable data. Raw declarations come from the reached source-state
cache rather than the compiler's complete native substitution context.
The opaque source prefix and ordered physical allocation receipts survive.
This decoder does not evaluate source code or establish execution history. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallablePairedHeapOutputs
open SourceInference
open SourceCoreCallablePairedOutputs
abbrev Cell := SourceTypedRuntime.Cell
abbrev Row {checked : Checked} {program : Program checked} (completion : Completion program) :=
  SourceCoreAllocationLedger.Row program.layouts (StoreOf completion)

inductive Error where
  | output (error : SourceCoreCallablePairedOutputs.Error)
  | headers (error : SourceCoreCallablePairedCellHeaders.Error)
  | principal (error : SourceCoreCallablePairedPrincipalAllocations.Error)
  | projection (location : SourceTypedRuntime.Location) (error : SourceCoreCompatibleCatalog.Error)
  | payloadTypeMismatch (location : SourceTypedRuntime.Location) (expected actual : Core.Ty)
  | principalTypeMismatch (location : SourceTypedRuntime.Location)
  | snapshotUnavailable
  deriving Repr

structure Prepared {checked : Checked} (program : Program checked) where private mk ::
  output : SourceCoreCallablePairedOutputs.Prepared program
  outputPrepared : SourceCoreCallablePairedOutputs.prepare program = .ok output
  headers : SourceCoreCallablePairedCellHeaders.Prepared (program := program) output.graph
  headersPrepared : SourceCoreCallablePairedCellHeaders.prepare (program := program) output.graph = .ok headers

def prepare {checked : Checked} (program : Program checked) : Except Error (Prepared program) := do
  match outputPrepared : SourceCoreCallablePairedOutputs.prepare program with
  | .error error => throw (.output error)
  | .ok output =>
    match headersPrepared : SourceCoreCallablePairedCellHeaders.prepare (program := program) output.graph with
    | .error error => throw (.headers error)
    | .ok headers => pure ⟨output, outputPrepared, headers, headersPrepared⟩

abbrev Selection {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {completion : Completion program} (row : Row completion) :=
  SourceCoreCallablePairedCellHeaders.Selected prepared.headers row

def rawType {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {row : Row completion} (selected : Selection prepared row) : TypeSystem.Ty :=
  selected.header.raw.binder.scheme.body

inductive CellDecoded {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) {initial : SourceHeap} (ledger : Ledger completion initial)
    (row : Row completion) : Cell → Prop where
  | absent (selected : Selection prepared row)
      (monomorphic : selected.header.raw.binder.scheme.quantified = [])
      (missing : row.payload = none) :
      CellDecoded prepared completion ledger row ⟨rawType selected, none⟩
  | present (selected : Selection prepared row)
      (monomorphic : selected.header.raw.binder.scheme.quantified = [])
      {value : Core.Value} (present : row.payload = some value)
      (snapshot : SnapshotAt prepared.output completion)
      (decoded : Data ledger snapshot (rawType selected) value) :
      CellDecoded prepared completion ledger row ⟨rawType selected, some decoded.source⟩
  | principal (selected : Selection prepared row)
      (generic : selected.header.raw.binder.scheme.quantified ≠ [])
      (restored : SourceCoreCallablePairedPrincipalAllocations.Restored prepared.output.headers row)
      (same : restored.cell.type = rawType selected) :
      CellDecoded prepared completion ledger row restored.cell

theorem CellDecoded.raw_header {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} {ledger : Ledger completion initial}
    {row : Row completion} {cell : Cell} (decoded : CellDecoded prepared completion ledger row cell) :
    ∃ selected : Selection prepared row, cell.type = rawType selected ∧
      selected.header.raw.binder.id = row.entry.key.binder.id := by
  cases decoded with
  | absent selected _ _ => exact ⟨selected, rfl, selected.binder_identity⟩
  | present selected _ _ _ _ => exact ⟨selected, rfl, selected.binder_identity⟩
  | principal selected _ _ same => exact ⟨selected, same, selected.binder_identity⟩

private def decodeCell {checked : Checked} {program : Program checked}
    (prepared : Prepared program) (completion : Completion program) {initial : SourceHeap}
    (ledger : Ledger completion initial) (available : Option (SnapshotAt prepared.output completion))
    (fuel : Nat) (row : Row completion) :
    Except Error {cell : Cell // CellDecoded prepared completion ledger row cell} := do
  let selected ← (SourceCoreCallablePairedCellHeaders.select prepared.headers row).mapError Error.headers
  if monomorphic : selected.header.raw.binder.scheme.quantified = [] then
    match present : row.payload with
    | none => pure ⟨⟨rawType selected, none⟩, .absent selected monomorphic present⟩
    | some value =>
      match projected : checked.catalog.project (rawType selected) with
      | .error error => throw (.projection row.sourceLocation error)
      | .ok type =>
        if same : type = row.entry.key.payloadType then
          let snapshot ← match available with
            | none => throw .snapshotUnavailable
            | some snapshot => pure snapshot
          let typed := row.payload_typed ledger.typed present
          let decoded ← (decodeData prepared.output completion ledger snapshot (rawType selected) value
            row.entry.key.payloadType (by simpa only [same] using projected) typed fuel).mapError Error.output
          pure ⟨⟨rawType selected, some decoded.source⟩, .present selected monomorphic present snapshot decoded⟩
        else throw (.payloadTypeMismatch row.sourceLocation type row.entry.key.payloadType)
  else
    let restored ← (SourceCoreCallablePairedPrincipalAllocations.restore prepared.output.headers row).mapError Error.principal
    if same : restored.cell.type = rawType selected then
      pure ⟨restored.cell, .principal selected monomorphic restored same⟩
    else throw (.principalTypeMismatch row.sourceLocation)

private def cell {checked : Checked} {program : Program checked}
    (prepared : Prepared program) (completion : Completion program) {initial : SourceHeap}
    (ledger : Ledger completion initial) (available : Option (SnapshotAt prepared.output completion))
    (fuel : Nat) (row : Row completion) : Except Error Cell :=
  (decodeCell prepared completion ledger available fuel row).map Subtype.val

inductive CellsDecoded {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) {initial : SourceHeap} (ledger : Ledger completion initial) :
    List (Row completion) → List Cell → Prop where
  | nil : CellsDecoded prepared completion ledger [] []
  | cons {row rows cell cells} (head : CellDecoded prepared completion ledger row cell)
      (tail : CellsDecoded prepared completion ledger rows cells) :
      CellsDecoded prepared completion ledger (row :: rows) (cell :: cells)

private theorem cells_sound {checked : Checked} {program : Program checked}
    (prepared : Prepared program) (completion : Completion program) {initial : SourceHeap}
    (ledger : Ledger completion initial) (available : Option (SnapshotAt prepared.output completion))
    (fuel : Nat) {rows : List (Row completion)} {cells : List Cell}
    (accepted : rows.mapM (cell prepared completion ledger available fuel) = .ok cells) :
    CellsDecoded prepared completion ledger rows cells := by
  induction rows generalizing cells with
  | nil => simp at accepted; subst cells; exact .nil
  | cons row rows ih =>
    cases head : decodeCell prepared completion ledger available fuel row with
    | error error => simp [List.mapM_cons, cell, head, Except.map, bind, Except.bind] at accepted
    | ok decoded =>
      cases tail : rows.mapM (cell prepared completion ledger available fuel) with
      | error error => simp [List.mapM_cons, cell, head, Except.map, bind, Except.bind, tail] at accepted
      | ok rest =>
        simp only [List.mapM_cons, cell, head, Except.map, bind, Except.bind, tail, pure, Except.pure,
          Except.ok.injEq] at accepted
        subst cells
        exact .cons decoded.property (ih tail)

theorem CellsDecoded.length {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} {ledger : Ledger completion initial}
    {rows : List (Row completion)} {cells : List Cell}
    (decoded : CellsDecoded prepared completion ledger rows cells) : cells.length = rows.length := by
  induction decoded <;> simp_all

theorem CellsDecoded.lookup {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} {ledger : Ledger completion initial}
    {rows : List (Row completion)} {cells : List Cell}
    (decoded : CellsDecoded prepared completion ledger rows cells) {index : Nat} {row : Row completion}
    (found : rows[index]? = some row) :
    ∃ cell, cells[index]? = some cell ∧ CellDecoded prepared completion ledger row cell := by
  induction decoded generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst row; exact ⟨_, rfl, head⟩
    | succ index => exact ih found

structure Export {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) (initial : SourceHeap) where private mk ::
  ledger : Ledger completion initial
  snapshot : Option (SnapshotAt prepared.output completion)
  cells : List Cell
  decoded : CellsDecoded prepared completion ledger ledger.ledger.rows cells
  private fuel : Nat
  private exported : ledger.ledger.exportHeap (cell prepared completion ledger snapshot fuel) = .ok (initial ++ cells)

def Export.heap {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} (exported : Export prepared completion initial) : SourceHeap :=
  initial ++ exported.cells

def exportHeap {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) (initial : SourceHeap := []) (fuel : Nat := 1024) :
    Except Error (Export prepared completion initial) := do
  let ledger ← (SourceCoreCallablePairedLedger.scan completion initial).mapError (Error.output ∘ SourceCoreCallablePairedOutputs.Error.ledger)
  let available ← if ledger.ledger.rows.any (fun row => row.payload.isSome) then
      some <$> ((SourceCoreCallablePairedOutputs.snapshot prepared.output completion).mapError Error.output)
    else pure none
  match accepted : ledger.ledger.rows.mapM (cell prepared completion ledger available fuel) with
  | .error error => throw error
  | .ok cells => pure ⟨ledger, available, cells, cells_sound prepared completion ledger available fuel accepted, fuel, by
      simp [SourceCoreAllocationLedger.Ledger.exportHeap, accepted, Functor.map, Except.map]⟩

theorem Export.prefix_exact {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} (exported : Export prepared completion initial) :
    exported.heap.take initial.length = initial :=
  exported.ledger.ledger.exportHeap_prefix _ exported.exported

theorem Export.length_exact {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} (exported : Export prepared completion initial) :
    exported.heap.length = initial.length + exported.ledger.ledger.rows.length := by
  simp only [heap, List.length_append, exported.decoded.length]

theorem Export.cell_at_sourceLocation {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} (exported : Export prepared completion initial)
    (index : Fin exported.ledger.ledger.rows.length) :
    ∃ cell, exported.heap[(exported.ledger.ledger.rows[index]).sourceLocation.index]? = some cell ∧
      CellDecoded prepared completion exported.ledger (exported.ledger.ledger.rows[index]) cell := by
  obtain ⟨cell, found, decoded⟩ := exported.decoded.lookup (List.getElem?_eq_getElem index.isLt)
  refine ⟨cell, ?_, decoded⟩
  rw [exported.ledger.ledger.sourceLocation_exact]
  simpa [Export.heap, List.getElem?_append_right] using found

end Solcore.Frontend.SourceCoreCallablePairedHeapOutputs
