import Solcore.Frontend.SourceCoreCallableNativeCellHeaders
import Solcore.Frontend.SourceCoreCallableIndexedLedger
import Solcore.Frontend.SourceCoreCallableIndexedAllocationFrames

/-! The paired runner joins an actual allocation snapshot to the shared raw
source declaration cache. Metadata is prepared once; runtime selection checks
only the snapshot's table index and the recorded compiler allocation key.
The selector keeps store adjacency without inferring execution history. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableIndexedCellHeaders
open SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Program := SourceCoreCallableIndexedPrograms.Prepared
abbrev Graph := @SourceCoreCallableAncestryPairedPreparation.Prepared
abbrev Header {checked : Checked} {program : Program checked} (graph : Graph program.base) :=
  SourceCoreCallableNativeCellHeaders.Header graph program.contexts
abbrev Prepared {checked : Checked} {program : Program checked} (graph : Graph program.base) :=
  SourceCoreCallableNativeCellHeaders.Prepared graph program.contexts

inductive Error where
  | metadata (error : SourceCoreCallableNativeCellHeaders.Error)
  | snapshot (error : SourceCoreCallableIndexedAllocationFrames.Error)
  | frameUnavailable (binder : Resolved.LocalId)
  | headerUnavailable (position : Nat) (binder : Resolved.LocalId)
  deriving Repr

def prepare {checked : Checked} {program : Program checked} (graph : Graph program.base) :
    Except Error (Prepared (program := program) graph) :=
  (SourceCoreCallableNativeCellHeaders.prepare graph program.contexts).mapError Error.metadata

structure Selected {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (prepared : Prepared (program := program) graph) {store : Core.Store}
    (row : SourceCoreAllocationLedger.Row program.layouts store) where private mk ::
  snapshot : SourceCoreCallableIndexedAllocationFrames.Snapshot program.ancestry.layout.frame row
  position : Nat
  lookup : snapshot.frame.index? = some position
  header : Header (program := program) graph
  selected : prepared.at? position row.entry.key = some header

def select {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (prepared : Prepared (program := program) graph) {store : Core.Store}
    (row : SourceCoreAllocationLedger.Row program.layouts store) : Except Error (Selected prepared row) := do
  let snapshot ← (SourceCoreCallableIndexedAllocationFrames.snapshot program.ancestry.layout.frame row).mapError Error.snapshot
  match lookup : snapshot.frame.index? with
  | some position =>
    match selected : prepared.at? position row.entry.key with
    | none => throw (.headerUnavailable position row.entry.key.binder.id)
    | some header => pure ⟨snapshot, position, lookup, header, selected⟩
  | _ => throw (.frameUnavailable row.entry.key.binder.id)

theorem Selected.binder_identity {checked : Checked} {program : Program checked} {graph : Graph program.base}
    {prepared : Prepared (program := program) graph} {store : Core.Store}
    {row : SourceCoreAllocationLedger.Row program.layouts store} (selected : Selected prepared row) :
    selected.header.raw.binder.id = row.entry.key.binder.id :=
  SourceCoreCallableNativeCellHeaders.Prepared.binder_identity prepared selected.selected

end Solcore.Frontend.SourceCoreCallableIndexedCellHeaders
