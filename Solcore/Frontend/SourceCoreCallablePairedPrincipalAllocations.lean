import Solcore.Frontend.SourceCoreCallablePairedHeaders
import Solcore.Frontend.SourceCoreCallablePairedLedger

/-! Restore a raw principal from its actual allocation snapshot and cached
paired source header. The generic allocation row supplies the ordered source
captures and its physical location. The native bundle can be Unit.

The receipt keeps actual store adjacency, paired-table lookup, cached header
selection and the complete compiler principal key. A typed but fabricated
frame is not execution history; emitted-frame provenance remains a separate
artifact obligation. No source body is traversed or evaluated by restoration.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallablePairedPrincipalAllocations
open SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Program := SourceCoreCallablePairedPrograms.Prepared
abbrev Graph := @SourceCoreCallableAncestryPairedPreparation.Prepared
abbrev Headers := @SourceCoreCallablePairedHeaders.Prepared
abbrev Cell := SourceTypedRuntime.Cell

inductive Error where
  | absentPrincipal (binder : Resolved.LocalId)
  | snapshot (error : SourceCoreCallablePairedAllocationFrames.Error)
  | frameUnavailable (binder : Resolved.LocalId)
  | headerUnavailable (position : Nat) (binder : Resolved.LocalId)
  deriving Repr

structure Restored {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {store : Core.Store}
    (row : SourceCoreAllocationLedger.Row program.layouts store) where private mk ::
  payload : Core.Value
  present : row.payload = some payload
  snapshot : SourceCoreCallablePairedAllocationFrames.Snapshot program.ancestry.layout.frame row
  position : Nat
  lookup : graph.table.lookupIndex? snapshot.frame = some (some position)
  header : SourceCoreCallablePairedHeaders.PrincipalHeader graph headers.principals
  selected : headers.principalAt? position row.entry.key = some header
  cell : Cell
  exact : cell = header.cell row.environment

def restore {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (headers : Headers graph) {store : Core.Store}
    (row : SourceCoreAllocationLedger.Row program.layouts store) : Except Error (Restored headers row) := do
  match present : row.payload with
  | none => throw (.absentPrincipal row.entry.key.binder.id)
  | some payload =>
    let snapshot ← (SourceCoreCallablePairedAllocationFrames.snapshot program.ancestry.layout.frame row).mapError Error.snapshot
    match lookup : graph.table.lookupIndex? snapshot.frame with
    | some (some position) =>
      match selected : headers.principalAt? position row.entry.key with
      | none => throw (.headerUnavailable position row.entry.key.binder.id)
      | some header => pure ⟨payload, present, snapshot, position, lookup, header, selected, header.cell row.environment, rfl⟩
    | _ => throw (.frameUnavailable row.entry.key.binder.id)

theorem Restored.position_exact {checked : Checked} {program : Program checked} {graph : Graph program.base}
    {headers : Headers graph} {store : Core.Store} {row : SourceCoreAllocationLedger.Row program.layouts store}
    (restored : Restored headers row) : restored.header.position.val = restored.position := by
  have selected := restored.selected
  unfold SourceCoreCallablePairedHeaders.Prepared.principalAt? at selected
  have tested := List.find?_some selected
  exact (of_decide_eq_true tested).1

theorem Restored.native_key {checked : Checked} {program : Program checked} {graph : Graph program.base}
    {headers : Headers graph} {store : Core.Store} {row : SourceCoreAllocationLedger.Row program.layouts store}
    (restored : Restored headers row) : restored.header.principal.matchesLayout row.entry.key := by
  have selected := restored.selected
  unfold SourceCoreCallablePairedHeaders.Prepared.principalAt? at selected
  have tested := List.find?_some selected
  exact (of_decide_eq_true tested).2

theorem Restored.raw_type {checked : Checked} {program : Program checked} {graph : Graph program.base}
    {headers : Headers graph} {store : Core.Store} {row : SourceCoreAllocationLedger.Row program.layouts store}
    (restored : Restored headers row) : restored.cell.type = restored.header.declaration.binder.scheme.body := by
  rw [restored.exact]
  rfl

theorem Restored.original_closure {checked : Checked} {program : Program checked} {graph : Graph program.base}
    {headers : Headers graph} {store : Core.Store} {row : SourceCoreAllocationLedger.Row program.layouts store}
    (restored : Restored headers row) :
    restored.cell.value = some (.closure restored.header.parameters restored.header.resultType restored.header.body
      restored.header.state.metadata.source restored.header.state.metadata.owner row.environment restored.header.principal.context.evidence) := by
  rw [restored.exact]
  rfl

theorem Restored.capture_order {checked : Checked} {program : Program checked} {graph : Graph program.base}
    {headers : Headers graph} {store : Core.Store} {row : SourceCoreAllocationLedger.Row program.layouts store}
    (_restored : Restored headers row) :
    row.environment.map Prod.fst = row.entry.key.scope.map Prod.fst := row.captured.binders_exact

end Solcore.Frontend.SourceCoreCallablePairedPrincipalAllocations
