import Solcore.Frontend.RustHull.RuntimeAccountStateCorrespondence
import Solcore.Frontend.RustHull.RuntimeLogInitializedEffects

/-! The public allocator supplies the balance ledger and separates it from
the mutable memory, storage and event cells used by execution. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeAccountInitializedEffects
open Correspondence ScalarExecution RuntimeInitializedEffects

structure Ready {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : StateReady cells store state}
    {words : LogsSemantics.Words} {cursor : Core.Word}
    (logs : RuntimeLogInitializedEffects.Ready runtime words cursor)
    (balances : StorageSemantics.Words) where
  layout : RuntimeAccountEffectsCorrespondence.Layout
  base : layout.toLogLayout = logs.layout
  balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ cells.map InitializedCell.effectSlot
  balancesRead : store.read? layout.balances = some (Core.WordMapping.encode balances)

theorem ready {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : StateReady cells store state}
    {words : LogsSemantics.Words} {cursor : Core.Word} {balances : StorageSemantics.Words}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots)
    (initialized : InitializedCells cells store) (separate : CellLocations cells)
    (logs : RuntimeLogInitializedEffects.Ready runtime words cursor)
    (observed : ∀ cell ∈ cells, cell.name = "balances" → cell.value = Core.WordMapping.encode balances) :
    Nonempty (Ready logs balances) := by
  obtain ⟨balance⟩ := RuntimeLogInitializedEffects.observe signature initialized
    (type := Core.WordMapping.type) (by simp [Effects.slots]) observed
  have outside : balance.cell.location ∉ RuntimeLogEffectsCorrespondence.mutable logs.layout := by
    intro inside
    rcases List.mem_cons.mp inside with same | inside
    · exact cell_location_ne separate balance.member logs.logsMember (by simp [balance.named]) same
    rcases List.mem_cons.mp inside with same | inside
    · exact cell_location_ne separate balance.member logs.logSizeMember (by simp [balance.named]) same
    rw [logs.base] at inside
    change balance.cell.location ∈ [runtime.memory, runtime.locations.memorySize] ++ runtime.locations.mutable at inside
    simp only [StorageBuiltinCorrespondence.Locations.mutable, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at inside
    rcases inside with (same | same) | same | same | same | same
    all_goals
      first
      | exact cell_location_ne separate balance.member runtime.memoryMember (by simp [balance.named]) same
      | exact cell_location_ne separate balance.member runtime.sizeMember (by simp [balance.named]) same
      | exact cell_location_ne separate balance.member runtime.worldMember (by simp [balance.named]) same
      | exact cell_location_ne separate balance.member runtime.exitMember (by simp [balance.named]) same
      | exact cell_location_ne separate balance.member runtime.offsetMember (by simp [balance.named]) same
      | exact cell_location_ne separate balance.member runtime.returnSizeMember (by simp [balance.named]) same
  let layout : RuntimeAccountEffectsCorrespondence.Layout := {
    toLogLayout := logs.layout
    balances := balance.cell.location
    balancesBelow := by
      change balance.cell.location < logs.layout.toLayout.boundary
      rw [logs.base]
      exact initialized.location_bound balance.member
    balancesOutside := outside }
  exact ⟨layout, rfl, balance.slot, balance.stored⟩

end Solcore.Frontend.RustHull.RuntimeAccountInitializedEffects
