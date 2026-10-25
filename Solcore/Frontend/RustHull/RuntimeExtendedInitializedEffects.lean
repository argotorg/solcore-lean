import Solcore.Frontend.RustHull.RuntimeAccountInitializedEffects

/-! Extra code-image cells preserve the existing initialized runtime resources.
The ordinary slot prefix supplies those resources; their members then lift to
the complete slot list without rebuilding the separation proofs. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeExtendedInitializedEffects
open Correspondence ScalarExecution RuntimeInitializedEffects

abbrev baseCells (cells : List InitializedCell) : List InitializedCell :=
  cells.take Effects.slots.length

theorem base_signature {cells : List InitializedCell} {extra : List (String × Core.Ty)}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots ++ extra) :
    (baseCells cells).map (fun cell => (cell.name, cell.type)) = Effects.slots := by
  rw [baseCells, List.map_take, signature, List.take_left]

theorem slot_inclusion {smaller larger : List InitializedCell}
    (included : ∀ cell ∈ smaller, cell ∈ larger) {slot : EffectSlot}
    (member : slot ∈ smaller.map InitializedCell.effectSlot) :
    slot ∈ larger.map InitializedCell.effectSlot := by
  obtain ⟨cell, present, rfl⟩ := List.mem_map.mp member
  exact List.mem_map_of_mem (included cell present)

/-- Enlarging the cell inventory does not change its represented resources. -/
def extendRuntime {smaller larger : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State}
    (included : ∀ cell ∈ smaller, cell ∈ larger) (ready : StateReady smaller store state) :
    StateReady larger store state where
  memory := ready.memory
  locations := ready.locations
  memoryMember := slot_inclusion included ready.memoryMember
  worldMember := slot_inclusion included ready.worldMember
  addressMember := slot_inclusion included ready.addressMember
  completeMember := slot_inclusion included ready.completeMember
  staticMember := slot_inclusion included ready.staticMember
  sizeMember := slot_inclusion included ready.sizeMember
  exitMember := slot_inclusion included ready.exitMember
  offsetMember := slot_inclusion included ready.offsetMember
  returnSizeMember := slot_inclusion included ready.returnSizeMember
  memoryRelated := ready.memoryRelated
  storageRelated := ready.storageRelated
  distinct := ready.distinct

def extendLogs {smaller larger : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : StateReady smaller store state}
    {words : LogsSemantics.Words} {cursor : Core.Word}
    (included : ∀ cell ∈ smaller, cell ∈ larger) (ready : RuntimeLogInitializedEffects.Ready runtime words cursor) :
    RuntimeLogInitializedEffects.Ready (extendRuntime included runtime) words cursor where
  layout := ready.layout
  base := ready.base
  logsMember := slot_inclusion included ready.logsMember
  logSizeMember := slot_inclusion included ready.logSizeMember
  logsRead := ready.logsRead
  logSizeRead := ready.logSizeRead

def extendAccounts {smaller larger : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : StateReady smaller store state}
    {words : LogsSemantics.Words} {cursor : Core.Word} {logs : RuntimeLogInitializedEffects.Ready runtime words cursor}
    {balances : StorageSemantics.Words}
    (included : ∀ cell ∈ smaller, cell ∈ larger) (ready : RuntimeAccountInitializedEffects.Ready logs balances) :
    RuntimeAccountInitializedEffects.Ready (extendLogs included logs) balances where
  layout := ready.layout
  base := ready.base
  balancesMember := slot_inclusion included ready.balancesMember
  balancesRead := ready.balancesRead

/-- The allocator's actual ordinary prefix provides memory, storage, events
and balances, even when code cells follow it. -/
theorem ready {cells : List InitializedCell} {store : Core.Store} {extra : List (String × Core.Ty)}
    {accounts : StorageCorrespondence.Accounts} {state : RuntimeEffectsSemantics.State}
    {words : LogsSemantics.Words} {cursor : Core.Word} {balances : StorageSemantics.Words}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots ++ extra)
    (initialized : InitializedCells cells store) (separate : CellLocations cells)
    (observed : ∀ cell ∈ cells, RuntimeInitializedEffects.Observed accounts state cell)
    (world : accounts.map Prod.fst = state.storage.world)
    (logsObserved : ∀ cell ∈ cells, cell.name = "logs" → cell.value = Core.WordMapping.encode words)
    (cursorObserved : ∀ cell ∈ cells, cell.name = "logSize" → cell.value = .word cursor)
    (balancesObserved : ∀ cell ∈ cells, cell.name = "balances" → cell.value = Core.WordMapping.encode balances) :
    ∃ runtime : StateReady cells store state,
      ∃ logs : RuntimeLogInitializedEffects.Ready runtime words cursor,
        Nonempty (RuntimeAccountInitializedEffects.Ready logs balances) := by
  have included : ∀ cell ∈ baseCells cells, cell ∈ cells := fun _ member => List.mem_of_mem_take member
  have baseInitialized : InitializedCells (baseCells cells) store := fun cell member => initialized cell (included cell member)
  have baseSeparate := separate.subset included
  obtain ⟨runtime⟩ := RuntimeInitializedEffects.state_ready (base_signature signature) baseInitialized baseSeparate
    (fun cell member => observed cell (included cell member)) world
  obtain ⟨logs⟩ := RuntimeLogInitializedEffects.ready (base_signature signature) baseInitialized baseSeparate runtime
    (fun cell member => logsObserved cell (included cell member))
    (fun cell member => cursorObserved cell (included cell member))
  obtain ⟨accounts⟩ := RuntimeAccountInitializedEffects.ready (base_signature signature) baseInitialized baseSeparate logs
    (fun cell member => balancesObserved cell (included cell member))
  exact ⟨extendRuntime included runtime, extendLogs included logs, ⟨extendAccounts included accounts⟩⟩

/-- These are exactly the two slot lists selected by the public compiler. -/
def slots (withCode : Bool) : List (String × Core.Ty) :=
  Effects.slots ++ if withCode then Effects.codeSlots else []

theorem slots_include (withCode : Bool) {slot : String × Core.Ty} (member : slot ∈ Effects.slots) :
    slot ∈ slots withCode := List.mem_append_left _ member

theorem code_member {slot : String × Core.Ty} (member : slot ∈ Effects.codeSlots) :
    slot ∈ slots true := List.mem_append_right _ member

theorem slots_allowed (withCode : Bool) {slot : String × Core.Ty} (member : slot ∈ slots withCode) :
    slot ∈ Effects.slots ++ Effects.codeSlots := by
  cases withCode with
  | false => exact List.mem_append_left _ (by simpa only [slots, Bool.false_eq_true, ↓reduceIte, List.append_nil] using member)
  | true => exact member

theorem slots_unique (withCode : Bool) : ((slots withCode).map Prod.fst).Nodup := by
  cases withCode <;> decide

theorem slots_separate (withCode : Bool) :
    ∀ slot ∈ slots withCode, slot.1.startsWith "function$" = false := by
  intro slot member
  apply String.startsWith_string_eq_false_iff.mpr
  have absent : ∀ slot ∈ slots withCode, ¬ ("function$".toList <+: slot.1.toList) := by
    cases withCode <;> decide
  exact absent slot member

theorem initialized_unique {cells : List InitializedCell} {withCode : Bool}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = slots withCode) :
    (cells.map InitializedCell.name).Nodup := by
  have names := congrArg (List.map Prod.fst) signature
  simp only [List.map_map, Function.comp_def] at names
  rw [names]
  exact slots_unique withCode

theorem initialized_separate {cells : List InitializedCell} {withCode : Bool}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = slots withCode) :
    EffectSlotsSeparate (cells.map InitializedCell.effectSlot) := by
  intro slot member
  obtain ⟨cell, cellMember, rfl⟩ := List.mem_map.mp member
  apply slots_separate withCode (cell.name, cell.type)
  rw [← signature]
  exact List.mem_map_of_mem cellMember

end Solcore.Frontend.RustHull.RuntimeExtendedInitializedEffects
