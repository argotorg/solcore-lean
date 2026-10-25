import Solcore.Frontend.RustHull.RuntimeReturnDataStateCorrespondence
import Solcore.Frontend.RustHull.RuntimeCodeInitializedEffects
import Solcore.Frontend.RustHull.ContractReturnDataRuntimeFacts

/-! The real frame cells establish return-data resources with or without code
slots. The account layout is retained, and optional code cells come from the
existing code initializer proof. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeReturnDataInitializedEffects
open Correspondence ScalarExecution RuntimeInitializedEffects

structure Ready {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : StateReady cells store state}
    {words : LogsSemantics.Words} {cursor : Core.Word} {logs : RuntimeLogInitializedEffects.Ready runtime words cursor}
    {balances : StorageSemantics.Words} (accounts : RuntimeAccountInitializedEffects.Ready logs balances)
    (withCode : Bool) (image : Option (List UInt8)) (data : MemorySemantics.Entries) (size : Core.Word) where
  layout : RuntimeReturnDataEffectsCorrespondence.Layout
  base : layout.toAccountLayout = accounts.layout
  mode : layout.codeCells.isSome = withCode
  dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ cells.map InitializedCell.effectSlot
  dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ cells.map InitializedCell.effectSlot
  readData : store.read? layout.returnData = some (Core.WordMapping.encode data)
  readSize : store.read? layout.returnDataSize = some (.word size)
  codeMembers : ∀ code, layout.codeCells = some code →
    ⟨"code", Core.WordMapping.type, code.code⟩ ∈ cells.map InitializedCell.effectSlot ∧
    ⟨"codeKnown", .bool, code.known⟩ ∈ cells.map InitializedCell.effectSlot
  readCode : ∀ code, layout.codeCells = some code →
    store.read? code.code = some (Core.WordMapping.encode (Memory.packBytes (image.getD []))) ∧
    store.read? code.known = some (.bool image.isSome)

private theorem optional_code {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : StateReady cells store state}
    {words : LogsSemantics.Words} {cursor : Core.Word} {logs : RuntimeLogInitializedEffects.Ready runtime words cursor}
    {balances : StorageSemantics.Words} {withCode : Bool} {image : Option (List UInt8)}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = RuntimeExtendedInitializedEffects.slots withCode)
    (initialized : InitializedCells cells store) (separate : CellLocations cells)
    (accounts : RuntimeAccountInitializedEffects.Ready logs balances)
    (codeObserved : withCode = true → ∀ cell ∈ cells, cell.name = "code" →
      cell.value = Core.WordMapping.encode (Memory.packBytes (image.getD [])))
    (knownObserved : withCode = true → ∀ cell ∈ cells, cell.name = "codeKnown" → cell.value = .bool image.isSome) :
    ∃ codeCells : Option (RuntimeReturnDataEffectsCorrespondence.CodeCells accounts.layout),
      codeCells.isSome = withCode ∧ ∀ code, codeCells = some code →
        (⟨"code", Core.WordMapping.type, code.code⟩ ∈ cells.map InitializedCell.effectSlot ∧
          ⟨"codeKnown", .bool, code.known⟩ ∈ cells.map InitializedCell.effectSlot) ∧
        (store.read? code.code = some (Core.WordMapping.encode (Memory.packBytes (image.getD []))) ∧
          store.read? code.known = some (.bool image.isSome)) := by
  cases withCode with
  | false => exact ⟨none, rfl, by intro _ impossible; cases impossible⟩
  | true =>
      obtain ⟨ready⟩ := RuntimeCodeInitializedEffects.ready signature initialized separate accounts
        (codeObserved rfl) (knownObserved rfl)
      let code : RuntimeReturnDataEffectsCorrespondence.CodeCells accounts.layout := {
        code := ready.layout.code
        known := ready.layout.known
        codeBelow := by simpa only [ready.base] using ready.layout.codeBelow
        knownBelow := by simpa only [ready.base] using ready.layout.knownBelow
        codeOutside := by simpa only [ready.base] using ready.layout.codeOutside
        knownOutside := by simpa only [ready.base] using ready.layout.knownOutside }
      refine ⟨some code, rfl, ?_⟩
      intro actual same
      cases Option.some.inj same
      exact ⟨⟨ready.codeMember, ready.knownMember⟩, ready.readCode, ready.readKnown⟩

private theorem cell_outside {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : StateReady cells store state}
    {words : LogsSemantics.Words} {cursor : Core.Word} (logs : RuntimeLogInitializedEffects.Ready runtime words cursor)
    (separate : CellLocations cells) {cell : InitializedCell} (member : cell ∈ cells)
    (outside : cell.name ∉ ["logs", "logSize", "memory", "memorySize", "world", "exit", "returnOffset", "returnSize"]) :
    cell.location ∉ RuntimeLogEffectsCorrespondence.mutable logs.layout := by
  intro inside
  change cell.location ∈ logs.layout.logs :: logs.layout.logSize ::
    RuntimeEffectsCorrespondence.mutable logs.layout.toLayout at inside
  rcases List.mem_cons.mp inside with same | inside
  · exact cell_location_ne separate member logs.logsMember (fun named => outside (by simp [named])) same
  rcases List.mem_cons.mp inside with same | inside
  · exact cell_location_ne separate member logs.logSizeMember (fun named => outside (by simp [named])) same
  rw [logs.base] at inside
  simp only [RuntimeEffectsCorrespondence.mutable, RuntimeEffectsCorrespondence.initialLayout,
    StorageBuiltinCorrespondence.Locations.mutable, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at inside
  rcases inside with (same | same) | same | same | same | same
  · exact cell_location_ne separate member runtime.memoryMember (fun named => outside (by simp [named])) same
  · exact cell_location_ne separate member runtime.sizeMember (fun named => outside (by simp [named])) same
  · exact cell_location_ne separate member runtime.worldMember (fun named => outside (by simp [named])) same
  · exact cell_location_ne separate member runtime.exitMember (fun named => outside (by simp [named])) same
  · exact cell_location_ne separate member runtime.offsetMember (fun named => outside (by simp [named])) same
  · exact cell_location_ne separate member runtime.returnSizeMember (fun named => outside (by simp [named])) same

/-- Initialization supplies both caller cells and optional image cells. All
bounds and separation facts follow from the actual named allocation. -/
theorem ready {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : StateReady cells store state}
    {words : LogsSemantics.Words} {cursor : Core.Word} {logs : RuntimeLogInitializedEffects.Ready runtime words cursor}
    {balances : StorageSemantics.Words} {withCode : Bool} {image : Option (List UInt8)}
    {data : MemorySemantics.Entries} {size : Core.Word}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = RuntimeExtendedInitializedEffects.slots withCode)
    (initialized : InitializedCells cells store) (separate : CellLocations cells)
    (accounts : RuntimeAccountInitializedEffects.Ready logs balances)
    (dataObserved : ∀ cell ∈ cells, cell.name = "returnData" → cell.value = Core.WordMapping.encode data)
    (sizeObserved : ∀ cell ∈ cells, cell.name = "returnDataSize" → cell.type = .word → cell.value = .word size)
    (codeObserved : withCode = true → ∀ cell ∈ cells, cell.name = "code" →
      cell.value = Core.WordMapping.encode (Memory.packBytes (image.getD [])))
    (knownObserved : withCode = true → ∀ cell ∈ cells, cell.name = "codeKnown" → cell.value = .bool image.isSome) :
    Nonempty (Ready accounts withCode image data size) := by
  obtain ⟨dataCell⟩ := ContractReturnDataCorrespondence.observe_base signature initialized
    (name := "returnData") (type := Core.WordMapping.type) (by simp [Effects.slots])
    (fun cell member named _ => dataObserved cell member named)
  obtain ⟨sizeCell⟩ := ContractReturnDataCorrespondence.observe_base signature initialized
    (name := "returnDataSize") (type := .word) (by simp [Effects.slots]) sizeObserved
  obtain ⟨codeCells, mode, codes⟩ := optional_code signature initialized separate accounts codeObserved knownObserved
  have boundary : accounts.layout.boundary = store.length := by
    change accounts.layout.toLogLayout.toLayout.boundary = store.length
    rw [accounts.base, logs.base]
    rfl
  let layout : RuntimeReturnDataEffectsCorrespondence.Layout := {
    toAccountLayout := accounts.layout
    codeCells := codeCells
    returnData := dataCell.cell.location
    returnDataSize := sizeCell.cell.location
    dataBelow := by rw [boundary]; exact initialized.location_bound dataCell.member
    sizeBelow := by rw [boundary]; exact initialized.location_bound sizeCell.member
    dataOutside := by
      change dataCell.cell.location ∉ RuntimeLogEffectsCorrespondence.mutable accounts.layout.toLogLayout
      rw [accounts.base]
      exact cell_outside logs separate dataCell.member (by rw [dataCell.named]; decide)
    sizeOutside := by
      change sizeCell.cell.location ∉ RuntimeLogEffectsCorrespondence.mutable accounts.layout.toLogLayout
      rw [accounts.base]
      exact cell_outside logs separate sizeCell.member (by rw [sizeCell.named]; decide)
    dataDistinct := ContractReturnDataCorrespondence.cells_distinct separate dataCell sizeCell }
  exact ⟨layout, rfl, mode, dataCell.slot, sizeCell.slot, dataCell.stored, sizeCell.stored,
    fun code present => (codes code present).1, fun code present => (codes code present).2⟩

end Solcore.Frontend.RustHull.RuntimeReturnDataInitializedEffects
