import Solcore.Frontend.RustHull.RuntimeCodeStateCorrespondence
import Solcore.Frontend.RustHull.RuntimeExtendedInitializedEffects

/-! Actual code-image allocations extend the account layout. Their bounds and
separation follow from the same named cells as the existing runtime resources. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCodeInitializedEffects
open Correspondence ScalarExecution RuntimeInitializedEffects

structure Ready {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : StateReady cells store state}
    {words : LogsSemantics.Words} {cursor : Core.Word} {logs : RuntimeLogInitializedEffects.Ready runtime words cursor}
    {balances : StorageSemantics.Words} (accounts : RuntimeAccountInitializedEffects.Ready logs balances)
    (image : Option (List UInt8)) where
  layout : RuntimeCodeEffectsCorrespondence.Layout
  base : layout.toAccountLayout = accounts.layout
  codeMember : ⟨"code", Core.WordMapping.type, layout.code⟩ ∈ cells.map InitializedCell.effectSlot
  knownMember : ⟨"codeKnown", .bool, layout.known⟩ ∈ cells.map InitializedCell.effectSlot
  readCode : store.read? layout.code = some (Core.WordMapping.encode (Memory.packBytes (image.getD [])))
  readKnown : store.read? layout.known = some (.bool image.isSome)

theorem observe {cells : List InitializedCell} {store : Core.Store}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots ++ Effects.codeSlots)
    (initialized : InitializedCells cells store)
    {name : String} {type : Core.Ty} {value : Core.Value}
    (member : (name, type) ∈ Effects.codeSlots)
    (observed : ∀ cell ∈ cells, cell.name = name → cell.value = value) :
    Nonempty (Cell cells store name type value) := by
  have present := List.mem_append_right Effects.slots member
  rw [← signature] at present
  obtain ⟨cell, cellMember, same⟩ := List.mem_map.mp present
  obtain ⟨named, typed⟩ := Prod.mk.inj same
  exact ⟨cell, cellMember, named, typed,
    by simpa only [observed cell cellMember named] using initialized cell cellMember⟩

theorem slot_typed {cells : List InitializedCell} {slot : EffectSlot}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots ++ Effects.codeSlots)
    (member : slot ∈ cells.map InitializedCell.effectSlot) :
    (slot.name, slot.type) ∈ Effects.slots ++ Effects.codeSlots := by
  obtain ⟨cell, cellMember, rfl⟩ := List.mem_map.mp member
  rw [← signature]
  exact List.mem_map_of_mem cellMember

/-- The code and availability cells are passive resources of the actual
frame, including when only the catalog supplies a linked image. -/
theorem ready {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : StateReady cells store state}
    {words : LogsSemantics.Words} {cursor : Core.Word} {logs : RuntimeLogInitializedEffects.Ready runtime words cursor}
    {balances : StorageSemantics.Words} {image : Option (List UInt8)}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots ++ Effects.codeSlots)
    (initialized : InitializedCells cells store) (separate : CellLocations cells)
    (accounts : RuntimeAccountInitializedEffects.Ready logs balances)
    (codeObserved : ∀ cell ∈ cells, cell.name = "code" →
      cell.value = Core.WordMapping.encode (Memory.packBytes (image.getD [])))
    (knownObserved : ∀ cell ∈ cells, cell.name = "codeKnown" → cell.value = .bool image.isSome) :
    Nonempty (Ready accounts image) := by
  obtain ⟨code⟩ := observe signature initialized (type := Core.WordMapping.type) (by simp [Effects.codeSlots]) codeObserved
  obtain ⟨known⟩ := observe signature initialized (type := .bool) (by simp [Effects.codeSlots]) knownObserved
  obtain ⟨codeSlot, codeMember, codeName, codeOutside, codeBelow, codeRead⟩ :=
    logs.passive_cell separate initialized code.member (by rw [code.named]; decide)
  obtain ⟨knownSlot, knownMember, knownName, knownOutside, knownBelow, knownRead⟩ :=
    logs.passive_cell separate initialized known.member (by rw [known.named]; decide)
  have codeName : codeSlot.name = "code" := codeName.trans code.named
  have knownName : knownSlot.name = "codeKnown" := knownName.trans known.named
  have codeTyped : codeSlot.type = Core.WordMapping.type := by
    have types : ∀ slot ∈ Effects.slots ++ Effects.codeSlots, slot.1 = "code" → slot.2 = Core.WordMapping.type := by decide
    exact types _ (slot_typed signature codeMember) codeName
  have knownTyped : knownSlot.type = .bool := by
    have types : ∀ slot ∈ Effects.slots ++ Effects.codeSlots, slot.1 = "codeKnown" → slot.2 = .bool := by decide
    exact types _ (slot_typed signature knownMember) knownName
  let layout : RuntimeCodeEffectsCorrespondence.Layout := {
    toAccountLayout := accounts.layout
    code := codeSlot.location
    known := knownSlot.location
    codeBelow := by change codeSlot.location < accounts.layout.toLogLayout.boundary; rw [accounts.base]; exact codeBelow
    knownBelow := by change knownSlot.location < accounts.layout.toLogLayout.boundary; rw [accounts.base]; exact knownBelow
    codeOutside := by change codeSlot.location ∉ RuntimeLogEffectsCorrespondence.mutable accounts.layout.toLogLayout; rw [accounts.base]; exact codeOutside
    knownOutside := by change knownSlot.location ∉ RuntimeLogEffectsCorrespondence.mutable accounts.layout.toLogLayout; rw [accounts.base]; exact knownOutside }
  refine ⟨layout, rfl, ?_, ?_, ?_, ?_⟩
  · simpa only [layout, ← codeName, ← codeTyped] using codeMember
  · simpa only [layout, ← knownName, ← knownTyped] using knownMember
  · simpa only [codeObserved code.cell code.member code.named] using codeRead
  · simpa only [knownObserved known.cell known.member known.named] using knownRead

end Solcore.Frontend.RustHull.RuntimeCodeInitializedEffects
