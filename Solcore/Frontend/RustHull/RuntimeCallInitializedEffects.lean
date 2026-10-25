import Solcore.Frontend.RustHull.RuntimeCallStateCorrespondence
import Solcore.Frontend.RustHull.ContractCallRuntimeFacts

/-! Named cells from the actual frame allocator supply the call layout, depth,
handler capture and location separation. The dispatcher is an earlier cell. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallInitializedEffects
open Correspondence ScalarExecution RuntimeInitializedEffects ContractCallCorrespondence

abbrev Base := RuntimeReturnDataEffectsCorrespondence.Layout

def baseSlots (base : Base) : List EffectSlot :=
  [⟨"balances", Core.WordMapping.type, base.balances⟩,
   ⟨"returnData", Core.WordMapping.type, base.returnData⟩,
   ⟨"returnDataSize", .word, base.returnDataSize⟩,
   ⟨"logs", Core.WordMapping.type, base.logs⟩,
   ⟨"logSize", .word, base.logSize⟩,
   ⟨"memory", Core.WordMapping.type, base.memory⟩,
   ⟨"world", AccountState.type, base.storage.world⟩,
   ⟨"address", .word, base.storage.address⟩,
   ⟨"worldComplete", .bool, base.storage.complete⟩,
   ⟨"isStatic", .bool, base.storage.isStatic⟩,
   ⟨"exit", .word, base.storage.exit⟩,
   ⟨"returnOffset", .word, base.storage.returnOffset⟩,
   ⟨"returnSize", .word, base.storage.returnSize⟩,
   ⟨"memorySize", .word, base.storage.memorySize⟩]

structure Ready (base : Base) (cells : List InitializedCell) (store : Core.Store)
    (depth : Core.Word) (source : Core.Word) (dispatcherLocation : Nat) where
  layout : RuntimeCallEffectsCorrespondence.Layout
  baseEqual : layout.toReturnDataLayout = base
  dispatcherEqual : layout.dispatcher = dispatcherLocation
  depthMember : ⟨"callDepth", .word, layout.callDepth⟩ ∈ cells.map InitializedCell.effectSlot
  handlerMember : ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, layout.callHandler⟩ ∈ cells.map InitializedCell.effectSlot
  depthRead : store.read? layout.callDepth = some (.word depth)
  handlerValue : Core.Value
  handlerRead : store.read? layout.callHandler = some (.inRight .unit handlerValue)
  handler : AccountCallCorrespondence.CallHandlerClosure source dispatcherLocation handlerValue

theorem ready {cells : List InitializedCell} {store : Core.Store}
    {extra : List (String × Core.Ty)} {base : Base} {depth source : Core.Word} {dispatcherLocation : Nat}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots ++ extra)
    (initialized : InitializedCells cells store) (separate : CellLocations cells)
    (boundary : base.boundary = store.length)
    (members : ∀ slot ∈ baseSlots base, slot ∈ cells.map InitializedCell.effectSlot)
    (dispatcherBelow : dispatcherLocation < base.boundary)
    (dispatcherOutside : ∀ cell ∈ cells, cell.location ≠ dispatcherLocation)
    (depthObserved : ∀ cell ∈ cells, initializedDepth depth cell)
    (handlerObserved : ∀ cell ∈ cells, initializedHandler source dispatcherLocation cell) :
    Nonempty (Ready base cells store depth source dispatcherLocation) := by
  obtain ⟨depthCell⟩ := ContractReturnDataCorrespondence.observe_base signature initialized
    (name := "callDepth") (type := .word) (by simp [Effects.slots])
    (fun cell member named _ => depthObserved cell member named)
  have present : ("callHandler", Core.OptionalCell.cellType Calls.callbackType) ∈
      cells.map (fun cell => (cell.name, cell.type)) := by
    rw [signature]
    exact List.mem_append_left _ (by simp [Effects.slots])
  obtain ⟨handlerCell, handlerMember, handlerSame⟩ := List.mem_map.mp present
  obtain ⟨handlerName, handlerType⟩ := Prod.mk.inj handlerSame
  obtain ⟨handlerValue, handlerStored, ⟨handler⟩⟩ := handlerObserved handlerCell handlerMember handlerName
  have handlerSlot : (⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, handlerCell.location⟩ : EffectSlot)
      ∈ cells.map InitializedCell.effectSlot :=
    List.mem_map.mpr ⟨handlerCell, handlerMember, by simp only [InitializedCell.effectSlot, handlerName, handlerType]⟩
  let dispatchCell : InitializedCell :=
    ⟨"$dispatcher", Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType, dispatcherLocation, .unit⟩
  let selected : List EffectSlot :=
    (baseSlots base).take 3 ++
    [⟨"callDepth", .word, depthCell.cell.location⟩,
     ⟨"callHandler", Core.OptionalCell.cellType Calls.callbackType, handlerCell.location⟩,
     dispatchCell.effectSlot] ++ (baseSlots base).drop 3
  have selectedIncluded : ∀ slot ∈ selected, slot ∈ (dispatchCell :: cells).map InitializedCell.effectSlot := by
    intro slot member
    simp only [selected, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with (member | rfl | rfl | rfl) | member
    · exact List.mem_cons_of_mem _ (members slot (List.mem_of_mem_take member))
    · exact List.mem_cons_of_mem _ depthCell.slot
    · exact List.mem_cons_of_mem _ handlerSlot
    · exact .head _
    · exact List.mem_cons_of_mem _ (members slot (List.mem_of_mem_drop member))
  have names : (selected.map EffectSlot.name).Nodup := by
    simp only [selected, baseSlots, dispatchCell, InitializedCell.effectSlot, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    decide
  have distinct := effectSlots_distinct (separate_dispatcher separate dispatcherOutside .unit) selectedIncluded names
  let layout : RuntimeCallEffectsCorrespondence.Layout := {
    toReturnDataLayout := base
    callDepth := depthCell.cell.location
    callHandler := handlerCell.location
    dispatcher := dispatcherLocation
    depthBelow := by rw [boundary]; exact initialized.location_bound depthCell.member
    handlerBelow := by rw [boundary]; exact initialized.location_bound handlerMember
    dispatcherBelow := dispatcherBelow
    callDistinct := distinct }
  exact ⟨layout, rfl, rfl, depthCell.slot, handlerSlot, depthCell.stored, handlerValue,
    by simpa only [handlerStored] using initialized handlerCell handlerMember, handler⟩

end Solcore.Frontend.RustHull.RuntimeCallInitializedEffects
