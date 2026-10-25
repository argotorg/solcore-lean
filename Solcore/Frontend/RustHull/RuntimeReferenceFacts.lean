import Solcore.Frontend.RustHull.RuntimeFrameInitializationFacts

/-! Actual shared reference lookup and the initialized frame fields retain
both their declared types and their concrete input values. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open CodeBuilder ScalarExecution

theorem InitializedCells.location_bound {cells : List InitializedCell} {store : Core.Store}
    (initialized : InitializedCells cells store) {cell : InitializedCell} (member : cell ∈ cells) :
    cell.location < store.length := (List.getElem?_eq_some_iff.mp (initialized cell member)).1

theorem RuntimeReferences.find {depth : Nat} {environment : Core.Environment}
    {references : AccountRuntime.References} {cells : List InitializedCell}
    (related : RuntimeReferences depth environment references cells)
    {name foundName : String} {code : Code}
    (found : references.find? (·.1 == name) = some (foundName, code)) :
    ∃ cell ∈ cells, cell.name = name ∧ CodeValue depth environment code cell.reference := by
  induction references generalizing cells with
  | nil => cases found
  | cons entry rest ih =>
      cases cells with
      | nil => cases related.values
      | cons cell cells =>
          obtain ⟨names, values⟩ := related
          have names' : entry.1 = cell.name ∧ rest.map Prod.fst = cells.map InitializedCell.name := by
            simpa only [List.map_cons, List.cons.injEq] using names
          cases values with
          | cons head tail =>
              simp only [List.find?_cons] at found
              split at found
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
                exact ⟨cell, .head _, by simpa only [← names'.1, beq_iff_eq] using ‹(entry.1 == name) = true›, head⟩
              · obtain ⟨selected, member, named, related⟩ := ih ⟨names'.2, tail⟩ found
                exact ⟨selected, .tail _ member, named, related⟩

theorem RuntimeReferences.absent {depth : Nat} {environment : Core.Environment}
    {references : AccountRuntime.References} {cells : List InitializedCell}
    (related : RuntimeReferences depth environment references cells) (name : String)
    (absent : ∀ cell ∈ cells, cell.name ≠ name) : references.find? (·.1 == name) = none := by
  cases found : references.find? (·.1 == name) with
  | none => rfl
  | some entry =>
      obtain ⟨cell, member, named, _⟩ := related.find found
      exact False.elim (absent cell member named)

theorem RuntimeReferences.reference {depth : Nat} {environment : Core.Environment}
    {references : AccountRuntime.References} {cells : List InitializedCell}
    (related : RuntimeReferences depth environment references cells) {name : String}
    (present : name ∈ cells.map InitializedCell.name) :
    ∃ cell ∈ cells, cell.name = name ∧
      CodeValue depth environment (AccountRuntime.reference references name) cell.reference := by
  cases found : references.find? (·.1 == name) with
  | none =>
      rw [← related.names] at present
      obtain ⟨⟨entryName, code⟩, member, named⟩ := List.mem_map.mp present
      have absent := List.find?_eq_none.mp found _ member
      exact False.elim (absent (by simpa only [beq_iff_eq] using named))
  | some entry =>
      obtain ⟨cell, member, named, value⟩ := related.find found
      refine ⟨cell, member, named, ?_⟩
      simpa only [AccountRuntime.reference, found, Option.map_some, Option.getD_some] using value

theorem RuntimeReferences.sharedValid {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {references : AccountRuntime.References} {cells : List InitializedCell}
    (related : RuntimeReferences depth environment references cells)
    (initialized : InitializedCells cells store)
    {slots : List (String × Core.Ty)} {property : InitializedCell → Prop}
    (typed : ∀ slot ∈ slots, ∀ cell ∈ cells, cell.name = slot.1 → cell.type = slot.2)
    (valid : ∀ cell ∈ cells, property cell) :
    FrameSharedValid depth environment store slots references property := by
  intro slot member name code found
  obtain ⟨cell, member', named, codeRelated⟩ := related.find found
  exact ⟨cell, named, typed slot member cell member' named, codeRelated, initialized cell member', valid cell member'⟩

def sharedSlotTypes : List (String × Core.Ty) :=
  [("world", AccountState.type), ("worldComplete", .bool), ("logs", Core.WordMapping.type),
    ("logSize", .word), ("balances", Core.WordMapping.type)] ++ Ambient.slots

theorem sharedInitializers_types (context : Code) :
    (AccountRuntime.sharedInitializers context).map (fun entry => (entry.1, entry.2.1)) = sharedSlotTypes := rfl

theorem sharedInitializers_names (context : Code) :
    (AccountRuntime.sharedInitializers context).map Prod.fst = sharedSlotTypes.map Prod.fst := rfl

theorem sharedSlotTypes_unique : (sharedSlotTypes.map Prod.fst).Nodup := by decide

theorem sharedSlotTypes_compatible {slot sharedSlot : String × Core.Ty}
    (member : slot ∈ Effects.slots ++ Effects.codeSlots) (sharedMember : sharedSlot ∈ sharedSlotTypes)
    (named : sharedSlot.1 = slot.1) : sharedSlot.2 = slot.2 := by
  have checked : sharedSlotTypes.all (fun shared => (Effects.slots ++ Effects.codeSlots).all
      (fun slot => !(shared.1 == slot.1) || decide (shared.2 = slot.2))) = true := by decide
  have valid := List.all_eq_true.mp (List.all_eq_true.mp checked sharedSlot sharedMember) slot member
  simpa only [named, beq_self_eq_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] using valid

theorem shared_description_index {context : Code} {initialValues : List Core.Value}
    {cells : List InitializedCell}
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip initialValues).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    {cell : InitializedCell} (member : cell ∈ cells) :
    ∃ (index : Nat) (entry : String × Core.Ty × Code), (AccountRuntime.sharedInitializers context)[index]? = some entry ∧
      initialValues[index]? = some cell.value ∧ entry.1 = cell.name ∧ entry.2.1 = cell.type := by
  have selected : (cell.name, cell.type, cell.value) ∈
      (((AccountRuntime.sharedInitializers context).zip initialValues).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := by
    rw [← description]
    exact List.mem_map.mpr ⟨cell, member, rfl⟩
  obtain ⟨⟨entry, value⟩, member, same⟩ := List.mem_map.mp (List.mem_reverse.mp selected)
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨entryFound, valueFound⟩ := List.getElem?_zip_eq_some.mp found
  obtain ⟨named, typed, valueSame⟩ := Prod.mk.inj same |>.imp_right Prod.mk.inj
  exact ⟨index, entry, entryFound, valueSame ▸ valueFound, named, typed⟩

theorem shared_description_member {context : Code} {initialValues : List Core.Value}
    {cells : List InitializedCell}
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip initialValues).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    {cell : InitializedCell} (member : cell ∈ cells) : (cell.name, cell.type) ∈ sharedSlotTypes := by
  obtain ⟨_, entry, found, _, named, typed⟩ := shared_description_index description member
  rw [← sharedInitializers_types context]
  exact List.mem_map.mpr ⟨entry, List.mem_of_getElem? found, by simp only [named, typed]⟩

theorem shared_description_value {context : Code} {initialValues : List Core.Value}
    {cells : List InitializedCell}
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip initialValues).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    {cell : InitializedCell} (member : cell ∈ cells) {index : Nat} {name : String} {value : Core.Value}
    (knownName : (sharedSlotTypes.map Prod.fst)[index]? = some name)
    (knownValue : initialValues[index]? = some value) (named : cell.name = name) : cell.value = value := by
  obtain ⟨actualIndex, entry, found, valueFound, named', _⟩ := shared_description_index description member
  have actualName : (sharedSlotTypes.map Prod.fst)[actualIndex]? = some name := by
    rw [← sharedInitializers_names context, List.getElem?_map, found]
    simp only [Option.map_some, named', named]
  have sameIndex : actualIndex = index := (List.getElem?_inj
    (List.getElem?_eq_some_iff.mp actualName).1 sharedSlotTypes_unique).mp (actualName.trans knownName.symm)
  subst actualIndex
  exact Option.some.inj (valueFound.symm.trans knownValue)

theorem shared_description_cell {context : Code} {initialValues : List Core.Value}
    {cells : List InitializedCell}
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip initialValues).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    {index : Nat} {name : String} {value : Core.Value}
    (knownName : (sharedSlotTypes.map Prod.fst)[index]? = some name)
    (knownValue : initialValues[index]? = some value) :
    ∃ cell ∈ cells, cell.name = name ∧ cell.value = value := by
  rw [← sharedInitializers_names context, List.getElem?_map] at knownName
  obtain ⟨entry, found, named⟩ := Option.map_eq_some_iff.mp knownName
  have selected : (entry, value) ∈ (AccountRuntime.sharedInitializers context).zip initialValues :=
    List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨found, knownValue⟩)
  have described : (entry.1, entry.2.1, value) ∈ cells.map (fun cell => (cell.name, cell.type, cell.value)) := by
    rw [description]
    exact List.mem_reverse.mpr (List.mem_map.mpr ⟨(entry, value), selected, rfl⟩)
  obtain ⟨cell, member, same⟩ := List.mem_map.mp described
  obtain ⟨named', _, valueSame⟩ := Prod.mk.inj same |>.imp_right Prod.mk.inj
  exact ⟨cell, member, named'.trans named, valueSame⟩

def frameExpected (frameValues : List Core.Value) (gas code codeSize codeKnown : Core.Value) : String → Option Core.Value
  | "memory" | "returnData" => some (Core.WordMapping.encode [])
  | "address" => frameValues[0]?
  | "caller" => frameValues[1]?
  | "callvalue" => frameValues[2]?
  | "isStatic" => frameValues[3]?
  | "callDepth" => frameValues[4]?
  | "availableGas" => some gas
  | "calldata" => frameValues[6]?
  | "calldataSize" => frameValues[7]?
  | "callHandler" | "callCodeHandler" | "delegateCallHandler" => none
  | "code" => some code
  | "codeSize" => some codeSize
  | "codeKnown" => some codeKnown
  | _ => some (.word (Core.Word.ofNatModulo 0))

theorem frameExpected_related {depth : Nat} {environment : Core.Environment}
    {frame dispatcher gas code codeSize codeKnown : Code} {values : List Core.Value}
    {gasValue codeValue sizeValue knownValue : Core.Value}
    (frameRelated : CodeValue depth environment frame (bundleValues values))
    (length : values.length = 8)
    (gasRelated : CodeValue depth environment gas gasValue)
    (codeRelated : CodeValue depth environment code codeValue)
    (sizeRelated : CodeValue depth environment codeSize sizeValue)
    (knownRelated : CodeValue depth environment codeKnown knownValue)
    {name : String} {value : Core.Value}
    (expected : frameExpected values gasValue codeValue sizeValue knownValue name = some value) :
    CodeValue depth environment (AccountRuntime.frameInitial name frame dispatcher gas code codeSize codeKnown) value := by
  unfold frameExpected at expected
  split at expected <;> solve
    | cases expected
    | (cases expected; exact CodeValue.empty depth environment)
    | (cases expected; exact gasRelated)
    | (cases expected; exact codeRelated)
    | (cases expected; exact sizeRelated)
    | (cases expected; exact knownRelated)
    | (cases expected; simpa [AccountRuntime.frameInitial, *] using CodeValue.number 0 depth environment)
    | (simpa only [AccountRuntime.frameInitial, length] using frameRelated.part expected)

theorem frameInitializers_valid {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {frame dispatcher gas code codeSize codeKnown : Code} {shared : AccountRuntime.References} {values : List Core.Value}
    {gasValue codeValue sizeValue knownValue : Core.Value} {property : InitializedCell → Prop}
    (frameRelated : CodeValue depth environment frame (bundleValues values))
    (length : values.length = 8)
    (gasRelated : CodeValue depth environment gas gasValue)
    (codeRelated : CodeValue depth environment code codeValue)
    (sizeRelated : CodeValue depth environment codeSize sizeValue)
    (knownRelated : CodeValue depth environment codeKnown knownValue)
    (valid : ∀ name type location value, shared.find? (·.1 == name) = none → store.length ≤ location →
      (∀ expected, frameExpected values gasValue codeValue sizeValue knownValue name = some expected → value = expected) →
      property ⟨name, type, location, value⟩) :
    FrameInitializersValid depth environment store frame dispatcher gas code codeSize codeKnown shared property := by
  intro extra suffix name type absent
  obtain ⟨value, evaluated⟩ := frameInitializers_ready frameRelated length gasRelated codeRelated sizeRelated knownRelated
    extra name (store ++ suffix)
  refine ⟨value, evaluated, valid name type (store ++ suffix).length value absent (by simp) ?_⟩
  intro expected specified
  exact (Core.evaluation_deterministic evaluated
    (frameExpected_related frameRelated length gasRelated codeRelated sizeRelated knownRelated specified extra (store ++ suffix))).1

end Solcore.Frontend.RustHull.Correspondence
