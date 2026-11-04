import Solcore.Frontend.RustHull.Internal.RuntimeFrames
import Solcore.Frontend.RustHull.Internal.LoweringFacts
import Solcore.Frontend.RustHull.Internal.StorageState
import Solcore.Frontend.RustHull.Internal.Derivations
import Solcore.Frontend.RustHull.Internal.NamedFunctions
import Solcore.Frontend.RustHull.Internal.EffectBuiltins
import Solcore.Frontend.RustHull.Internal.MemoryState
import Solcore.Frontend.RustHull.AccountRuntime

/-!
# Runtime objects

Object initialization, allocation locations, installed callbacks and the code catalog, and the first
memory contract layer.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeReferenceFacts
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeAllocationLocations
/-! Actual runtime allocations give differently named cells distinct locations.
Repeated references to a shared cell remain valid. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open CodeBuilder ScalarExecution

def CellLocations (cells : List InitializedCell) : Prop :=
  ∀ left ∈ cells, ∀ right ∈ cells, left.location = right.location → left.name = right.name

theorem CellLocations.subset {cells smaller : List InitializedCell}
    (separate : CellLocations cells) (included : ∀ cell ∈ smaller, cell ∈ cells) :
    CellLocations smaller := fun left member right member' =>
  separate left (included left member) right (included right member')

theorem CellLocations.nil : CellLocations [] := by
  intro cell member
  cases member

theorem CellLocations.fresh {cells : List InitializedCell} {store : Core.Store}
    (separate : CellLocations cells) (initialized : InitializedCells cells store)
    (name : String) (type : Core.Ty) (value : Core.Value) :
    CellLocations (⟨name, type, store.length, value⟩ :: cells) := by
  intro left member right member' same
  cases member with
  | head =>
      cases member' with
      | head => rfl
      | tail _ member' =>
          have below := initialized.location_bound member'
          simp only at same
          omega
  | tail _ member =>
      cases member' with
      | head =>
          have below := initialized.location_bound member
          simp only at same
          omega
      | tail _ member' => exact separate left member right member' same

theorem CellLocations.different {cells : List InitializedCell} (separate : CellLocations cells)
    {left right : InitializedCell} (leftMember : left ∈ cells) (rightMember : right ∈ cells)
    (different : left.name ≠ right.name) : left.location ≠ right.location :=
  fun same => different (separate left leftMember right rightMember same)

theorem CellLocations.nodup {cells : List InitializedCell} (separate : CellLocations cells)
    (names : (cells.map InitializedCell.name).Nodup) :
    (cells.map InitializedCell.location).Nodup := by
  induction cells with
  | nil => exact List.nodup_nil
  | cons cell rest ih =>
      obtain ⟨absent, unique⟩ := List.nodup_cons.mp names
      apply List.nodup_cons.mpr
      constructor
      · intro present
        obtain ⟨other, member, same⟩ := List.mem_map.mp present
        apply absent
        exact List.mem_map.mpr ⟨other, member, separate other (.tail _ member) cell (.head _) same⟩
      · exact ih (separate.subset (fun _ member => .tail _ member)) unique

theorem allocateSharedSlots_separates
    {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {initializers : List (String × Core.Ty × Code)} {initialValues : List Core.Value}
    (inputs : CodeValues depth environment (initializers.map (·.2.2)) initialValues)
    {references : AccountRuntime.References} {cells : List InitializedCell}
    (related : RuntimeReferences depth environment references cells)
    (initialized : InitializedCells cells store)
    (separate : CellLocations cells) :
    ∃ extra suffix finalReferences finalCells,
      RuntimeReferences (depth + extra.length) (extra ++ environment) finalReferences finalCells ∧
      InitializedCells finalCells (store ++ suffix) ∧
      CellLocations finalCells ∧
      finalCells.map (fun cell => (cell.name, cell.type, cell.value)) =
        ((initializers.zip initialValues).map (fun (entry, value) => (entry.1, entry.2.1, value))).reverse ++
          cells.map (fun cell => (cell.name, cell.type, cell.value)) ∧
      ∀ continuation result finalStore,
        Core.Evaluates (extra ++ environment) (store ++ suffix)
          (continuation finalReferences (depth + extra.length)) result finalStore →
        Core.Evaluates environment store
          (AccountRuntime.allocateSharedSlots continuation initializers references depth) result finalStore := by
  induction initializers generalizing depth environment store initialValues references cells with
  | nil =>
      cases inputs
      refine ⟨[], [], references, cells, ?_, ?_, separate, rfl, ?_⟩
      · simpa using related
      · simpa using initialized
      · intro continuation result finalStore evaluated
        simpa [AccountRuntime.allocateSharedSlots] using evaluated
  | cons entry rest ih =>
      rcases entry with ⟨name, type, code⟩
      cases inputs with
      | @cons _ value _ values head tail =>
          let reference : Core.Value := .cellRef type store.length
          let bound : Code := fun here => .var (here - depth - 1)
          let cell : InitializedCell := ⟨name, type, store.length, value⟩
          have earlier := related.prepend [reference]
          have nextRelated : RuntimeReferences (depth + 1) (reference :: environment)
              ((name, bound) :: references) (cell :: cells) := by
            refine ⟨congrArg (name :: ·) related.names, .cons ?_ ?_⟩
            · exact CodeValue.bound depth environment reference
            · simpa using earlier.values
          obtain ⟨extra, suffix, finalReferences, finalCells, finalRelated, finalInitialized, finalSeparate, description, evaluated⟩ :=
            ih (by simpa using tail.prepend [reference]) nextRelated (initialized.cons name type value) (separate.fresh initialized name type value)
          refine ⟨extra ++ [reference], [value] ++ suffix, finalReferences, finalCells, ?_, ?_, finalSeparate, ?_, ?_⟩
          · simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using finalRelated
          · simpa only [List.append_assoc] using finalInitialized
          · simpa only [List.zip_cons_cons, List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append, cell] using description
          · intro continuation result finalStore completed
            apply Core.Evaluates.letE (.newCell (head.evaluates store))
            apply evaluated continuation result finalStore
            simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using completed

/-- The created cells, including that every cell for the create-handler slot
is one of the known cells, since the allocator reuses the installed creator. -/
theorem allocateFrameSlots_creates
    {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {slots : List (String × Core.Ty)} {shared : AccountRuntime.References}
    {frame dispatcher creator gas code codeSize codeKnown : Code}
    {property : InitializedCell → Prop} {known : List InitializedCell}
    (initializers : FrameInitializersValid depth environment store frame dispatcher gas code codeSize codeKnown shared property)
    (sharedReady : FrameSharedValid depth environment store slots shared (fun cell => property cell ∧ cell ∈ known))
    (creatorReady : FrameCreatorValid depth environment store slots creator (fun cell => property cell ∧ cell ∈ known))
    {previous : List Code} {previousCells : List InitializedCell}
    (previousRelated : CodeValues depth environment previous (previousCells.map InitializedCell.reference))
    (previousStored : InitializedCells previousCells store)
    (previousValid : ∀ cell ∈ previousCells, property cell)
    (knownStored : InitializedCells known store)
    (separate : CellLocations (known ++ previousCells)) :
    ∃ extra suffix references cells,
      CodeValues (depth + extra.length) (extra ++ environment) references
        ((previousCells.reverse ++ cells).map InitializedCell.reference) ∧
      InitializedCells (previousCells.reverse ++ cells) (store ++ suffix) ∧
      cells.map (fun cell => (cell.name, cell.type)) = slots ∧
      (∀ cell ∈ previousCells.reverse ++ cells, property cell) ∧
      CellLocations (known ++ previousCells.reverse ++ cells) ∧
      (∀ cell ∈ cells, cell.name = "createHandler" → cell ∈ known) ∧
      ∀ continuation result finalStore,
        Core.Evaluates (extra ++ environment) (store ++ suffix)
          (continuation references (depth + extra.length)) result finalStore →
        Core.Evaluates environment store
          (AccountRuntime.allocateFrameSlots shared frame dispatcher creator gas code codeSize codeKnown
            continuation slots previous depth) result finalStore := by
  induction slots generalizing depth environment store previous previousCells with
  | nil =>
      refine ⟨[], [], previous.reverse, [], ?_, ?_, rfl, ?_, ?_, (fun _ member => by cases member), ?_⟩
      · simpa only [List.length_nil, Nat.add_zero, List.nil_append, List.append_nil, List.map_reverse]
          using previousRelated.reverse
      · intro cell member
        simpa only [List.append_nil] using previousStored cell (by simpa using member)
      · intro cell member
        exact previousValid cell (by simpa using member)
      · apply separate.subset
        intro cell member
        simpa only [List.mem_append, List.mem_reverse, List.not_mem_nil, or_false] using member
      · intro continuation result finalStore evaluated
        simpa only [List.length_nil, Nat.add_zero, List.nil_append, List.append_nil,
          AccountRuntime.allocateFrameSlots] using evaluated
  | cons slot rest ih =>
      rcases slot with ⟨name, type⟩
      have sharedTail : FrameSharedValid depth environment store rest shared (fun cell => property cell ∧ cell ∈ known) := by
        intro slot member
        exact sharedReady slot (.tail _ member)
      have creatorTail : FrameCreatorValid depth environment store rest creator (fun cell => property cell ∧ cell ∈ known) := by
        intro type member
        exact creatorReady type (.tail _ member)
      cases found : shared.find? (·.1 == name) with
      | some entry =>
          rcases entry with ⟨foundName, reference⟩
          obtain ⟨cell, named, typed, related, stored, valid⟩ := sharedReady (name, type) (.head _) foundName reference found
          have storedCons : InitializedCells (cell :: previousCells) store := by
            intro selected member
            cases member with
            | head => exact stored
            | tail _ member => exact previousStored selected member
          obtain ⟨extra, suffix, references, cells, related', stored', signature, valid', separate', creators', evaluated⟩ :=
            ih initializers sharedTail creatorTail (.cons related previousRelated) storedCons
                (by intro selected member; cases member with
                    | head => exact valid.1
                    | tail _ member => exact previousValid selected member) knownStored
                (by
                  apply separate.subset
                  intro selected member
                  simp only [List.mem_append, List.mem_cons] at member ⊢
                  rcases member with old | rfl | previous
                  · exact Or.inl old
                  · exact Or.inl valid.2
                  · exact Or.inr previous)
          refine ⟨extra, suffix, references, cell :: cells, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using related'
          · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using stored'
          · simp only [List.map_cons, named, typed, signature]
          · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using valid'
          · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using separate'
          · intro selected member creatorNamed
            cases member with
            | head => exact valid.2
            | tail _ member => exact creators' selected member creatorNamed
          · intro continuation result finalStore completed
            simpa only [AccountRuntime.allocateFrameSlots, found] using evaluated continuation result finalStore completed
      | none =>
          by_cases isCreator : name == "createHandler"
          · have named : name = "createHandler" := by simpa only [beq_iff_eq] using isCreator
            subst name
            obtain ⟨cell, named, typed, related, stored, valid⟩ := creatorReady type (.head _)
            have storedCons : InitializedCells (cell :: previousCells) store := by
              intro selected member
              cases member with
              | head => exact stored
              | tail _ member => exact previousStored selected member
            obtain ⟨extra, suffix, references, cells, related', stored', signature, valid', separate', creators', evaluated⟩ :=
              ih initializers sharedTail creatorTail (.cons related previousRelated) storedCons
                (by intro selected member; cases member with
                    | head => exact valid.1
                    | tail _ member => exact previousValid selected member) knownStored
                (by
                  apply separate.subset
                  intro selected member
                  simp only [List.mem_append, List.mem_cons] at member ⊢
                  rcases member with old | rfl | previous
                  · exact Or.inl old
                  · exact Or.inl valid.2
                  · exact Or.inr previous)
            refine ⟨extra, suffix, references, cell :: cells, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using related'
            · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using stored'
            · simp only [List.map_cons, named, typed, signature]
            · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using valid'
            · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using separate'
            · intro selected member creatorNamed
              cases member with
              | head => exact valid.2
              | tail _ member => exact creators' selected member creatorNamed
            · intro continuation result finalStore completed
              simpa only [AccountRuntime.allocateFrameSlots, found, beq_self_eq_true, ↓reduceIte]
                using evaluated continuation result finalStore completed
          · obtain ⟨value, initialized, valid⟩ := initializers [] [] name type found
            have initialized' : Core.Evaluates environment store
                (AccountRuntime.frameInitial name frame dispatcher gas code codeSize codeKnown depth) value store := by
              simpa using initialized
            let reference : Core.Value := .cellRef type store.length
            let cell : InitializedCell := ⟨name, type, store.length, value⟩
            have sharedTail' : FrameSharedValid (depth + 1) (reference :: environment) (store ++ [value]) rest shared
                (fun cell => property cell ∧ cell ∈ known) := by
              intro slot member foundName foundCode found'
              simpa using (sharedTail slot member foundName foundCode found').extend [reference] [value]
            have creatorTail' : FrameCreatorValid (depth + 1) (reference :: environment) (store ++ [value]) rest creator
                (fun cell => property cell ∧ cell ∈ known) := by
              intro type member
              simpa using (creatorTail type member).extend [reference] [value]
            have relatedCons : CodeValues (depth + 1) (reference :: environment)
                ((fun here => .var (here - depth - 1)) :: previous) ((cell :: previousCells).map InitializedCell.reference) :=
              .cons (CodeValue.bound depth environment reference) (by simpa using previousRelated.prepend [reference])
            obtain ⟨extra, suffix, references, cells, related', stored', signature, valid', separate', creators', evaluated⟩ :=
              ih (by simpa using initializers.extend [reference] [value]) sharedTail' creatorTail'
                relatedCons (previousStored.cons name type value)
                (by intro selected member; cases member with
                    | head => simpa only [List.append_nil] using valid
                    | tail _ member => exact previousValid selected member)
                (knownStored.appendStore [value])
                (by
                  have allStored : InitializedCells (known ++ previousCells) store := by
                    intro selected member
                    rcases List.mem_append.mp member with old | previous
                    · exact knownStored selected old
                    · exact previousStored selected previous
                  apply (separate.fresh allStored name type value).subset
                  intro selected member
                  simp only [List.mem_append, List.mem_cons] at member ⊢
                  rcases member with old | rfl | previous
                  · exact Or.inr (Or.inl old)
                  · exact Or.inl rfl
                  · exact Or.inr (Or.inr previous))
            refine ⟨extra ++ [reference], [value] ++ suffix, references, cell :: cells, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1, List.reverse_cons] using related'
            · simpa [List.append_assoc, List.reverse_cons] using stored'
            · exact congrArg ((name, type) :: ·) signature
            · simpa [List.append_assoc, List.reverse_cons] using valid'
            · simpa [List.append_assoc, List.reverse_cons] using separate'
            · intro selected member creatorNamed
              cases member with
              | head => exact False.elim (isCreator (by simpa only [beq_iff_eq] using creatorNamed))
              | tail _ member => exact creators' selected member creatorNamed
            · intro continuation result finalStore completed
              simp only [AccountRuntime.allocateFrameSlots, found, isCreator]
              apply Core.Evaluates.letE (.newCell initialized')
              apply evaluated continuation result finalStore
              simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using completed

theorem allocateFrameSlots_separates
    {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {slots : List (String × Core.Ty)} {shared : AccountRuntime.References}
    {frame dispatcher creator gas code codeSize codeKnown : Code}
    {property : InitializedCell → Prop} {known : List InitializedCell}
    (initializers : FrameInitializersValid depth environment store frame dispatcher gas code codeSize codeKnown shared property)
    (sharedReady : FrameSharedValid depth environment store slots shared (fun cell => property cell ∧ cell ∈ known))
    (creatorReady : FrameCreatorValid depth environment store slots creator (fun cell => property cell ∧ cell ∈ known))
    {previous : List Code} {previousCells : List InitializedCell}
    (previousRelated : CodeValues depth environment previous (previousCells.map InitializedCell.reference))
    (previousStored : InitializedCells previousCells store)
    (previousValid : ∀ cell ∈ previousCells, property cell)
    (knownStored : InitializedCells known store)
    (separate : CellLocations (known ++ previousCells)) :
    ∃ extra suffix references cells,
      CodeValues (depth + extra.length) (extra ++ environment) references
        ((previousCells.reverse ++ cells).map InitializedCell.reference) ∧
      InitializedCells (previousCells.reverse ++ cells) (store ++ suffix) ∧
      cells.map (fun cell => (cell.name, cell.type)) = slots ∧
      (∀ cell ∈ previousCells.reverse ++ cells, property cell) ∧
      CellLocations (known ++ previousCells.reverse ++ cells) ∧
      ∀ continuation result finalStore,
        Core.Evaluates (extra ++ environment) (store ++ suffix)
          (continuation references (depth + extra.length)) result finalStore →
        Core.Evaluates environment store
          (AccountRuntime.allocateFrameSlots shared frame dispatcher creator gas code codeSize codeKnown
            continuation slots previous depth) result finalStore := by
  obtain ⟨extra, suffix, references, cells, related, stored, signature, valid, separate', _, evaluated⟩ :=
    allocateFrameSlots_creates initializers sharedReady creatorReady previousRelated previousStored previousValid
      knownStored separate
  exact ⟨extra, suffix, references, cells, related, stored, signature, valid, separate', evaluated⟩

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeObjectInitializationCorrespondence
/-! The actual object wrapper captures its frame closures, installs callback
closures in fresh cells, and enters the same frame initializer as execution. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open CodeBuilder ScalarExecution

/-- A structural property of emitted callback syntax. -/
def LambdaCode (code : Code) : Prop :=
  ∀ depth, ∃ parameter result body, code depth = Core.Expr.lambda parameter result body

theorem LambdaCode.evaluates {code : Code} (lambda : LambdaCode code)
    (depth : Nat) (environment : Core.Environment) (store : Core.Store) :
    ∃ value, Core.Evaluates environment store (code depth) value store := by
  obtain ⟨parameter, result, body, same⟩ := lambda depth
  exact ⟨.closure parameter result body environment, same ▸ Core.Evaluates.lambda⟩

theorem objectHandlers_lambdas (slots : List (String × Core.Ty)) (count : Nat)
    (images : List (Nat × List UInt8)) (catalog : List AccountRuntime.CodeDefinition)
    (functions : Code) (shared : AccountRuntime.References) (dispatcher creator : Code) :
    LambdaCode (AccountRuntime.objectHandlers slots count images catalog functions shared dispatcher creator).1 ∧
    LambdaCode (AccountRuntime.objectHandlers slots count images catalog functions shared dispatcher creator).2 := by
  constructor <;> intro depth <;> exact ⟨_, _, _, rfl⟩

/-- Both callback cells are allocated and populated by their actual emitted
operations. All prior cells and all lexical values remain available to the
continuation. -/
theorem allocateCallbacks_initializes {depth : Nat} {environment : Core.Environment}
    {initial : Core.Store} {handlers : Code → Code → Code × Code}
    (closures : ∀ dispatcher creator, LambdaCode (handlers dispatcher creator).1 ∧ LambdaCode (handlers dispatcher creator).2) :
    ∃ dispatcher creator extra allocated,
      extra.length = 4 ∧ StoreRetains initial allocated ∧
      CodeValue (depth + extra.length) (extra ++ environment) dispatcher
        (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) initial.length) ∧
      CodeValue (depth + extra.length) (extra ++ environment) creator
        (.cellRef (Core.OptionalCell.cellType Creation.callbackType) (initial.length + 1)) ∧
      (∃ value, allocated.read? (initial.length + 1) = some value) ∧
      ∀ continuation result final,
        Core.Evaluates (extra ++ environment) allocated
          (continuation dispatcher creator (depth + extra.length)) result final →
        Core.Evaluates environment initial (AccountRuntime.allocateCallbacks handlers continuation depth) result final := by
  let dispatcher : Code := fun here => .var (here - depth - 1)
  let creator : Code := fun here => .var (here - (depth + 1) - 1)
  let dispatcherValue := Core.Value.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) initial.length
  let creatorValue := Core.Value.cellRef (Core.OptionalCell.cellType Creation.callbackType) (initial.length + 1)
  let allocated := initial ++ [Core.Value.inLeft AccountRuntime.dispatchCallbackType .unit,
    Core.Value.inLeft Creation.callbackType .unit]
  have dispatcherRelated := CodeValue.bound depth environment dispatcherValue
  have creatorRelated := CodeValue.bound (depth + 1) (dispatcherValue :: environment) creatorValue
  obtain ⟨dispatchClosure, dispatchEvaluated⟩ := ((closures dispatcher creator).1).evaluates
    (depth + 2) (creatorValue :: dispatcherValue :: environment) allocated
  let stored : Core.Store := allocated.set initial.length (.inRight .unit dispatchClosure)
  have dispatchFound : allocated.read? initial.length = some (.inLeft AccountRuntime.dispatchCallbackType .unit) := by
    simp [allocated, Core.Store.read?]
  have dispatchWritten : allocated.write? initial.length (.inRight .unit dispatchClosure) = some stored :=
    Core.Store.write?_eq_some_iff.mpr ⟨by simp [allocated], rfl⟩
  obtain ⟨createClosure, createEvaluated⟩ := ((closures dispatcher creator).2).evaluates
    (depth + 3) (.unit :: creatorValue :: dispatcherValue :: environment) stored
  let initialized : Core.Store := stored.set (initial.length + 1) (.inRight .unit createClosure)
  have createFound : stored.read? (initial.length + 1) = some (.inLeft Creation.callbackType .unit) := by
    rw [Core.Store.write?_preserves_other (location := initial.length) (otherLocation := initial.length + 1) dispatchWritten (Nat.succ_ne_self _)]
    simp [allocated, Core.Store.read?]
  have createWritten : stored.write? (initial.length + 1) (.inRight .unit createClosure) = some initialized :=
    Core.Store.write?_eq_some_iff.mpr ⟨by simp [stored, allocated], rfl⟩
  have retained : StoreRetains initial initialized := by
    constructor
    · simp [initialized, stored, allocated]
    · intro location bounded
      rw [Core.Store.write?_preserves_other (location := initial.length + 1) (otherLocation := location) createWritten (Nat.ne_of_lt (Nat.lt_trans bounded (Nat.lt_succ_self _))),
        Core.Store.write?_preserves_other (location := initial.length) (otherLocation := location) dispatchWritten (Nat.ne_of_lt bounded)]
      exact List.getElem?_append_left bounded
  refine ⟨dispatcher, creator, [Core.Value.unit, .unit, creatorValue, dispatcherValue], initialized,
    rfl, retained, dispatcherRelated.prepend [Core.Value.unit, .unit, creatorValue],
    creatorRelated.prepend [Core.Value.unit, .unit], ⟨_, Core.Store.write?_reads_written createWritten⟩, ?_⟩
  intro continuation result final completed
  unfold AccountRuntime.allocateCallbacks CodeBuilder.bind
  apply Core.Evaluates.letE (Core.OptionalCell.allocate_evaluates ..)
  have second := Core.OptionalCell.allocate_evaluates Creation.callbackType
    (dispatcherValue :: environment) (initial ++ [.inLeft AccountRuntime.dispatchCallbackType .unit])
  simp only [List.length_append, List.length_cons, List.length_nil, List.append_assoc] at second
  apply Core.Evaluates.letE second
  apply Core.Evaluates.letE
    (Core.Evaluates.storeCell (dispatcherRelated [creatorValue] allocated) dispatchFound
      (.inRight dispatchEvaluated) dispatchWritten)
  apply Core.Evaluates.letE
    (Core.Evaluates.storeCell (creatorRelated [Core.Value.unit] stored) createFound
      (.inRight createEvaluated) createWritten)
  exact completed

theorem allocateCallbacks_evaluates {depth : Nat} {environment : Core.Environment}
    {initial final : Core.Store} {result : Core.Value}
    {handlers : Code → Code → Code × Code} {continuation : Code → Code → Code}
    (closures : ∀ dispatcher creator, LambdaCode (handlers dispatcher creator).1 ∧ LambdaCode (handlers dispatcher creator).2)
    (continued : ∀ dispatcher creator extra allocated,
      extra.length = 4 → StoreRetains initial allocated →
      CodeValue (depth + extra.length) (extra ++ environment) dispatcher
        (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) initial.length) →
      CodeValue (depth + extra.length) (extra ++ environment) creator
        (.cellRef (Core.OptionalCell.cellType Creation.callbackType) (initial.length + 1)) →
      (∃ value, allocated.read? (initial.length + 1) = some value) →
      Core.Evaluates (extra ++ environment) allocated
        (continuation dispatcher creator (depth + extra.length)) result final) :
    Core.Evaluates environment initial (AccountRuntime.allocateCallbacks handlers continuation depth) result final := by
  obtain ⟨dispatcher, creator, extra, allocated, length, retained, dispatcherValue, creatorValue, creatorFound, evaluated⟩ :=
    allocateCallbacks_initializes (depth := depth) (environment := environment) (initial := initial) closures
  exact evaluated continuation result final
    (continued dispatcher creator extra allocated length retained dispatcherValue creatorValue creatorFound)

inductive CapturedClosures (environment : Core.Environment) : List Core.Expr → List Core.Value → Prop where
  | nil : CapturedClosures environment [] []
  | cons {expression expressions value values} (head : CapturedClosure expression environment value)
      (tail : CapturedClosures environment expressions values) :
      CapturedClosures environment (expression :: expressions) (value :: values)

theorem CapturedClosures.evaluates {environment : Core.Environment} {expressions : List Core.Expr}
    {values : List Core.Value} (related : CapturedClosures environment expressions values) (store : Core.Store) :
    Core.Evaluates environment store (bundle expressions) (bundleValues values) store := by
  induction related with
  | nil => exact .unit
  | cons head tail ih =>
      cases tail with
      | nil => exact head.evaluates store
      | cons next rest => exact .pair (head.evaluates store) ih

theorem compileFrame_captures {program : Program} {code : CodeBlock}
    {slots : List (String × Core.Ty)} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code slots fuel = .ok compiled)
    (environment : Core.Environment) : ∃ value, CapturedClosure compiled environment value := by
  obtain ⟨_, _, _, _, _, rfl⟩ := compileFrame_components accepted
  exact ⟨_, .lambda _ _ _ _⟩

theorem InitializedCells.retained {cells : List InitializedCell} {initial final : Core.Store}
    (initialized : InitializedCells cells initial) (retained : StoreRetains initial final) :
    InitializedCells cells final := by
  intro cell member
  have found := initialized cell member
  rw [retained.read cell.location (List.getElem?_eq_some_iff.mp found).1]
  exact found

/-- Frame closures, shared state and callback cells are created by the actual
object wrapper. The remaining continuation is precisely its top-level frame. -/
theorem objectRuntime_evaluates {depth : Nat} {environment : Core.Environment}
    {initial final : Core.Store} {result : Core.Value}
    {slots : List (String × Core.Ty)} {compiled : Core.Expr} {others : List Core.Expr}
    {images : List (Nat × List UInt8)} {codeBytes : Option (List UInt8)}
    {catalog : List AccountRuntime.CodeDefinition} {context : Code}
    {functionsValue initialValues : List Core.Value}
    (captured : CapturedClosures environment (compiled :: others) functionsValue)
    (inputs : CodeValues depth environment ((AccountRuntime.sharedInitializers context).map (·.2.2)) initialValues)
    (continued : ∀ functions shared dispatcher creator extra allocated cells dispatcherLocation creatorLocation,
      CodeValue (depth + extra.length) (extra ++ environment) functions (bundleValues functionsValue) →
      RuntimeReferences (depth + extra.length) (extra ++ environment) shared cells →
      InitializedCells cells allocated →
      cells.map (fun cell => (cell.name, cell.type, cell.value)) =
        (((AccountRuntime.sharedInitializers context).zip initialValues).map
          (fun (entry, value) => (entry.1, entry.2.1, value))).reverse →
      StoreRetains initial allocated →
      CodeValue (depth + extra.length) (extra ++ environment) dispatcher
        (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation) →
      CodeValue (depth + extra.length) (extra ++ environment) creator
        (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation) →
      (∃ value, allocated.read? creatorLocation = some value) →
      Core.Evaluates (extra ++ environment) allocated
        (AccountRuntime.objectFrame slots (others.length + 1) images codeBytes context functions shared dispatcher creator
          (depth + extra.length)) result final) :
    Core.Evaluates environment initial
      (AccountRuntime.objectRuntime slots compiled others images codeBytes catalog context depth) result final := by
  have packetEvaluated := captured.evaluates initial
  have bundleEvaluated : Core.Evaluates environment initial
      (packet ((compiled :: others).map constant) depth) (bundleValues functionsValue) initial := by
    simpa [packet, constant, Function.comp_def] using packetEvaluated
  unfold AccountRuntime.objectRuntime CodeBuilder.bind
  apply Core.Evaluates.letE bundleEvaluated
  let functions : Code := fun here => .var (here - depth - 1)
  have functionsRelated := CodeValue.bound depth environment (bundleValues functionsValue)
  have sharedInputs := inputs.prepend [bundleValues functionsValue]
  obtain ⟨sharedExtra, suffix, shared, cells, references, initialized, description, sharedEvaluated⟩ :=
    allocateSharedSlots_initializes sharedInputs
      (references := []) (cells := []) ⟨rfl, .nil⟩ (by intro cell member; cases member)
  apply sharedEvaluated
  apply allocateCallbacks_evaluates
    (fun dispatcher creator => objectHandlers_lambdas slots (others.length + 1) images catalog functions shared dispatcher creator)
  intro dispatcher creator callbackExtra allocated _ callbacksRetained dispatcherRelated creatorRelated creatorRead
  have allRetained : StoreRetains initial allocated := (StoreRetains.append initial suffix).trans callbacksRetained
  have functionsFinal := (functionsRelated.prepend sharedExtra).prepend callbackExtra
  have referencesFinal := references.prepend callbackExtra
  have initializedFinal := initialized.retained callbacksRetained
  have descriptionFinal : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip initialValues).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := by
    simpa only [List.map_nil, List.append_nil] using description
  have completed := continued functions shared dispatcher creator
    (callbackExtra ++ sharedExtra ++ [bundleValues functionsValue]) allocated cells
    (initial ++ suffix).length ((initial ++ suffix).length + 1)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using functionsFinal)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using referencesFinal)
    initializedFinal descriptionFinal allRetained
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using dispatcherRelated)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using creatorRelated) creatorRead
  simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using completed

theorem objectRuntime_evaluates_some {depth : Nat} {environment : Core.Environment}
    {initial : Core.Store} {result : Core.Value}
    {slots : List (String × Core.Ty)} {compiled : Core.Expr} {others : List Core.Expr}
    {images : List (Nat × List UInt8)} {codeBytes : Option (List UInt8)}
    {catalog : List AccountRuntime.CodeDefinition} {context : Code}
    {functionsValue initialValues : List Core.Value}
    (captured : CapturedClosures environment (compiled :: others) functionsValue)
    (inputs : CodeValues depth environment ((AccountRuntime.sharedInitializers context).map (·.2.2)) initialValues)
    (continued : ∀ functions shared dispatcher creator extra allocated cells dispatcherLocation creatorLocation,
      CodeValue (depth + extra.length) (extra ++ environment) functions (bundleValues functionsValue) →
      RuntimeReferences (depth + extra.length) (extra ++ environment) shared cells →
      InitializedCells cells allocated →
      cells.map (fun cell => (cell.name, cell.type, cell.value)) =
        (((AccountRuntime.sharedInitializers context).zip initialValues).map
          (fun (entry, value) => (entry.1, entry.2.1, value))).reverse →
      StoreRetains initial allocated →
      CodeValue (depth + extra.length) (extra ++ environment) dispatcher
        (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation) →
      CodeValue (depth + extra.length) (extra ++ environment) creator
        (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation) →
      (∃ value, allocated.read? creatorLocation = some value) →
      ∃ final, Core.Evaluates (extra ++ environment) allocated
        (AccountRuntime.objectFrame slots (others.length + 1) images codeBytes context functions shared dispatcher creator
          (depth + extra.length)) result final) :
    ∃ final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime slots compiled others images codeBytes catalog context depth) result final := by
  have packetEvaluated := captured.evaluates initial
  have bundleEvaluated : Core.Evaluates environment initial
      (packet ((compiled :: others).map constant) depth) (bundleValues functionsValue) initial := by
    simpa [packet, constant, Function.comp_def] using packetEvaluated
  let functions : Code := fun here => .var (here - depth - 1)
  have functionsRelated := CodeValue.bound depth environment (bundleValues functionsValue)
  have sharedInputs := inputs.prepend [bundleValues functionsValue]
  obtain ⟨sharedExtra, suffix, shared, cells, references, initialized, description, sharedEvaluated⟩ :=
    allocateSharedSlots_initializes sharedInputs
      (references := []) (cells := []) ⟨rfl, .nil⟩ (by intro cell member; cases member)
  obtain ⟨dispatcher, creator, callbackExtra, allocated, _, callbacksRetained, dispatcherRelated, creatorRelated, creatorRead, callbacksEvaluated⟩ :=
    allocateCallbacks_initializes (depth := depth + 1 + sharedExtra.length)
      (environment := sharedExtra ++ bundleValues functionsValue :: environment) (initial := initial ++ suffix)
      (fun dispatcher creator => objectHandlers_lambdas slots (others.length + 1) images catalog functions shared dispatcher creator)
  have allRetained : StoreRetains initial allocated := (StoreRetains.append initial suffix).trans callbacksRetained
  have functionsFinal := (functionsRelated.prepend sharedExtra).prepend callbackExtra
  have referencesFinal := references.prepend callbackExtra
  have initializedFinal := initialized.retained callbacksRetained
  have descriptionFinal : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip initialValues).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := by
    simpa only [List.map_nil, List.append_nil] using description
  obtain ⟨final, completed⟩ := continued functions shared dispatcher creator
    (callbackExtra ++ sharedExtra ++ [bundleValues functionsValue]) allocated cells
    (initial ++ suffix).length ((initial ++ suffix).length + 1)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using functionsFinal)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using referencesFinal)
    initializedFinal descriptionFinal allRetained
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using dispatcherRelated)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using creatorRelated) creatorRead
  refine ⟨final, Core.Evaluates.letE bundleEvaluated ?_⟩
  apply sharedEvaluated
  apply callbacksEvaluated
  simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using completed

theorem objectRuntime_evaluates_result {depth : Nat} {environment : Core.Environment}
    {initial : Core.Store} (observes : Core.Value → Core.Store → Prop)
    {slots : List (String × Core.Ty)} {compiled : Core.Expr} {others : List Core.Expr}
    {images : List (Nat × List UInt8)} {codeBytes : Option (List UInt8)}
    {catalog : List AccountRuntime.CodeDefinition} {context : Code}
    {functionsValue initialValues : List Core.Value}
    (captured : CapturedClosures environment (compiled :: others) functionsValue)
    (inputs : CodeValues depth environment ((AccountRuntime.sharedInitializers context).map (·.2.2)) initialValues)
    (continued : ∀ functions shared dispatcher creator extra allocated cells dispatcherLocation creatorLocation,
      CodeValue (depth + extra.length) (extra ++ environment) functions (bundleValues functionsValue) →
      RuntimeReferences (depth + extra.length) (extra ++ environment) shared cells →
      InitializedCells cells allocated →
      cells.map (fun cell => (cell.name, cell.type, cell.value)) =
        (((AccountRuntime.sharedInitializers context).zip initialValues).map
          (fun (entry, value) => (entry.1, entry.2.1, value))).reverse →
      StoreRetains initial allocated →
      CodeValue (depth + extra.length) (extra ++ environment) dispatcher
        (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation) →
      CodeValue (depth + extra.length) (extra ++ environment) creator
        (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation) →
      (∃ value, allocated.read? creatorLocation = some value) →
      ∃ result final, Core.Evaluates (extra ++ environment) allocated
        (AccountRuntime.objectFrame slots (others.length + 1) images codeBytes context functions shared dispatcher creator
          (depth + extra.length)) result final ∧ observes result final) :
    ∃ result final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime slots compiled others images codeBytes catalog context depth) result final ∧ observes result final := by
  have packetEvaluated := captured.evaluates initial
  have bundleEvaluated : Core.Evaluates environment initial
      (packet ((compiled :: others).map constant) depth) (bundleValues functionsValue) initial := by
    simpa [packet, constant, Function.comp_def] using packetEvaluated
  let functions : Code := fun here => .var (here - depth - 1)
  have functionsRelated := CodeValue.bound depth environment (bundleValues functionsValue)
  have sharedInputs := inputs.prepend [bundleValues functionsValue]
  obtain ⟨sharedExtra, suffix, shared, cells, references, initialized, description, sharedEvaluated⟩ :=
    allocateSharedSlots_initializes sharedInputs
      (references := []) (cells := []) ⟨rfl, .nil⟩ (by intro cell member; cases member)
  obtain ⟨dispatcher, creator, callbackExtra, allocated, _, callbacksRetained, dispatcherRelated, creatorRelated, creatorRead, callbacksEvaluated⟩ :=
    allocateCallbacks_initializes (depth := depth + 1 + sharedExtra.length)
      (environment := sharedExtra ++ bundleValues functionsValue :: environment) (initial := initial ++ suffix)
      (fun dispatcher creator => objectHandlers_lambdas slots (others.length + 1) images catalog functions shared dispatcher creator)
  have allRetained : StoreRetains initial allocated := (StoreRetains.append initial suffix).trans callbacksRetained
  have functionsFinal := (functionsRelated.prepend sharedExtra).prepend callbackExtra
  have referencesFinal := references.prepend callbackExtra
  have initializedFinal := initialized.retained callbacksRetained
  have descriptionFinal : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip initialValues).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := by
    simpa only [List.map_nil, List.append_nil] using description
  obtain ⟨result, final, completed, observed⟩ := continued functions shared dispatcher creator
    (callbackExtra ++ sharedExtra ++ [bundleValues functionsValue]) allocated cells
    (initial ++ suffix).length ((initial ++ suffix).length + 1)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using functionsFinal)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using referencesFinal)
    initializedFinal descriptionFinal allRetained
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using dispatcherRelated)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using creatorRelated) creatorRead
  refine ⟨result, final, Core.Evaluates.letE bundleEvaluated ?_, observed⟩
  apply sharedEvaluated
  apply callbacksEvaluated
  simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using completed

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeObjectLocationsCorrespondence
/-! Shared and callback allocations preserve concrete cell separation for public execution. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open CodeBuilder ScalarExecution

theorem objectRuntime_evaluates_separated {depth : Nat} {environment : Core.Environment}
    {initial : Core.Store} (observes : Core.Value → Core.Store → Prop)
    {slots : List (String × Core.Ty)} {compiled : Core.Expr} {others : List Core.Expr}
    {images : List (Nat × List UInt8)} {codeBytes : Option (List UInt8)}
    {catalog : List AccountRuntime.CodeDefinition} {context : Code}
    {functionsValue initialValues : List Core.Value}
    (captured : CapturedClosures environment (compiled :: others) functionsValue)
    (inputs : CodeValues depth environment ((AccountRuntime.sharedInitializers context).map (·.2.2)) initialValues)
    (continued : ∀ functions shared dispatcher creator extra allocated cells dispatcherLocation creatorLocation,
      CodeValue (depth + extra.length) (extra ++ environment) functions (bundleValues functionsValue) →
      RuntimeReferences (depth + extra.length) (extra ++ environment) shared cells →
      InitializedCells cells allocated →
      CellLocations cells →
      cells.map (fun cell => (cell.name, cell.type, cell.value)) =
        (((AccountRuntime.sharedInitializers context).zip initialValues).map
          (fun (entry, value) => (entry.1, entry.2.1, value))).reverse →
      StoreRetains initial allocated →
      CodeValue (depth + extra.length) (extra ++ environment) dispatcher
        (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation) →
      CodeValue (depth + extra.length) (extra ++ environment) creator
        (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation) →
      (∃ value, allocated.read? creatorLocation = some value) →
      (∀ cell ∈ cells, cell.location < creatorLocation) →
      ∃ result final, Core.Evaluates (extra ++ environment) allocated
        (AccountRuntime.objectFrame slots (others.length + 1) images codeBytes context functions shared dispatcher creator
          (depth + extra.length)) result final ∧ observes result final) :
    ∃ result final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime slots compiled others images codeBytes catalog context depth) result final ∧ observes result final := by
  have packetEvaluated := captured.evaluates initial
  have bundleEvaluated : Core.Evaluates environment initial
      (packet ((compiled :: others).map constant) depth) (bundleValues functionsValue) initial := by
    simpa [packet, constant, Function.comp_def] using packetEvaluated
  let functions : Code := fun here => .var (here - depth - 1)
  have functionsRelated := CodeValue.bound depth environment (bundleValues functionsValue)
  have sharedInputs := inputs.prepend [bundleValues functionsValue]
  obtain ⟨sharedExtra, suffix, shared, cells, references, initialized, separate, description, sharedEvaluated⟩ :=
    allocateSharedSlots_separates sharedInputs
      (references := []) (cells := []) ⟨rfl, .nil⟩ (by intro cell member; cases member) CellLocations.nil
  obtain ⟨dispatcher, creator, callbackExtra, allocated, _, callbacksRetained, dispatcherRelated, creatorRelated, creatorRead, callbacksEvaluated⟩ :=
    allocateCallbacks_initializes (depth := depth + 1 + sharedExtra.length)
      (environment := sharedExtra ++ bundleValues functionsValue :: environment) (initial := initial ++ suffix)
      (fun dispatcher creator => objectHandlers_lambdas slots (others.length + 1) images catalog functions shared dispatcher creator)
  have allRetained : StoreRetains initial allocated := (StoreRetains.append initial suffix).trans callbacksRetained
  have functionsFinal := (functionsRelated.prepend sharedExtra).prepend callbackExtra
  have referencesFinal := references.prepend callbackExtra
  have initializedFinal := initialized.retained callbacksRetained
  have descriptionFinal : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip initialValues).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := by
    simpa only [List.map_nil, List.append_nil] using description
  obtain ⟨result, final, completed, observed⟩ := continued functions shared dispatcher creator
    (callbackExtra ++ sharedExtra ++ [bundleValues functionsValue]) allocated cells
    (initial ++ suffix).length ((initial ++ suffix).length + 1)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using functionsFinal)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using referencesFinal)
    initializedFinal separate descriptionFinal allRetained
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using dispatcherRelated)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using creatorRelated) creatorRead
    (fun cell member => Nat.lt_trans (initialized.location_bound member) (Nat.lt_succ_self _))
  refine ⟨result, final, Core.Evaluates.letE bundleEvaluated ?_, observed⟩
  apply sharedEvaluated
  apply callbacksEvaluated
  simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using completed

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractCatalogCorrespondence
/-! Public compilation selects every catalog frame and installs its actual
closure. These facts retain the ordering used by the runtime dispatcher. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractCatalogCorrespondence
open Correspondence ScalarExecution CodeBuilder

def slots (codeBytes : Option (List UInt8)) (catalog : List AccountRuntime.CodeDefinition) :
    List (String × Core.Ty) :=
  Effects.slots ++ if codeBytes.isSome || !catalog.isEmpty then Effects.codeSlots else []

def images (codeBytes : Option (List UInt8)) (catalog : List AccountRuntime.CodeDefinition) :
    List (Nat × List UInt8) :=
  codeBytes.toList.map (1, ·) ++ catalog.zipIdx.filterMap fun (definition, index) =>
    if definition.isInit then none else some (index + 2, definition.bytes)

def compileDefinition (slotTypes : List (String × Core.Ty)) (fuel : Nat)
    (definition : AccountRuntime.CodeDefinition) : LowerM Core.Expr := do
  AccountRuntime.compileFrame definition.program
    (← AccountRuntime.select definition.program.objects definition.path) slotTypes fuel

inductive CompiledCatalog (slotTypes : List (String × Core.Ty)) (fuel : Nat) :
    List AccountRuntime.CodeDefinition → List Core.Expr → Prop where
  | nil : CompiledCatalog slotTypes fuel [] []
  | cons {definition : AccountRuntime.CodeDefinition} {code : CodeBlock} {compiled : Core.Expr}
      {definitions : List AccountRuntime.CodeDefinition} {expressions : List Core.Expr}
      (selected : AccountRuntime.select definition.program.objects definition.path = .ok code)
      (accepted : AccountRuntime.compileFrame definition.program code slotTypes fuel = .ok compiled)
      (tail : CompiledCatalog slotTypes fuel definitions expressions) :
      CompiledCatalog slotTypes fuel (definition :: definitions) (compiled :: expressions)

theorem compiledCatalog {slotTypes : List (String × Core.Ty)} {fuel : Nat}
    {catalog : List AccountRuntime.CodeDefinition} {expressions : List Core.Expr}
    (accepted : catalog.mapM (compileDefinition slotTypes fuel) = .ok expressions) :
    CompiledCatalog slotTypes fuel catalog expressions := by
  induction catalog generalizing expressions with
  | nil => cases accepted; exact .nil
  | cons definition definitions ih =>
      simp only [List.mapM_cons] at accepted
      obtain ⟨expression, head, accepted⟩ := lower_bind_eq_ok.mp accepted
      obtain ⟨rest, tail, returned⟩ := lower_bind_eq_ok.mp accepted
      cases returned
      obtain ⟨code, selected, accepted⟩ := lower_bind_eq_ok.mp head
      exact .cons selected accepted (ih tail)

theorem CompiledCatalog.length {slotTypes : List (String × Core.Ty)} {fuel : Nat}
    {catalog : List AccountRuntime.CodeDefinition} {expressions : List Core.Expr}
    (accepted : CompiledCatalog slotTypes fuel catalog expressions) : expressions.length = catalog.length := by
  induction accepted with
  | nil => rfl
  | cons _ _ _ ih => exact congrArg Nat.succ ih

theorem CompiledCatalog.selected {slotTypes : List (String × Core.Ty)} {fuel : Nat}
    {catalog : List AccountRuntime.CodeDefinition} {expressions : List Core.Expr}
    (accepted : CompiledCatalog slotTypes fuel catalog expressions)
    {index : Nat} {definition : AccountRuntime.CodeDefinition}
    (found : catalog[index]? = some definition) :
    ∃ code compiled, expressions[index]? = some compiled ∧
      AccountRuntime.select definition.program.objects definition.path = .ok code ∧
      AccountRuntime.compileFrame definition.program code slotTypes fuel = .ok compiled := by
  induction accepted generalizing index with
  | nil => simp at found
  | @cons head code compiled definitions rest selected accepted tail ih =>
      cases index with
      | zero =>
          have same : head = definition := Option.some.inj found
          subst definition
          exact ⟨code, compiled, rfl, selected, accepted⟩
      | succ index => exact ih found

theorem CompiledCatalog.captures {slotTypes : List (String × Core.Ty)} {fuel : Nat}
    {catalog : List AccountRuntime.CodeDefinition} {expressions : List Core.Expr}
    (accepted : CompiledCatalog slotTypes fuel catalog expressions) (environment : Core.Environment) :
    ∃ values, CapturedClosures environment expressions values := by
  induction accepted with
  | nil => exact ⟨[], .nil⟩
  | cons _ accepted _ ih =>
      obtain ⟨value, captured⟩ := compileFrame_captures accepted environment
      obtain ⟨values, captures⟩ := ih
      exact ⟨value :: values, .cons captured captures⟩

theorem captured_length {environment : Core.Environment} {expressions : List Core.Expr}
    {values : List Core.Value} (captured : CapturedClosures environment expressions values) :
    values.length = expressions.length := by
  induction captured with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem captured_selected {environment : Core.Environment} {expressions : List Core.Expr}
    {values : List Core.Value} (captured : CapturedClosures environment expressions values)
    {index : Nat} {expression : Core.Expr} (found : expressions[index]? = some expression) :
    ∃ value, values[index]? = some value ∧ CapturedClosure expression environment value := by
  induction captured generalizing index with
  | nil => simp at found
  | @cons head rest value values captured tail ih =>
      cases index with
      | zero =>
          have same : head = expression := Option.some.inj found
          subst expression
          exact ⟨value, rfl, captured⟩
      | succ index => exact ih found

/-- Every catalog entry is compiled in order with exactly the entry frame's
extended slot list, including entries used only as creation templates. -/
theorem compileObject_selected {program : Program} {path : List String} {code : CodeBlock}
    {fuel : Nat} {codeBytes : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition}
    {expression : Core.Expr}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : AccountRuntime.compileObject program path fuel codeBytes catalog = .ok expression) :
    ∃ compiled others,
      AccountRuntime.compileFrame program code (slots codeBytes catalog) fuel = .ok compiled ∧
      catalog.mapM (compileDefinition (slots codeBytes catalog) fuel) = .ok others ∧
      expression = AccountRuntime.objectExpression (slots codeBytes catalog)
        compiled others (images codeBytes catalog) codeBytes catalog := by
  unfold AccountRuntime.compileObject at accepted
  obtain ⟨selectedCode, selectedAgain, accepted⟩ := lower_bind_eq_ok.mp accepted
  have same := Except.ok.inj (selectedAgain.symm.trans selected)
  subst selectedCode
  obtain ⟨compiled, compiledOk, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨others, mapped, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨guard, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  cases guard
  cases accepted
  exact ⟨compiled, others, compiledOk, mapped, rfl⟩

/-- Compilation itself supplies all closure-capture premises needed by the
generic object initializer; callers do not assume evaluation of a catalog. -/
theorem compileObject_captures {program : Program} {path : List String} {code : CodeBlock}
    {fuel : Nat} {codeBytes : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition}
    {expression : Core.Expr}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : AccountRuntime.compileObject program path fuel codeBytes catalog = .ok expression)
    (environment : Core.Environment) :
    ∃ compiled others closure values,
      AccountRuntime.compileFrame program code (slots codeBytes catalog) fuel = .ok compiled ∧
      CompiledCatalog (slots codeBytes catalog) fuel catalog others ∧
      CapturedClosure compiled environment closure ∧
      CapturedClosures environment others values ∧
      CapturedClosures environment (compiled :: others) (closure :: values) ∧
      values.length = catalog.length ∧
      expression = AccountRuntime.objectExpression (slots codeBytes catalog)
        compiled others (images codeBytes catalog) codeBytes catalog := by
  obtain ⟨compiled, others, frame, mapped, expression⟩ := compileObject_selected selected accepted
  have catalogCompiled := compiledCatalog mapped
  obtain ⟨closure, captured⟩ := compileFrame_captures frame environment
  obtain ⟨values, captures⟩ := catalogCompiled.captures environment
  exact ⟨compiled, others, closure, values, frame, catalogCompiled, captured, captures,
    .cons captured captures, (captured_length captures).trans catalogCompiled.length, expression⟩

/-- The top-level frame is index zero of the actual closure packet. -/
theorem entry_reference {depth : Nat} {environment captured : Core.Environment}
    {functions : Code} {closure : Core.Value} {values : List Core.Value} {others : List Core.Expr}
    (catalogCaptured : CapturedClosures captured others values)
    (functionsRelated : CodeValue depth environment functions (bundleValues (closure :: values))) :
    CodeValue depth environment (part 0 (others.length + 1) functions) closure := by
  have selected := functionsRelated.part (index := 0) rfl
  simpa only [List.length_cons, captured_length catalogCaptured] using selected

/-- Catalog index `index` is installed after the entry closure, at runtime
packet index `index + 1`, with its own selected program and capture. -/
theorem catalog_reference {slotTypes : List (String × Core.Ty)} {fuel depth : Nat}
    {catalog : List AccountRuntime.CodeDefinition} {others : List Core.Expr}
    {environment captured : Core.Environment} {functions : Code}
    {closure : Core.Value} {values : List Core.Value}
    (compiled : CompiledCatalog slotTypes fuel catalog others)
    (catalogCaptured : CapturedClosures captured others values)
    (functionsRelated : CodeValue depth environment functions (bundleValues (closure :: values)))
    {index : Nat} {definition : AccountRuntime.CodeDefinition} (found : catalog[index]? = some definition) :
    ∃ code expression value,
      AccountRuntime.select definition.program.objects definition.path = .ok code ∧
      AccountRuntime.compileFrame definition.program code slotTypes fuel = .ok expression ∧
      CapturedClosure expression captured value ∧
      CodeValue depth environment (part (index + 1) (others.length + 1) functions) value := by
  obtain ⟨code, expression, expressionFound, selected, accepted⟩ := compiled.selected found
  obtain ⟨value, valueFound, captured⟩ := captured_selected catalogCaptured expressionFound
  refine ⟨code, expression, value, selected, accepted, captured, ?_⟩
  have projected := functionsRelated.part (index := index + 1) valueFound
  simpa only [List.length_cons, captured_length catalogCaptured] using projected

end Solcore.Frontend.RustHull.ContractCatalogCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractInputCorrespondence
/-! Actual public contract instantiation supplies its normalized context,
linked account records and concrete runtime argument. Literal construction
leaves the store unchanged and introduces no execution assumptions. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open ScalarExecution

def optionalWordValue : Option Core.Word → Core.Value
  | none => .inLeft .word .unit
  | some value => .inRight .unit (.word value)

def optionalHashesValue : Option Core.WordMapping.Entries → Core.Value
  | none => .inLeft Core.WordMapping.type .unit
  | some entries => .inRight .unit (Core.WordMapping.encode entries)

theorem ambientWord_evaluates (word : Option Core.Word) (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates environment store (Ambient.wordLiteral word) (optionalWordValue word) store := by
  cases word with
  | none => exact .inLeft .unit
  | some word => exact .inRight .word

theorem ambientHashes_evaluates (hashes : Option Core.WordMapping.Entries)
    (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates environment store (Ambient.hashesLiteral hashes) (optionalHashesValue hashes) store := by
  cases hashes with
  | none => exact .inLeft .unit
  | some entries => exact .inRight (Core.WordMapping.literal_evaluates entries environment store)

def ambientValues (context : Ambient.Context) : List Core.Value :=
  [optionalWordValue context.origin, optionalWordValue context.gasprice,
   optionalWordValue context.coinbase, optionalWordValue context.timestamp,
   optionalWordValue context.number, optionalWordValue context.prevrandao,
   optionalWordValue context.gaslimit, optionalWordValue context.chainid,
   optionalWordValue context.basefee, optionalWordValue context.blobbasefee,
   optionalHashesValue context.blockHashes, optionalHashesValue (context.blobHashes.map Ambient.blobEntries)]

theorem ambientContext_evaluates (context : Ambient.Context) (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates environment store (Ambient.contextExpression context) (bundleValues (ambientValues context)) store :=
  .pair (ambientWord_evaluates _ _ _) (.pair (ambientWord_evaluates _ _ _)
    (.pair (ambientWord_evaluates _ _ _) (.pair (ambientWord_evaluates _ _ _)
    (.pair (ambientWord_evaluates _ _ _) (.pair (ambientWord_evaluates _ _ _)
    (.pair (ambientWord_evaluates _ _ _) (.pair (ambientWord_evaluates _ _ _)
    (.pair (ambientWord_evaluates _ _ _) (.pair (ambientWord_evaluates _ _ _)
    (.pair (ambientHashes_evaluates _ _ _) (ambientHashes_evaluates _ _ _)))))))))))

def contextValues (compiled : Contract.CompiledObject) (context : Contract.Context) : List Core.Value :=
  [Core.WordMapping.encode (Contract.calldataEntries context.calldata),
   .word (Core.Word.ofNatModulo context.calldata.length),
   .word context.value, .word context.caller, .word context.address, optionalWordValue context.availableGas,
   Core.WordMapping.encode (Core.WordMapping.insertEntries context.address context.balance context.accounts),
   StorageCorrespondence.world (StorageCorrespondence.canonical (compiled.initialWorld context)),
   .bool context.isStatic, .bool context.completeWorld,
   bundleValues (ambientValues context.ambient), .bool context.deploying]

theorem contextArgument_evaluates (compiled : Contract.CompiledObject) (context : Contract.Context)
    (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates environment store (compiled.contextArgument context)
      (bundleValues (contextValues compiled context)) store := by
  have gas : Core.Evaluates environment store
      (match context.availableGas with | none => .inLeft .word .unit | some value => .inRight .unit (.word value))
      (optionalWordValue context.availableGas) store := by
    cases context.availableGas with
    | none => exact .inLeft .unit
    | some value => exact .inRight .word
  exact .pair (Core.WordMapping.literal_evaluates _ _ _) (.pair .word (.pair .word (.pair .word
    (.pair .word (.pair gas (.pair (Core.WordMapping.literal_evaluates _ _ _)
    (.pair (StorageCorrespondence.literal_evaluates _ _ _) (.pair .bool (.pair .bool
    (.pair (ambientContext_evaluates _ _ _) .bool))))))))))

/-- The public constructor evaluates the actual context literal before entering
the compiled lambda. The source state can therefore be based on these exact
normalized inputs instead of an assumed argument representation. -/
theorem instantiate_evaluates {compiled : Contract.CompiledObject} (context : Contract.Context)
    {parameter resultType : Core.Ty} {body : Core.Expr}
    (expression : compiled.expression = .lambda parameter resultType body)
    {value : Core.Value} {store : Core.Store}
    (executed : Core.Evaluates [bundleValues (contextValues compiled (Contract.normalizeContext context))]
      [] body value store) :
    Core.Evaluates [] [] (compiled.instantiate context).expression value store := by
  change Core.Evaluates [] []
    (.apply compiled.expression (compiled.contextArgument (Contract.normalizeContext context))) value store
  rw [expression]
  exact .apply .lambda (contextArgument_evaluates compiled (Contract.normalizeContext context) [] []) executed

/-- Every genuine public resumption chain reaches exactly the receipt exported
from the instantiated lambda, at the cumulative transition count. -/
theorem instantiate_resumes_exact {compiled : Contract.CompiledObject} (context : Contract.Context)
    {parameter resultType : Core.Ty} {body : Core.Expr}
    (expression : compiled.expression = .lambda parameter resultType body)
    {value : Core.Value} {store : Core.Store}
    (executed : Core.Evaluates [bundleValues (contextValues compiled (Contract.normalizeContext context))]
      [] body value store) :
    ∃ required, ∀ fuel additional limit last,
      Contract.ReceiptResumes limit (Contract.runWithReceipt (compiled.instantiate context) fuel limit) additional last →
      (last = Contract.finish limit value ↔ required ≤ fuel + additional) ∧
      ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ fuel + additional < required) :=
  Contract.evaluation_resumes_exact (instantiate_evaluates context expression executed)

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeAssemblyCorrespondence
/-! Actual assembly with an initialized runtime scope. The compiler's global
allocation, installation and selected invocation retain the independent Hull
result and the concrete external-state representation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open ScalarExecution DerivationCorrespondence

/-- Runtime slot names cannot be shadowed by generated function-cell bindings. -/
def EffectSlotsSeparate (slots : List EffectSlot) : Prop :=
  ∀ slot ∈ slots, slot.name.startsWith "function$" = false

theorem effectSlot_ne_function {slots : List EffectSlot} (separated : EffectSlotsSeparate slots)
    {slot : EffectSlot} (member : slot ∈ slots) (name : String) :
    Effects.slotName ("function$" ++ name) ≠ Effects.slotName slot.name := by
  intro same
  have equal : "function$" ++ name = slot.name := by simpa [Effects.slotName] using same
  have forbidden := separated slot member
  rw [← equal] at forbidden
  simp at forbidden

theorem EffectEnvironmentRel.addFunction {slots : List EffectSlot} {scope : Scope}
    {environment : Core.Environment}
    (related : EffectEnvironmentRel slots scope Core.Renaming.id environment)
    (separated : EffectSlotsSeparate slots) (own : Signature) (value : Core.Value) :
    EffectEnvironmentRel slots (globalBinding own :: scope) Core.Renaming.id (value :: environment) := by
  intro slot member binding index looked
  rw [scope_lookup_cons] at looked
  have different := effectSlot_ne_function separated member own.name
  simp only [globalBinding, Option.some_beq_some, beq_eq_false_iff_ne.mpr different,
    Bool.false_eq_true, ↓reduceIte] at looked
  cases previous : scope.lookup (Effects.slotName slot.name) with
  | error error => simp only [previous] at looked; contradiction
  | ok found =>
      rcases found with ⟨oldBinding, oldIndex⟩
      simp only [previous, Except.ok.injEq, Prod.mk.injEq] at looked
      obtain ⟨rfl, rfl⟩ := looked
      exact related slot member oldBinding oldIndex previous

theorem ScopeCoverage.globalScope {source : Semantics.Environment} {runtime : Scope}
    (covered : ScopeCoverage source runtime) (signatures : List Signature) :
    ScopeCoverage source (globalScope signatures runtime) := by
  induction signatures generalizing runtime with
  | nil => exact covered
  | cons own rest ih =>
      have reserved := covered.reserved (globalBinding own) (by
        intro name named
        cases Option.some.inj named
        exact slotName_reserved _)
      simpa only [Correspondence.globalScope, globalBinding, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append] using ih reserved

/-- Extend the actual runtime environment by the exact function references
allocated by globalAllocation; the reversed lexical order is derived here. -/
theorem EffectEnvironmentRel.globalScope {slots : List EffectSlot} {runtime : Scope}
    {environment : Core.Environment}
    (related : EffectEnvironmentRel slots runtime Core.Renaming.id environment)
    (separated : EffectSlotsSeparate slots) (signatures : List Signature) (base : Nat) :
    EffectEnvironmentRel slots (globalScope signatures runtime) Core.Renaming.id
      (globalEnvironment signatures base environment) := by
  induction signatures generalizing runtime environment base with
  | nil => exact related
  | cons own rest ih =>
      have next := ih (related.addFunction separated own
        (.cellRef (Core.OptionalCell.cellType own.functionType) base)) (base + 1)
      simpa only [Correspondence.globalScope, globalBinding, globalEnvironment, List.reverse_cons, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc, List.singleton_append] using next

/-- The assembled expression runs in the real frame's runtime references,
followed by its input bundle and caller environment. All function cells and
captured runtime references come from this same successful assembly. The
revert and assembly obligations default to the vacuous proofs, which effect
layers without a revert or assembly rule meet. -/
theorem assemble_recursive_program_effects {supported : String → Prop} {σ : Type} {model : StateModel σ} {slots : List EffectSlot}
    {effects : Semantics.ExternalSemantics σ} {functions : List Function} {function : Function}
    {entry : String} {runtime : Scope} {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (external : ExternalCallPreservation supported model slots effects)
    (eligible : ExecutableProgram supported functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State σ} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions effects function sources initial sourceResult final)
    {world : World} {runtimeValues caller : Core.Environment} {store : Core.Store}
    (runtimeLength : runtimeValues.length = runtime.length)
    (covered : ScopeCoverage [] runtime)
    (runtimeRelated : EffectEnvironmentRel slots runtime Core.Renaming.id
      (runtimeValues ++ bundleValues targets :: caller))
    (separated : EffectSlotsSeparate slots)
    (state : StateRel model world initial store)
    (reverting : RevertPreservation supported model slots effects :=
      by exact RevertPreservation.unreachable (fun _ _ _ _ reverted => reverted))
    (assembling : AssemblyPreservation supported model slots effects :=
      by exact AssemblyPreservation.unreachable (fun _ _ _ _ _ _ assembled => assembled)) :
    ∃ extension target finalStore,
      ResultRel own.result sourceResult target ∧
      Core.Evaluates (runtimeValues ++ bundleValues targets :: caller) store allocated target finalStore ∧
      StateRel model (world ++ extension) final finalStore ∧ ClosuresPreserved store finalStore := by
  have sourceUnique := assemble_names_unique accepted
  obtain ⟨signatures, codes, sourceFunction, code, index, signaturesCompiled,
    sourceSelected, signatureCompiled, codesCompiled, codeFound, ownEqual,
    _, allocatedEqual⟩ := assemble_selection accepted
  have sameFunction := Option.some.inj (selected.symm.trans sourceSelected)
  subst sourceFunction
  subst own
  subst allocated
  have aligned := codesCompiled.aligned signaturesCompiled
  have signatureTable := compiledSignatures signaturesCompiled
  have unique : (signatures.map Signature.name).Nodup := by
    rw [signatureTable.names]
    exact sourceUnique
  obtain ⟨selectedOwn, signatureSelected, selectedCompiled⟩ := signatureTable.source_selected selected
  have sameOwn := Except.ok.inj (selectedCompiled.symm.trans signatureCompiled)
  subst selectedOwn
  have globals := GlobalEnvironmentRel.of_lookup aligned
    (scope := globalScope signatures runtime)
    (fun slot closure found => globalScope_lookup unique
      (by simp only [← aligned, List.getElem?_map, found, Option.map_some]) runtime)
    store.length (runtimeValues ++ bundleValues targets :: caller)
  have initialized := state.initializeGlobals signatures codes (runtimeValues ++ bundleValues targets :: caller)
  have installed := InstalledGlobals.initialize aligned (runtimeValues ++ bundleValues targets :: caller) store
  obtain ⟨extension, target, finalStore, related, executed, finalState, _, frame⟩ :=
    (DerivationProgramCorrespondence.function_preserves_effects signaturesCompiled codesCompiled unique
      (covered.globalScope signatures) globals (runtimeRelated.globalScope separated signatures store.length)
      external reverting assembling eligible evaluated) selected signatureSelected codeFound values initialized installed
  have invoked := globalInvocation_evaluates aligned codeFound installed executed
  have assembled := globalInitialization_evaluates aligned invoked
  have initialFrame : ClosuresPreserved store
      (initializedGlobals signatures codes (runtimeValues ++ bundleValues targets :: caller) store) := by
    intro location parameter result body environment found
    rw [(initializedGlobals_retains signatures codes (runtimeValues ++ bundleValues targets :: caller) store).read
      location (List.getElem?_eq_some_iff.mp found).1]
    exact found
  exact ⟨extension, target, finalStore, related, by simpa only [runtimeLength] using assembled,
    finalState, initialFrame.trans frame⟩

theorem assemble_recursive_program {σ : Type} {model : StateModel σ} {slots : List EffectSlot}
    {effects : Semantics.ExternalSemantics σ} {functions : List Function} {function : Function}
    {entry : String} {runtime : Scope} {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (eligible : RecursiveProgram functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State σ} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions effects function sources initial sourceResult final)
    {world : World} {runtimeValues caller : Core.Environment} {store : Core.Store}
    (runtimeLength : runtimeValues.length = runtime.length)
    (covered : ScopeCoverage [] runtime)
    (runtimeRelated : EffectEnvironmentRel slots runtime Core.Renaming.id
      (runtimeValues ++ bundleValues targets :: caller))
    (separated : EffectSlotsSeparate slots)
    (state : StateRel model world initial store) :
    ∃ extension target finalStore,
      ResultRel own.result sourceResult target ∧
      Core.Evaluates (runtimeValues ++ bundleValues targets :: caller) store allocated target finalStore ∧
      StateRel model (world ++ extension) final finalStore ∧ ClosuresPreserved store finalStore :=
  assemble_recursive_program_effects accepted selected
    (ExternalCallPreservation.empty model slots effects) eligible values evaluated runtimeLength
    covered runtimeRelated separated state (RevertPreservation.empty model slots effects)
    (AssemblyPreservation.empty model slots effects)

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.MemoryEffectCorrespondence
/-! Concrete memory effects discharge the external-call boundary of the mutual
Hull simulation. All other runtime resources retain their original observations;
source locals and installed closures are preserved across each memory operation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.MemoryEffectCorrespondence
open Correspondence DerivationCorrespondence ScalarExecution

structure Layout where
  boundary : Nat
  memory : Nat
  size : Nat
  distinct : memory ≠ size
  memoryBelow : memory < boundary
  sizeBelow : size < boundary

def resources (layout : Layout) (baseline : Nat → Option Core.Value)
    (state : MemorySemantics.State) (read : Nat → Option Core.Value) : Prop :=
  read layout.memory = some (Core.WordMapping.encode state.words) ∧
  read layout.size = some (.word state.size) ∧
  ∀ location, location ≠ layout.memory → location ≠ layout.size → read location = baseline location

def model (layout : Layout) (baseline : Nat → Option Core.Value) : StateModel MemorySemantics.State :=
  StateModel.cutoff layout.boundary (resources layout baseline)

theorem memory_related {layout : Layout} {baseline : Nat → Option Core.Value}
    {world : World} {state : Semantics.State MemorySemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline) world state store) :
    MemoryCorrespondence.StateRel layout.memory layout.size state.external store := by
  refine ⟨layout.distinct, ?_, ?_⟩
  · simpa only [prefixRead, layout.memoryBelow, ↓reduceIte] using related.external.2.2.1
  · simpa only [prefixRead, layout.sizeBelow, ↓reduceIte] using related.external.2.2.2.1

theorem frame_above {layout : Layout} {initial final : Core.Store}
    (frame : MemoryCorrespondence.Frame layout.memory layout.size initial final) :
    StoreRetainsFrom layout.boundary initial final := by
  refine ⟨frame.length, ?_⟩
  intro location separated bounded
  have found : initial.read? location = some initial[location] := List.getElem?_eq_getElem bounded
  rw [found]
  exact frame.read location _ (by have := layout.memoryBelow; omega)
    (by have := layout.sizeBelow; omega) found

theorem resources_preserved {layout : Layout} {baseline : Nat → Option Core.Value}
    {initial final : Core.Store} {before after : MemorySemantics.State}
    (bounded : layout.boundary ≤ initial.length)
    (resourcesBefore : resources layout baseline before (prefixRead layout.boundary initial))
    (memoryAfter : MemoryCorrespondence.StateRel layout.memory layout.size after final)
    (frame : MemoryCorrespondence.Frame layout.memory layout.size initial final) :
    resources layout baseline after (prefixRead layout.boundary final) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [prefixRead, layout.memoryBelow, ↓reduceIte] using memoryAfter.memory
  · simpa only [prefixRead, layout.sizeBelow, ↓reduceIte] using memoryAfter.size
  · intro location memory size
    rw [← resourcesBefore.2.2 location memory size]
    by_cases below : location < layout.boundary
    · simp only [prefixRead, below, ↓reduceIte]
      have bound : location < initial.length := Nat.lt_of_lt_of_le below bounded
      have found : initial.read? location = some initial[location] := List.getElem?_eq_getElem bound
      rw [found]
      exact frame.read location _ memory size found
    · simp only [prefixRead, below, ↓reduceIte]

theorem closures_preserved {memory size : Nat} {before : MemorySemantics.State}
    {initial final : Core.Store}
    (related : MemoryCorrespondence.StateRel memory size before initial)
    (frame : MemoryCorrespondence.Frame memory size initial final) :
    ClosuresPreserved initial final := by
  intro location parameter result body environment found
  apply frame.read location _ _ _ found
  · intro same
    subst location
    have equal := Option.some.inj (related.memory.symm.trans found)
    cases entries : before.words <;> simp only [entries, Core.WordMapping.encode] at equal <;> cases equal
  · intro same
    subst location
    have equal := Option.some.inj (related.size.symm.trans found)
    cases equal

def supported (name : String) : Prop := ∃ operation : MemoryBuiltinCorrespondence.Operation, operation.name = name

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (sizeMember : ⟨"memorySize", .word, layout.size⟩ ∈ slots) :
    ExternalCallPreservation supported (model layout baseline) slots MemorySemantics.effects := by
  intro functions name type sources initial final result available notFunction called
  obtain ⟨operation, rfl⟩ := available
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => cases operation <;> simp [MemoryBuiltinCorrespondence.Operation.name, Semantics.primitive?] at computed
  | external absent notPrimitive computed =>
      intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
      obtain ⟨computedResult, computedState, target, finalStore, meaning, resultRelated, evaluated, memoryFinal, frame⟩ :=
        MemoryBuiltinCorrespondence.preserves operation compiled related runtime memoryMember sizeMember
          (memory_related state) packed type
      have same := Option.some.inj (computed.symm.trans meaning)
      cases same
      have retained : ClosuresPreserved argumentStore finalStore := closures_preserved (memory_related state) frame
      exact ⟨target, finalStore, resultRelated, evaluated,
        state.cutoff_effect (frame_above frame)
          (resources_preserved state.external.1 state.external.2.2 memoryFinal frame),
        installed.preserved retained, retained⟩

/-- The actual initialized store supplies the resource boundary and unchanged
observations; no heap or frame invariant is requested of the source caller. -/
def initialLayout {memory size : Nat} {state : MemorySemantics.State} {store : Core.Store}
    (related : MemoryCorrespondence.StateRel memory size state store) : Layout :=
  ⟨store.length, memory, size, related.distinct,
    (List.getElem?_eq_some_iff.mp related.memory).1,
    (List.getElem?_eq_some_iff.mp related.size).1⟩

theorem initial_state {memory size : Nat} {state : MemorySemantics.State} {store : Core.Store}
    (related : MemoryCorrespondence.StateRel memory size state store) :
    StateRel (model (initialLayout related) (prefixRead store.length store)) [] ⟨[], state⟩ store := by
  apply StateRel.cutoff_initial
  exact ⟨by simpa only [initialLayout, prefixRead, (List.getElem?_eq_some_iff.mp related.memory).1, ↓reduceIte] using related.memory,
    by simpa only [initialLayout, prefixRead, (List.getElem?_eq_some_iff.mp related.size).1, ↓reduceIte] using related.size,
    fun _ _ _ => rfl⟩

/-- Memory calls in recursive Hull functions and loops reach actual assembly.
The external-call correctness obligation is discharged by concrete operations. -/
theorem assemble_program (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (sizeMember : ⟨"memorySize", .word, layout.size⟩ ∈ slots)
    {functions : List Function} {function : Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (eligible : ExecutableProgram supported functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State MemorySemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions MemorySemantics.effects function sources initial sourceResult final)
    {world : World} {runtimeValues caller : Core.Environment} {store : Core.Store}
    (runtimeLength : runtimeValues.length = runtime.length)
    (covered : ScopeCoverage [] runtime)
    (runtimeRelated : EffectEnvironmentRel slots runtime Core.Renaming.id
      (runtimeValues ++ bundleValues targets :: caller))
    (separated : EffectSlotsSeparate slots)
    (state : StateRel (model layout baseline) world initial store) :
    ∃ extension target finalStore,
      ResultRel own.result sourceResult target ∧
      Core.Evaluates (runtimeValues ++ bundleValues targets :: caller) store allocated target finalStore ∧
      StateRel (model layout baseline) (world ++ extension) final finalStore ∧
      ClosuresPreserved store finalStore :=
  assemble_recursive_program_effects accepted selected
    (external_preserves layout baseline slots memoryMember sizeMember) eligible values evaluated
    runtimeLength covered runtimeRelated separated state

end Solcore.Frontend.RustHull.MemoryEffectCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.MemoryFrameCorrespondence
/-! Independent memory-bearing Hull executions pass through the actual object
frame compiler, including its runtime-reference unpacking and final snapshot. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.MemoryFrameCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence MemoryEffectCorrespondence

def slotTypes (slots : List EffectSlot) : List (String × Core.Ty) :=
  slots.map fun slot => (slot.name, slot.type)

theorem frame_selected {program : Program} {code : CodeBlock} {slots : List (String × Core.Ty)}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code slots fuel = .ok compiled) :
    (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]).find?
      (·.name == AccountRuntime.frameEntry) = some (AccountRuntime.frameFunction code) := by
  unfold AccountRuntime.compileFrame at accepted
  split at accepted
  · simp [fail, Bind.bind, Except.bind] at accepted
  · rename_i notReserved
    have absent : (program.functions ++ code.functions).find? (·.name == AccountRuntime.frameEntry) = none := by
      apply List.find?_eq_none.mpr
      intro function member
      intro named
      exact notReserved (List.any_eq_true.mpr ⟨function, member, named⟩)
    simp only [List.find?_append, absent, Option.none_or, List.find?_cons,
      AccountRuntime.frameFunction, beq_self_eq_true]

theorem frame_signature {code : CodeBlock} {fuel : Nat} {own : Signature}
    (compiled : signature fuel (AccountRuntime.frameFunction code) = .ok own) :
    own.parameters = [] ∧ own.result = .unit := by
  obtain ⟨arity, result⟩ := StatementCorrespondence.signature_components compiled
  have parameters : own.parameters = [] := List.eq_nil_of_length_eq_zero arity.symm
  refine ⟨parameters, ?_⟩
  cases fuel with
  | zero => cases result
  | succ fuel => exact (Except.ok.inj result).symm

theorem frame_coverage (slots : List (String × Core.Ty)) :
    ScopeCoverage [] (AccountRuntime.frameScope slots) := by
  apply ScopeCoverage.of_reserved
  intro binding member name named
  obtain ⟨⟨slot, type⟩, _, rfl⟩ := List.mem_map.mp member
  cases Option.some.inj named
  exact slotName_reserved slot

/-- An unchanged runtime cell is observed at its real pre-body store location.
The initializer supplies these finite facts directly from allocation. -/
def PassiveCell (layout : Layout) (slots : List EffectSlot) (store : Core.Store)
    (name : String) (value : Core.Value) : Prop :=
  ∃ slot ∈ slots, slot.name = name ∧ slot.location ≠ layout.memory ∧
    slot.location ≠ layout.size ∧ slot.location < layout.boundary ∧
    store.read? slot.location = some value

theorem passive_observed {layout : Layout} {slots : List EffectSlot} {initial final : Core.Store}
    {world : World} {source : Semantics.State MemorySemantics.State}
    {cells : AccountRuntime.References} {environment : Core.Environment}
    (references : AccountRuntime.frameReferences (slotTypes slots) = .ok cells)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id environment)
    (related : StateRel (model layout (prefixRead layout.boundary initial)) world source final)
    {name : String} {value : Core.Value} (observed : PassiveCell layout slots initial name value) :
    FrameCellObserved cells environment final name value := by
  obtain ⟨slot, member, named, memory, size, below, stored⟩ := observed
  apply FrameCellObserved.of_compilation (type := slot.type) references
    (List.mem_map.mpr ⟨slot, member, by simp only [named]⟩)
  · intro binding index looked
    exact runtime slot member binding index (by simpa only [named] using looked)
  · have retained := related.external.2.2.2.2 slot.location memory size
    simpa only [prefixRead, below, ↓reduceIte, stored] using retained

theorem memory_observed {layout : Layout} {baseline : Nat → Option Core.Value}
    {slots : List EffectSlot} {store : Core.Store} {world : World}
    {source : Semantics.State MemorySemantics.State} {cells : AccountRuntime.References}
    {environment : Core.Environment}
    (references : AccountRuntime.frameReferences (slotTypes slots) = .ok cells)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id environment)
    (member : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (related : StateRel (model layout baseline) world source store) :
    FrameCellObserved cells environment store "memory" (Core.WordMapping.encode source.external.words) := by
  apply FrameCellObserved.of_compilation references
    (List.mem_map.mpr ⟨⟨"memory", Core.WordMapping.type, layout.memory⟩, member, rfl⟩)
  · exact runtime _ member
  · exact (memory_related related).memory

def snapshotValues (values : String → Core.Value) (memory : MemorySemantics.State) (name : String) : Core.Value :=
  if name = "memory" then Core.WordMapping.encode memory.words else values name

/-- Compilation, the independent source derivation and initialized cells are
sufficient for the complete emitted frame, including snapshot lookup faults. -/
theorem compileFrame_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {memoryLocation sizeLocation : Nat} {initialMemory : MemorySemantics.State}
    {initialStore store : Core.Store} {values environment : Core.Environment} {argument : Core.Expr}
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: environment))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, memoryLocation⟩ ∈ slots)
    (sizeMember : ⟨"memorySize", .word, sizeLocation⟩ ∈ slots)
    (memoryInitial : MemoryCorrespondence.StateRel memoryLocation sizeLocation initialMemory store)
    {final : Semantics.State MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) MemorySemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initialMemory⟩ result final)
    (accounts : StorageCorrespondence.Accounts) (address : Core.Word) (complete : Bool)
    (worldObserved : PassiveCell (initialLayout memoryInitial) slots store "world" (StorageCorrespondence.world accounts))
    (addressObserved : PassiveCell (initialLayout memoryInitial) slots store "address" (.word address))
    (completeObserved : PassiveCell (initialLayout memoryInitial) slots store "worldComplete" (.bool complete))
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ frameSnapshotNames, name ≠ "memory" →
      PassiveCell (initialLayout memoryInitial) slots store name (snapshot name)) :
    ∃ extension status finalStore,
      ResultRel .unit result status ∧
      Core.Evaluates environment initialStore (.apply compiled argument)
        (frameCompletionValue status (snapshotValues snapshot final.external)
          (StorageCorrespondence.get accounts address complete)) finalStore ∧
      StateRel (model (initialLayout memoryInitial) (prefixRead store.length store)) extension final finalStore := by
  obtain ⟨own, body, cells, assembled, references, rfl⟩ := compileFrame_components accepted
  have selected := frame_selected accepted
  obtain ⟨signatures, codes, selectedFunction, selectedCode, index, _, sourceSelected,
    signatureCompiled, _, _, _, _, _⟩ := assemble_selection assembled
  have sameFunction := Option.some.inj (sourceSelected.symm.trans selected)
  subst selectedFunction
  obtain ⟨parameters, resultType⟩ := frame_signature signatureCompiled
  have argumentValues : ValuesRel own.parameters [] [] := by rw [parameters]; exact .nil
  obtain ⟨extension, status, bodyStore, related, executed, state, _⟩ :=
    assemble_program (initialLayout memoryInitial) (prefixRead store.length store) slots
      memoryMember sizeMember assembled selected eligible argumentValues evaluated
      (runtimeValues := values.reverse) (caller := bundleValues values :: environment)
      (by simpa [AccountRuntime.frameScope, slotTypes] using length)
      (frame_coverage _) runtime separated (initial_state memoryInitial)
  have finalWorld := passive_observed references runtime state worldObserved
  have finalAddress := passive_observed references runtime state addressObserved
  have finalComplete := passive_observed references runtime state completeObserved
  have finalSnapshot : ∀ name ∈ frameSnapshotNames,
      FrameCellObserved cells (values.reverse ++ .unit :: bundleValues values :: environment)
        bodyStore name (snapshotValues snapshot final.external name) := by
    intro name member
    by_cases memory : name = "memory"
    · subst name
      exact memory_observed references runtime memoryMember state
    · simpa only [snapshotValues, memory, ↓reduceIte] using
        passive_observed references runtime state (snapshotObserved name member memory)
  have completed := frameCompletion_evaluates executed accounts address complete
    finalWorld finalAddress finalComplete finalSnapshot
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.getStore_extension accounts address complete
    (status :: (values.reverse ++ .unit :: bundleValues values :: environment)) bodyStore
  refine ⟨extension, status, _, by simpa only [resultType] using related,
    frameUnpack_evaluates (by simpa only [slotTypes, List.length_map] using length) supplied completed, ?_⟩
  rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
  simpa only [List.nil_append] using state.appendCore suffix

/-- The same source-driven frame theorem applies to the installed closure,
with its original capture environment and the actual later call expression. -/
theorem compileFrame_call_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {memoryLocation sizeLocation : Nat} {initialMemory : MemorySemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment} {function argument : Core.Expr}
    {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, memoryLocation⟩ ∈ slots)
    (sizeMember : ⟨"memorySize", .word, sizeLocation⟩ ∈ slots)
    (memoryInitial : MemoryCorrespondence.StateRel memoryLocation sizeLocation initialMemory store)
    {final : Semantics.State MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) MemorySemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initialMemory⟩ result final)
    (accounts : StorageCorrespondence.Accounts) (address : Core.Word) (complete : Bool)
    (worldObserved : PassiveCell (initialLayout memoryInitial) slots store "world" (StorageCorrespondence.world accounts))
    (addressObserved : PassiveCell (initialLayout memoryInitial) slots store "address" (.word address))
    (completeObserved : PassiveCell (initialLayout memoryInitial) slots store "worldComplete" (.bool complete))
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ frameSnapshotNames, name ≠ "memory" →
      PassiveCell (initialLayout memoryInitial) slots store name (snapshot name)) :
    ∃ extension status finalStore,
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues snapshot final.external)
          (StorageCorrespondence.get accounts address complete)) finalStore ∧
      StateRel (model (initialLayout memoryInitial) (prefixRead store.length store)) extension final finalStore := by
  obtain ⟨own, body, cells, assembled, references, rfl⟩ := compileFrame_components accepted
  have selected := frame_selected accepted
  obtain ⟨signatures, codes, selectedFunction, selectedCode, index, _, sourceSelected,
    signatureCompiled, _, _, _, _, _⟩ := assemble_selection assembled
  have sameFunction := Option.some.inj (sourceSelected.symm.trans selected)
  subst selectedFunction
  obtain ⟨parameters, resultType⟩ := frame_signature signatureCompiled
  have argumentValues : ValuesRel own.parameters [] [] := by rw [parameters]; exact .nil
  obtain ⟨extension, status, bodyStore, related, executed, state, _⟩ :=
    assemble_program (initialLayout memoryInitial) (prefixRead store.length store) slots
      memoryMember sizeMember assembled selected eligible argumentValues evaluated
      (runtimeValues := values.reverse) (caller := bundleValues values :: captured)
      (by simpa [AccountRuntime.frameScope, slotTypes] using length)
      (frame_coverage _) runtime separated (initial_state memoryInitial)
  have finalWorld := passive_observed references runtime state worldObserved
  have finalAddress := passive_observed references runtime state addressObserved
  have finalComplete := passive_observed references runtime state completeObserved
  have finalSnapshot : ∀ name ∈ frameSnapshotNames,
      FrameCellObserved cells (values.reverse ++ .unit :: bundleValues values :: captured)
        bodyStore name (snapshotValues snapshot final.external name) := by
    intro name member
    by_cases memory : name = "memory"
    · subst name
      exact memory_observed references runtime memoryMember state
    · simpa only [snapshotValues, memory, ↓reduceIte] using
        passive_observed references runtime state (snapshotObserved name member memory)
  have completed := frameCompletion_evaluates executed accounts address complete
    finalWorld finalAddress finalComplete finalSnapshot
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.getStore_extension accounts address complete
    (status :: (values.reverse ++ .unit :: bundleValues values :: captured)) bodyStore
  refine ⟨extension, status, _, by simpa only [resultType] using related,
    frameUnpack_call_evaluates (by simpa only [slotTypes, List.length_map] using length) closureRelated resolved supplied completed, ?_⟩
  rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
  simpa only [List.nil_append] using state.appendCore suffix

end Solcore.Frontend.RustHull.MemoryFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractMemoryCorrespondence
/-! Public contract execution of the memory fragment follows the independent
Hull derivation through allocation, frame execution and message finalization. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractMemoryCorrespondence
open Correspondence ScalarExecution CodeBuilder

def resultValue : Semantics.Result Semantics.Value → Core.Value
  | .fault (.language reason) => .inLeft .unit (.word reason)
  | _ => .inRight .word .unit

def snapshotValues (memory : MemorySemantics.State) (accounts : StorageCorrespondence.Accounts)
    (balances : StorageSemantics.Words) (name : String) : Core.Value :=
  if name = "memory" then Core.WordMapping.encode memory.words
  else if name = "world" then StorageCorrespondence.world accounts
  else if name = "balances" then Core.WordMapping.encode balances
  else if name = "logs" then Core.WordMapping.encode []
  else .word (Core.Word.ofNatModulo 0)

def messageValue (result : Semantics.Result Semantics.Value) (memory : MemorySemantics.State)
    (accounts : StorageCorrespondence.Accounts) (address : Core.Word) (complete : Bool)
    (balances : StorageSemantics.Words) : Core.Value :=
  let snapshot := snapshotValues memory accounts balances
  let framed := frameCompletionValue (resultValue result) snapshot (StorageCorrespondence.get accounts address complete)
  match StorageCorrespondence.get accounts address complete, result with
  | .ok _, .value _ =>
      match StorageCorrespondence.get (StorageCorrespondence.finalize accounts balances).1 address true with
      | .ok (account, _) => .pair (resultValue result)
          (finalizedSnapshotValue snapshot account (StorageCorrespondence.finalize accounts balances).1
            (StorageCorrespondence.finalize accounts balances).2)
      | .error _ => framed
  | _, _ => framed

theorem resultValue_eq {result : Semantics.Result Semantics.Value} {value : Core.Value}
    (related : ResultRel .unit result value) : value = resultValue result := by
  cases related with
  | value related => cases related; rfl
  | language reason => rfl

/-- Both completion branches are determined by the independent source result.
Successful messages execute concrete account finalization before exporting;
language failures retain the frame snapshot without changing shared state. -/
theorem message_evaluates {depth : Nat} {environment : Core.Environment}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {target deploying framed : Code}
    {worldLocation balancesLocation : Nat} {initial : Core.Store}
    (sourceResult : Semantics.Result Semantics.Value) (memory : MemorySemantics.State)
    (accounts : StorageCorrespondence.Accounts) (address : Core.Word) (complete : Bool) (balances : StorageSemantics.Words)
    {status : Core.Value} (statusRelated : ResultRel .unit sourceResult status)
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type worldLocation))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false))
    (framedValue : CodeValue depth environment framed
      (frameCompletionValue status (snapshotValues memory accounts balances)
        (StorageCorrespondence.get accounts address complete)))
    (worldFound : initial.read? worldLocation = some (StorageCorrespondence.world accounts))
    (balancesFound : initial.read? balancesLocation = some (Core.WordMapping.encode balances)) :
    ∃ final, Core.Evaluates environment initial
      (AccountRuntime.completeMessage shared images target deploying framed depth)
      (messageValue sourceResult memory accounts address complete balances) final := by
  have statusEqual := resultValue_eq statusRelated
  cases got : StorageCorrespondence.get accounts address complete with
  | error reason =>
      have framedRelated : CodeValue depth environment framed
          (.pair (.inLeft .unit (.word reason))
            (frameSnapshotValue (snapshotValues memory accounts balances) (Core.WordMapping.encode []))) := by
        simpa only [got, frameCompletionValue] using framedValue
      refine ⟨initial, ?_⟩
      have completed := completeMessage_failure (shared := shared) (images := images) (target := target)
        (deploying := deploying) framedRelated (MessageStatus.failure (.word reason))
        (by rfl : snapshotValues memory accounts balances "exit" = .word (Core.Word.ofNatModulo 0)) (by decide) initial
      simpa only [messageValue, got, frameCompletionValue] using completed
  | ok pair =>
      rcases pair with ⟨account, identity⟩
      have framedRelated : CodeValue depth environment framed
          (.pair status (frameSnapshotValue (snapshotValues memory accounts balances) (Core.WordMapping.encode account.storage))) := by
        simpa only [got, frameCompletionValue] using framedValue
      cases statusRelated with
      | value related =>
          cases related
          obtain ⟨finalAccount, finalIdentity, final, finalGot, completed, _, _, _⟩ :=
            completeMessage_success accounts balances worldReference balancesReference targetValue deployingValue
              framedRelated MessageStatus.success
              (by rfl : snapshotValues memory accounts balances "exit" = .word (Core.Word.ofNatModulo 0))
              (by decide) worldFound balancesFound
          exact ⟨final, by simpa only [messageValue, got, finalGot, resultValue] using completed⟩
      | language reason =>
          refine ⟨initial, ?_⟩
          have completed := completeMessage_failure (shared := shared) (images := images) (target := target)
            (deploying := deploying) framedRelated (MessageStatus.failure (.word reason))
            (by rfl : snapshotValues memory accounts balances "exit" = .word (Core.Word.ofNatModulo 0)) (by decide) initial
          simpa only [messageValue, got, frameCompletionValue, resultValue] using completed

theorem compileObject_selected {program : Program} {path : List String} {code : CodeBlock}
    {fuel : Nat} {codeBytes : Option (List UInt8)} {expression : Core.Expr}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : AccountRuntime.compileObject program path fuel codeBytes [] = .ok expression) :
    ∃ compiled,
      AccountRuntime.compileFrame program code
        (Effects.slots ++ (if codeBytes.isSome then Effects.codeSlots else [])) fuel = .ok compiled ∧
      expression = AccountRuntime.objectExpression
        (Effects.slots ++ (if codeBytes.isSome then Effects.codeSlots else []))
        compiled [] (codeBytes.toList.map (1, ·)) codeBytes [] := by
  unfold AccountRuntime.compileObject at accepted
  obtain ⟨selectedCode, selectedAgain, accepted⟩ := lower_bind_eq_ok.mp accepted
  have same := Except.ok.inj (selectedAgain.symm.trans selected)
  subst selectedCode
  obtain ⟨compiled, compiledOk, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨others, mapped, accepted⟩ := lower_bind_eq_ok.mp accepted
  have empty : others = [] := by simpa using (Except.ok.inj mapped).symm
  subst others
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨guard, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  cases guard
  cases accepted
  exact ⟨compiled, by simpa using compiledOk, by simp⟩

/-- A source-driven call of the installed frame continues into the actual
message completion code; its resulting value is determined solely by the
source result, final memory and supplied account data. -/
theorem frameCall_message_evaluates {program : Program} {code : CodeBlock}
    {slots : List EffectSlot} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (MemoryFrameCorrespondence.slotTypes slots) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram MemoryEffectCorrespondence.supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment captured : Core.Environment} {initial : Core.Store}
    {function argument target deploying : Code} {shared : AccountRuntime.References}
    {images : List (Nat × List UInt8)} {closure : Core.Value} {values : List Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment initial (function depth) closure initial)
    (supplied : Core.Evaluates environment initial (argument depth) (bundleValues values) initial)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots
      (AccountRuntime.frameScope (MemoryFrameCorrespondence.slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    {memoryLocation sizeLocation : Nat}
    (memoryMember : ⟨"memory", Core.WordMapping.type, memoryLocation⟩ ∈ slots)
    (sizeMember : ⟨"memorySize", .word, sizeLocation⟩ ∈ slots)
    (memoryInitial : MemoryCorrespondence.StateRel memoryLocation sizeLocation ⟨[], Core.Word.ofNatModulo 0⟩ initial)
    {finalSource : Semantics.State MemorySemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) MemorySemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], ⟨[], Core.Word.ofNatModulo 0⟩⟩ sourceResult finalSource)
    (accounts : StorageCorrespondence.Accounts) (address : Core.Word) (complete : Bool) (balances : StorageSemantics.Words)
    (worldObserved : MemoryFrameCorrespondence.PassiveCell (MemoryEffectCorrespondence.initialLayout memoryInitial)
      slots initial "world" (StorageCorrespondence.world accounts))
    (addressObserved : MemoryFrameCorrespondence.PassiveCell (MemoryEffectCorrespondence.initialLayout memoryInitial)
      slots initial "address" (.word address))
    (completeObserved : MemoryFrameCorrespondence.PassiveCell (MemoryEffectCorrespondence.initialLayout memoryInitial)
      slots initial "worldComplete" (.bool complete))
    (snapshotObserved : ∀ name ∈ frameSnapshotNames, name ≠ "memory" →
      MemoryFrameCorrespondence.PassiveCell (MemoryEffectCorrespondence.initialLayout memoryInitial) slots initial
        name (snapshotValues ⟨[], Core.Word.ofNatModulo 0⟩ accounts balances name))
    {worldLocation balancesLocation : Nat}
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type worldLocation))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false))
    (worldFound : initial.read? worldLocation = some (StorageCorrespondence.world accounts))
    (balancesFound : initial.read? balancesLocation = some (Core.WordMapping.encode balances))
    (worldMemory : worldLocation ≠ memoryLocation) (worldSize : worldLocation ≠ sizeLocation)
    (balancesMemory : balancesLocation ≠ memoryLocation) (balancesSize : balancesLocation ≠ sizeLocation) :
    ∃ final, Core.Evaluates environment initial
      (bind (apply function argument) (fun result => AccountRuntime.completeMessage shared images target deploying result) depth)
      (messageValue sourceResult finalSource.external accounts address complete balances) final := by
  obtain ⟨extension, status, bodyStore, statusRelated, executed, related⟩ :=
    MemoryFrameCorrespondence.compileFrame_call_preserves accepted eligible closureRelated resolved supplied length
      runtime separated memoryMember sizeMember memoryInitial evaluated accounts address complete worldObserved addressObserved
      completeObserved (snapshotValues ⟨[], Core.Word.ofNatModulo 0⟩ accounts balances) snapshotObserved
  have snapshots : MemoryFrameCorrespondence.snapshotValues
      (snapshotValues ⟨[], Core.Word.ofNatModulo 0⟩ accounts balances) finalSource.external =
      snapshotValues finalSource.external accounts balances := by
    funext name
    simp only [MemoryFrameCorrespondence.snapshotValues, snapshotValues]
    split <;> rfl
  rw [snapshots] at executed
  have worldBound := (List.getElem?_eq_some_iff.mp worldFound).1
  have balancesBound := (List.getElem?_eq_some_iff.mp balancesFound).1
  have worldFinal : bodyStore.read? worldLocation = some (StorageCorrespondence.world accounts) := by
    have retained := related.external.2.2.2.2 worldLocation worldMemory worldSize
    simpa only [prefixRead, MemoryEffectCorrespondence.initialLayout, worldBound, ↓reduceIte, worldFound] using retained
  have balancesFinal : bodyStore.read? balancesLocation = some (Core.WordMapping.encode balances) := by
    have retained := related.external.2.2.2.2 balancesLocation balancesMemory balancesSize
    simpa only [prefixRead, MemoryEffectCorrespondence.initialLayout, balancesBound, ↓reduceIte, balancesFound] using retained
  let frameResult := frameCompletionValue status (snapshotValues finalSource.external accounts balances)
    (StorageCorrespondence.get accounts address complete)
  obtain ⟨final, completed⟩ := message_evaluates sourceResult finalSource.external accounts address complete balances
    statusRelated (worldReference.prepend [frameResult]) (balancesReference.prepend [frameResult])
    (targetValue.prepend [frameResult]) (deployingValue.prepend [frameResult])
    (CodeValue.bound depth environment frameResult) worldFinal balancesFinal
  exact ⟨final, .letE executed completed⟩

end Solcore.Frontend.RustHull.ContractMemoryCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.MemorySnapshotCorrespondence
/-! Snapshot extraction retains every pre-existing store cell. Both the
aligned traversal and unaligned copying preserve their actual allocations. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.MemorySnapshotCorrespondence
open Core CodeBuilder Correspondence ScalarExecution

inductive ResultRel : Semantics.Result MemorySemantics.Entries → Value → Prop where
  | returned (entries : MemorySemantics.Entries) : ResultRel (.value entries) (.inRight .word (WordMapping.encode entries))
  | language (reason : Word) : ResultRel (.fault (.language reason)) (.inLeft WordMapping.type (.word reason))

def extractTail (args size : Code) : Code :=
  let source := part 0 3 args
  let offset := part 1 3 args
  let length := part 2 3 args
  choose (binary .wordEq length (number 0)) (success empty) <|
  choose (binary .wordEq (binary .wordMod offset (number 32)) (number 0))
    (fun depth => WordMapping.runHelper MemorySnapshot.parameter WordMapping.type MemorySnapshot.alignedBody
      (packet [source, binary .wordDiv offset (number 32),
        binary .wordDiv (binary .wordSub length (number 1)) (number 32),
        binary .wordMul (binary .wordMod
          (binary .wordSub (number 32) (binary .wordMod length (number 32))) (number 32))
          (number 8)] depth))
    (bind (allocate WordMapping.type empty) fun destination =>
      bindResult WordMapping.type (fun depth => Memory.copyPackedFrom
        (destination depth) (size depth) (number 0 depth) (source depth) (offset depth) (length depth)) fun _ =>
      success (load destination))

private theorem touch_idempotent {size offset length expanded : Word}
    (checked : MemorySemantics.touchSize? size offset length = some expanded) :
    MemorySemantics.touchSize? expanded offset length = some expanded := by
  unfold MemorySemantics.touchSize? at checked ⊢
  split at checked
  · cases checked
    simp_all
  · dsimp only at checked
    split at checked
    · cases checked
    · split at checked
      · cases checked
      · split at checked <;> cases checked <;> simp_all
        intro contrary
        exact False.elim ((Nat.not_lt_of_ge ‹MemorySemantics.rounded (offset.add length) ≤ size›) contrary)

private theorem touched_retains (store : Store) (length : Word) :
    StoreRetains store (MemoryCorrespondence.touchStore (store ++ [.word Word.zero]) store.length Word.zero Word.zero length) where
  length_le := by rw [MemoryCorrespondence.touchStore_length]; simp
  read := by
    intro location bounded
    rw [MemoryCorrespondence.touchStore_other _ (by omega)]
    simp only [Store.read?, List.getElem?_append_left bounded]

theorem extract_preserves {entries : MemorySemantics.Entries} {offset length : Word}
    {result : Semantics.Result MemorySemantics.Entries}
    (extracted : MemorySnapshotSemantics.Extract entries offset length result)
    {environment : Environment} {store : Store} {mapping offsetExpr lengthExpr : Core.Expr}
    (mappingEvaluated : Evaluates environment store mapping (WordMapping.encode entries) store)
    (offsetEvaluated : Evaluates environment store offsetExpr (.word offset) store)
    (lengthEvaluated : Evaluates environment store lengthExpr (.word length) store) :
    ∃ target final, ResultRel result target ∧
      Evaluates environment store (MemorySnapshot.extract mapping offsetExpr lengthExpr) target final ∧
      StoreRetains store final := by
  let input := bundleValues [WordMapping.encode entries, .word offset, .word length]
  let argsCode : Code := fun here => .var (here - 0 - 1)
  let sizeCode : Code := fun here => .var (here - 1 - 1)
  let sizeRef : Value := .cellRef .word store.length
  let allocated := store ++ [Value.word Word.zero]
  let touchedStore := MemoryCorrespondence.touchStore allocated store.length Word.zero Word.zero length
  let entered := [Value.unit, sizeRef, input] ++ environment
  have argsRelated : CodeValue 1 (input :: environment) argsCode (bundleValues [WordMapping.encode entries, .word offset, .word length]) :=
    CodeValue.bound 0 environment input
  have sourceRelated := argsRelated.part (index := 0) rfl
  have offsetRelated := argsRelated.part (index := 1) rfl
  have lengthRelated := argsRelated.part (index := 2) rfl
  have sizeRelated : CodeValue 2 (sizeRef :: input :: environment) sizeCode (.cellRef .word store.length) :=
    CodeValue.bound 1 (input :: environment) sizeRef
  have sizeRead : allocated.read? store.length = some (.word Word.zero) := by simp [allocated, Store.read?]
  have touched := MemoryCorrespondence.touch_evaluates (offset := Word.zero) (sizeRelated.evaluates allocated) .word
    ((lengthRelated.prepend [sizeRef]).evaluates allocated) sizeRead
  have enter {size : Word} (checked : MemorySemantics.touchSize? Word.zero Word.zero length = some size)
      {target : Value} {final : Store}
      (continued : Evaluates entered touchedStore (extractTail argsCode sizeCode 3) target final) :
      Evaluates environment store (MemorySnapshot.extract mapping offsetExpr lengthExpr) target final := by
    apply Evaluates.letE (.pair mappingEvaluated (.pair offsetEvaluated lengthEvaluated))
    apply Evaluates.letE (bodyStore := allocated) (.newCell .word)
    apply LanguageResult.bind_success WordMapping.type
    · have successful := touched
      simp only [MemoryCorrespondence.touchResult, checked] at successful
      exact successful
    · exact continued
  cases extracted with
  | overflow invalid =>
      simp only [MemoryCorrespondence.touchResult, invalid, MemoryCorrespondence.touchStore_failure invalid] at touched
      refine ⟨.inLeft WordMapping.type (.word (Word.ofNatModulo 6)), allocated, .language _, ?_, StoreRetains.append _ _⟩
      apply Evaluates.letE (.pair mappingEvaluated (.pair offsetEvaluated lengthEvaluated))
      apply Evaluates.letE (bodyStore := allocated) (.newCell .word)
      exact LanguageResult.bind_failure WordMapping.type touched
  | empty zero =>
      subst length
      refine ⟨.inRight .word (WordMapping.encode []), touchedStore, .returned _, enter rfl ?_, touched_retains store Word.zero⟩
      exact .ifTrue (.binary ((lengthRelated.prepend [.unit, sizeRef]).evaluates touchedStore) .word rfl) (.inRight (.construct .unit))
  | aligned checked nonempty alignedOffset =>
      have source' := sourceRelated.prepend [.unit, sizeRef]
      have offset' := offsetRelated.prepend [.unit, sizeRef]
      have length' := lengthRelated.prepend [.unit, sizeRef]
      have copied := aligned_evaluates (start := offset.udiv (Word.ofNatModulo 32))
        (last := MemorySnapshotSemantics.lastIndex length) (shift := MemorySnapshotSemantics.padding length)
        (.pair (source'.evaluates touchedStore) (.pair (.binary (op := .wordDiv) (offset'.evaluates touchedStore) .word rfl)
          (.pair (.binary (op := .wordDiv) (.binary (op := .wordSub) (length'.evaluates touchedStore) .word rfl) .word rfl)
            (.binary (op := .wordMul) (.binary (op := .wordMod) (.binary (op := .wordSub) .word
              (.binary (op := .wordMod) (length'.evaluates touchedStore) .word rfl) rfl) .word rfl) .word rfl))))
      let final := WordMapping.installedStore touchedStore MemorySnapshot.parameter WordMapping.type MemorySnapshot.alignedBody
        (alignedInput entries (offset.udiv (Word.ofNatModulo 32)) (MemorySnapshotSemantics.lastIndex length)
          (MemorySnapshotSemantics.padding length)) entered
      refine ⟨_, final, .returned _, enter checked ?_, (touched_retains store length).trans (StoreRetains.append _ _)⟩
      apply Evaluates.ifFalse (.binary (length'.evaluates touchedStore) .word (by simp [BinaryOp.apply, nonempty, show Word.ofNatModulo 0 = Word.zero from rfl]))
      apply Evaluates.ifTrue (.binary (.binary (offset'.evaluates touchedStore) .word rfl) .word (by simp [BinaryOp.apply, alignedOffset, show Word.ofNatModulo 0 = Word.zero from rfl]))
      exact copied
  | @copied size words checked nonempty unaligned copied =>
      let destination := touchedStore.length
      let destinationRef : Value := .cellRef WordMapping.type destination
      let copyStore := touchedStore ++ [WordMapping.encode []]
      have touchedSize := MemoryCorrespondence.touchStore_read sizeRead checked
      have touchedLength : touchedStore.length = store.length + 1 := by
        rw [MemoryCorrespondence.touchStore_length]
        simp [allocated]
      have destinationRelated := CodeValue.bound 3 entered destinationRef
      have source' := sourceRelated.prepend [destinationRef, .unit, sizeRef]
      have offset' := offsetRelated.prepend [destinationRef, .unit, sizeRef]
      have length' := lengthRelated.prepend [destinationRef, .unit, sizeRef]
      have size' := sizeRelated.prepend [destinationRef, .unit]
      have memoryRelated : MemoryCorrespondence.StateRel destination store.length ⟨[], size⟩ copyStore := by
        refine ⟨by dsimp [destination]; omega, ?_, ?_⟩
        · simp [copyStore, destination, Store.read?]
        · simpa only [copyStore, Store.read?, List.getElem?_append_left (by omega : store.length < touchedStore.length)] using touchedSize
      obtain ⟨target, final, related, evaluated, finalRelated, framed⟩ := MemoryCopyCorrespondence.copyPackedFrom_preserves
        (MemoryCopySemantics.From.done (touch_idempotent checked) copied) memoryRelated
        (destinationRelated.evaluates copyStore) (size'.evaluates copyStore) .word
        (source'.evaluates copyStore) (offset'.evaluates copyStore) (length'.evaluates copyStore)
      cases related with
      | value related =>
          cases related
          have retained : StoreRetains store final := by
            refine ⟨?_, ?_⟩
            · have bound := framed.length
              simp only [copyStore, List.length_append, List.length_cons, List.length_nil] at bound
              omega
            · intro location bounded
              have found : store.read? location = some store[location] := List.getElem?_eq_getElem bounded
              have same := framed.read location _ (by dsimp [destination]; omega) (by omega)
                (by simpa only [copyStore, Store.read?, List.getElem?_append_left (by omega : location < touchedStore.length)] using
                  ((touched_retains store length).read location bounded).trans found)
              exact same.trans found.symm
          refine ⟨.inRight .word (WordMapping.encode words), final, .returned _, enter checked ?_, retained⟩
          apply Evaluates.ifFalse (.binary ((lengthRelated.prepend [.unit, sizeRef]).evaluates touchedStore) .word (by simp [BinaryOp.apply, nonempty, show Word.ofNatModulo 0 = Word.zero from rfl]))
          apply Evaluates.ifFalse (.binary (.binary ((offsetRelated.prepend [.unit, sizeRef]).evaluates touchedStore) .word rfl) .word (by simp [BinaryOp.apply, unaligned, show Word.ofNatModulo 0 = Word.zero from rfl]))
          apply Evaluates.letE (bodyStore := copyStore) (.newCell (.construct .unit))
          apply LanguageResult.bind_success WordMapping.type evaluated
          exact .inRight (.loadCell ((destinationRelated.prepend [.unit]).evaluates final) finalRelated.memory)

end Solcore.Frontend.RustHull.MemorySnapshotCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeEnvironmentCorrespondence
/-! The runtime references supplied by actual allocation line up with the
compiler's reversed frame scope. Unique slot names determine each cell lookup. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence

def effectSlotBinding (slot : EffectSlot) : Binding :=
  ⟨some (Effects.slotName slot.name), slot.type, false⟩

def effectSlotReference (slot : EffectSlot) : Core.Value := .cellRef slot.type slot.location

theorem EffectEnvironmentRel.of_slots (slots : List EffectSlot)
    (unique : (slots.map EffectSlot.name).Nodup) (caller : Core.Environment) :
    EffectEnvironmentRel slots (slots.map effectSlotBinding) Core.Renaming.id
      (slots.map effectSlotReference ++ caller) := by
  induction slots with
  | nil => exact .empty _ _ _
  | cons head rest ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      intro slot member binding index looked
      rcases List.mem_cons.mp member with rfl | member
      · simp only [List.map_cons, scope_lookup_cons, effectSlotBinding,
          beq_self_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at looked
        obtain ⟨rfl, rfl⟩ := looked
        rfl
      · have different : head.name ≠ slot.name := by
          intro same
          exact absent (List.mem_map.mpr ⟨slot, member, same.symm⟩)
        have names : Effects.slotName head.name ≠ Effects.slotName slot.name := by
          intro same
          exact different (by simpa [Effects.slotName] using same)
        simp only [List.map_cons, scope_lookup_cons, effectSlotBinding,
          Option.some_beq_some, beq_eq_false_iff_ne.mpr names, Bool.false_eq_true, ↓reduceIte] at looked
        cases previous : Scope.lookup (rest.map effectSlotBinding) (Effects.slotName slot.name) with
        | error error => simp only [previous] at looked; contradiction
        | ok pair =>
            rcases pair with ⟨oldBinding, oldIndex⟩
            simp only [previous, Except.ok.injEq, Prod.mk.injEq] at looked
            obtain ⟨rfl, rfl⟩ := looked
            exact ih tailUnique slot member oldBinding oldIndex previous

/-- The exact value order unpacked by frameUnpack denotes every reserved slot.
Caller values may include the argument bundle and arbitrary captured closures. -/
theorem EffectEnvironmentRel.frame (slots : List EffectSlot)
    (unique : (slots.map EffectSlot.name).Nodup) (caller : Core.Environment) :
    EffectEnvironmentRel slots
      (AccountRuntime.frameScope (slots.map fun slot => (slot.name, slot.type))) Core.Renaming.id
      ((slots.map effectSlotReference).reverse ++ caller) := by
  have reversed := EffectEnvironmentRel.of_slots slots.reverse
    (by
      rw [List.map_reverse]
      exact List.pairwise_reverse.mpr (unique.imp (fun different => Ne.symm different))) caller
  intro slot member binding index looked
  have lookup : Scope.lookup (slots.reverse.map effectSlotBinding) (Effects.slotName slot.name) = .ok (binding, index) := by
    have same : AccountRuntime.frameScope (slots.map fun slot => (slot.name, slot.type)) = slots.reverse.map effectSlotBinding := by
      simp only [AccountRuntime.frameScope, List.map_reverse, List.map_map]
      rfl
    rw [← same]
    exact looked
  simpa only [List.map_reverse] using reversed slot (List.mem_reverse.mpr member) binding index lookup

def InitializedCell.effectSlot (cell : InitializedCell) : EffectSlot :=
  ⟨cell.name, cell.type, cell.location⟩

theorem initialized_environment (cells : List InitializedCell)
    (unique : (cells.map InitializedCell.name).Nodup) (caller : Core.Environment) :
    EffectEnvironmentRel (cells.map InitializedCell.effectSlot)
      (AccountRuntime.frameScope (cells.map fun cell => (cell.name, cell.type))) Core.Renaming.id
      ((cells.map InitializedCell.reference).reverse ++ caller) := by
  have related := EffectEnvironmentRel.frame (cells.map InitializedCell.effectSlot)
    (by simpa only [List.map_map, Function.comp_def, InitializedCell.effectSlot] using unique) caller
  simp only [List.map_map] at related
  exact related

theorem effects_slots_unique : (Effects.slots.map Prod.fst).Nodup := by decide

theorem effects_slots_separate : ∀ slot ∈ Effects.slots, slot.1.startsWith "function$" = false := by
  intro slot member
  apply String.startsWith_string_eq_false_iff.mpr
  have absent : ∀ slot ∈ Effects.slots, ¬ ("function$".toList <+: slot.1.toList) := by decide
  exact absent slot member

theorem initialized_effects_unique {cells : List InitializedCell}
    (names : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots) :
    (cells.map InitializedCell.name).Nodup := by
  have equality := congrArg (List.map Prod.fst) names
  simp only [List.map_map] at equality
  change cells.map InitializedCell.name = Effects.slots.map Prod.fst at equality
  rw [equality]
  exact effects_slots_unique

theorem initialized_effects_separate {cells : List InitializedCell}
    (names : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots) :
    EffectSlotsSeparate (cells.map InitializedCell.effectSlot) := by
  intro slot member
  obtain ⟨cell, cellMember, rfl⟩ := List.mem_map.mp member
  have inSlots : (cell.name, cell.type) ∈ Effects.slots := by
    rw [← names]
    exact List.mem_map.mpr ⟨cell, cellMember, rfl⟩
  exact effects_slots_separate _ inSlots

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeInstalledCallbacksCorrespondence
/-! Actual callback installation exposes both captured closures and exact cell
contents for later calls through the public object runtime. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open CodeBuilder ScalarExecution

theorem LambdaCode.captures {code : Code} (lambda : LambdaCode code)
    (depth : Nat) (environment : Core.Environment) :
    ∃ value, CapturedClosure (code depth) environment value := by
  obtain ⟨parameter, result, body, same⟩ := lambda depth
  exact ⟨.closure parameter result body environment, same ▸ CapturedClosure.lambda ..⟩

theorem allocateCallbacks_captures {depth : Nat} {environment : Core.Environment}
    {initial : Core.Store} {handlers : Code → Code → Code × Code}
    (closures : ∀ dispatcher creator, LambdaCode (handlers dispatcher creator).1 ∧ LambdaCode (handlers dispatcher creator).2) :
    ∃ dispatcher creator extra allocated,
      extra.length = 4 ∧ StoreRetains initial allocated ∧
      CodeValue (depth + extra.length) (extra ++ environment) dispatcher
        (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) initial.length) ∧
      CodeValue (depth + extra.length) (extra ++ environment) creator
        (.cellRef (Core.OptionalCell.cellType Creation.callbackType) (initial.length + 1)) ∧
      CodeValue (depth + 2)
        (.cellRef (Core.OptionalCell.cellType Creation.callbackType) (initial.length + 1) ::
          .cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) initial.length :: environment)
        dispatcher (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) initial.length) ∧
      CodeValue (depth + 2)
        (.cellRef (Core.OptionalCell.cellType Creation.callbackType) (initial.length + 1) ::
          .cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) initial.length :: environment)
        creator (.cellRef (Core.OptionalCell.cellType Creation.callbackType) (initial.length + 1)) ∧
      (∃ dispatchClosure createClosure,
        CapturedClosure ((handlers dispatcher creator).1 (depth + 2))
          (.cellRef (Core.OptionalCell.cellType Creation.callbackType) (initial.length + 1) ::
            .cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) initial.length :: environment) dispatchClosure ∧
        CapturedClosure ((handlers dispatcher creator).2 (depth + 3))
          (.unit :: .cellRef (Core.OptionalCell.cellType Creation.callbackType) (initial.length + 1) ::
            .cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) initial.length :: environment) createClosure ∧
        allocated.read? initial.length = some (.inRight .unit dispatchClosure) ∧
        allocated.read? (initial.length + 1) = some (.inRight .unit createClosure)) ∧
      ∀ continuation result final,
        Core.Evaluates (extra ++ environment) allocated
          (continuation dispatcher creator (depth + extra.length)) result final →
        Core.Evaluates environment initial (AccountRuntime.allocateCallbacks handlers continuation depth) result final := by
  let dispatcher : Code := fun here => .var (here - depth - 1)
  let creator : Code := fun here => .var (here - (depth + 1) - 1)
  let dispatcherValue := Core.Value.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) initial.length
  let creatorValue := Core.Value.cellRef (Core.OptionalCell.cellType Creation.callbackType) (initial.length + 1)
  let allocated := initial ++ [Core.Value.inLeft AccountRuntime.dispatchCallbackType .unit,
    Core.Value.inLeft Creation.callbackType .unit]
  have dispatcherRelated := CodeValue.bound depth environment dispatcherValue
  have creatorRelated := CodeValue.bound (depth + 1) (dispatcherValue :: environment) creatorValue
  obtain ⟨dispatchClosure, dispatchCaptured⟩ := ((closures dispatcher creator).1).captures
    (depth + 2) (creatorValue :: dispatcherValue :: environment)
  have dispatchEvaluated := dispatchCaptured.evaluates allocated
  let stored : Core.Store := allocated.set initial.length (.inRight .unit dispatchClosure)
  have dispatchFound : allocated.read? initial.length = some (.inLeft AccountRuntime.dispatchCallbackType .unit) := by
    simp [allocated, Core.Store.read?]
  have dispatchWritten : allocated.write? initial.length (.inRight .unit dispatchClosure) = some stored :=
    Core.Store.write?_eq_some_iff.mpr ⟨by simp [allocated], rfl⟩
  obtain ⟨createClosure, createCaptured⟩ := ((closures dispatcher creator).2).captures
    (depth + 3) (.unit :: creatorValue :: dispatcherValue :: environment)
  have createEvaluated := createCaptured.evaluates stored
  let initialized : Core.Store := stored.set (initial.length + 1) (.inRight .unit createClosure)
  have createFound : stored.read? (initial.length + 1) = some (.inLeft Creation.callbackType .unit) := by
    rw [Core.Store.write?_preserves_other (location := initial.length) (otherLocation := initial.length + 1) dispatchWritten (Nat.succ_ne_self _)]
    simp [allocated, Core.Store.read?]
  have createWritten : stored.write? (initial.length + 1) (.inRight .unit createClosure) = some initialized :=
    Core.Store.write?_eq_some_iff.mpr ⟨by simp [stored, allocated], rfl⟩
  have retained : StoreRetains initial initialized := by
    constructor
    · simp [initialized, stored, allocated]
    · intro location bounded
      rw [Core.Store.write?_preserves_other (location := initial.length + 1) (otherLocation := location) createWritten (Nat.ne_of_lt (Nat.lt_trans bounded (Nat.lt_succ_self _))),
        Core.Store.write?_preserves_other (location := initial.length) (otherLocation := location) dispatchWritten (Nat.ne_of_lt bounded)]
      exact List.getElem?_append_left bounded
  refine ⟨dispatcher, creator, [Core.Value.unit, .unit, creatorValue, dispatcherValue], initialized,
    rfl, retained, dispatcherRelated.prepend [Core.Value.unit, .unit, creatorValue],
    creatorRelated.prepend [Core.Value.unit, .unit], dispatcherRelated.prepend [creatorValue], creatorRelated,
    ⟨dispatchClosure, createClosure, dispatchCaptured, createCaptured, ?_, Core.Store.write?_reads_written createWritten⟩, ?_⟩
  · rw [Core.Store.write?_preserves_other createWritten (Nat.ne_of_lt (Nat.lt_succ_self _))]
    exact Core.Store.write?_reads_written dispatchWritten
  · intro continuation result final completed
    unfold AccountRuntime.allocateCallbacks CodeBuilder.bind
    apply Core.Evaluates.letE (Core.OptionalCell.allocate_evaluates ..)
    have second := Core.OptionalCell.allocate_evaluates Creation.callbackType
      (dispatcherValue :: environment) (initial ++ [.inLeft AccountRuntime.dispatchCallbackType .unit])
    simp only [List.length_append, List.length_cons, List.length_nil, List.append_assoc] at second
    apply Core.Evaluates.letE second
    apply Core.Evaluates.letE
      (Core.Evaluates.storeCell (dispatcherRelated [creatorValue] allocated) dispatchFound
        (.inRight dispatchEvaluated) dispatchWritten)
    apply Core.Evaluates.letE
      (Core.Evaluates.storeCell (creatorRelated [Core.Value.unit] stored) createFound
        (.inRight createEvaluated) createWritten)
    exact completed

theorem shared_description_names {context : Code} {cells : List InitializedCell} {values : List Core.Value}
    (description : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip values).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse)
    (length : (AccountRuntime.sharedInitializers context).length ≤ values.length) :
    cells.map InitializedCell.name = (sharedSlotTypes.map Prod.fst).reverse := by
  have names := congrArg (List.map Prod.fst) description
  simp only [List.map_reverse, List.map_map, Function.comp_def] at names
  rw [names]
  have firsts := List.map_fst_zip length
  have mapped := congrArg (List.map Prod.fst) firsts
  simp only [List.map_map, Function.comp_def, sharedInitializers_names] at mapped
  exact congrArg List.reverse mapped

/-- Concrete code references and the actual shared cells at callback capture. -/
structure ObjectCallbackCapture (slots : List (String × Core.Ty)) (count : Nat)
    (images : List (Nat × List UInt8)) (catalog : List AccountRuntime.CodeDefinition)
    (functionsValue : List Core.Value) (cells : List InitializedCell)
    (dispatcherLocation creatorLocation : Nat) (store : Core.Store) where
  depth : Nat
  environment : Core.Environment
  functions : Code
  shared : AccountRuntime.References
  dispatcher : Code
  creator : Code
  functionValues : CodeValue depth environment functions (bundleValues functionsValue)
  names : cells.map InitializedCell.name = (sharedSlotTypes.map Prod.fst).reverse
  references : RuntimeReferences depth environment shared cells
  dispatcherValue : CodeValue depth environment dispatcher
    (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation)
  creatorValue : CodeValue depth environment creator
    (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation)
  closure : Core.Value
  captured : CapturedClosure
    ((AccountRuntime.objectHandlers slots count images catalog functions shared dispatcher creator).1 depth)
    environment closure
  stored : store.read? dispatcherLocation = some (.inRight .unit closure)


/-- The installed callbacks, including the actual create-handler closure and
its cell. -/
theorem objectRuntime_evaluates_creator {depth : Nat} {environment : Core.Environment}
    {initial : Core.Store} (observes : Core.Value → Core.Store → Prop)
    {slots : List (String × Core.Ty)} {compiled : Core.Expr} {others : List Core.Expr}
    {images : List (Nat × List UInt8)} {codeBytes : Option (List UInt8)}
    {catalog : List AccountRuntime.CodeDefinition} {context : Code}
    {functionsValue initialValues : List Core.Value}
    (captured : CapturedClosures environment (compiled :: others) functionsValue)
    (inputs : CodeValues depth environment ((AccountRuntime.sharedInitializers context).map (·.2.2)) initialValues)
    (continued : ∀ functions shared dispatcher creator extra allocated cells dispatcherLocation creatorLocation,
      CodeValue (depth + extra.length) (extra ++ environment) functions (bundleValues functionsValue) →
      RuntimeReferences (depth + extra.length) (extra ++ environment) shared cells →
      InitializedCells cells allocated →
      CellLocations cells →
      cells.map (fun cell => (cell.name, cell.type, cell.value)) =
        (((AccountRuntime.sharedInitializers context).zip initialValues).map
          (fun (entry, value) => (entry.1, entry.2.1, value))).reverse →
      StoreRetains initial allocated →
      CodeValue (depth + extra.length) (extra ++ environment) dispatcher
        (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation) →
      CodeValue (depth + extra.length) (extra ++ environment) creator
        (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation) →
      (∃ value, allocated.read? creatorLocation = some value) →
      (∀ cell ∈ cells, cell.location < creatorLocation) →
      (∀ cell ∈ cells, cell.location < dispatcherLocation) →
      dispatcherLocation < creatorLocation →
      (capture : ObjectCallbackCapture slots (others.length + 1) images catalog functionsValue cells
        dispatcherLocation creatorLocation allocated) →
      ∀ createValue, allocated.read? creatorLocation = some (.inRight .unit createValue) →
        CapturedClosure ((AccountRuntime.objectHandlers slots (others.length + 1) images catalog capture.functions
          capture.shared capture.dispatcher capture.creator).2 (capture.depth + 1)) (.unit :: capture.environment) createValue →
      ∃ result final, Core.Evaluates (extra ++ environment) allocated
        (AccountRuntime.objectFrame slots (others.length + 1) images codeBytes context functions shared dispatcher creator
          (depth + extra.length)) result final ∧ observes result final) :
    ∃ result final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime slots compiled others images codeBytes catalog context depth) result final ∧ observes result final := by
  have packetEvaluated := captured.evaluates initial
  have bundleEvaluated : Core.Evaluates environment initial
      (packet ((compiled :: others).map constant) depth) (bundleValues functionsValue) initial := by
    simpa [packet, constant, Function.comp_def] using packetEvaluated
  let functions : Code := fun here => .var (here - depth - 1)
  have functionsRelated := CodeValue.bound depth environment (bundleValues functionsValue)
  have sharedInputs := inputs.prepend [bundleValues functionsValue]
  obtain ⟨sharedExtra, suffix, shared, cells, references, initialized, separate, description, sharedEvaluated⟩ :=
    allocateSharedSlots_separates sharedInputs
      (references := []) (cells := []) ⟨rfl, .nil⟩ (by intro cell member; cases member) CellLocations.nil
  obtain ⟨dispatcher, creator, callbackExtra, allocated, _, callbacksRetained, dispatcherRelated, creatorRelated, dispatcherCaptured, creatorCaptured, capturedCallbacks, callbacksEvaluated⟩ :=
    allocateCallbacks_captures (depth := depth + 1 + sharedExtra.length)
      (environment := sharedExtra ++ bundleValues functionsValue :: environment) (initial := initial ++ suffix)
      (fun dispatcher creator => objectHandlers_lambdas slots (others.length + 1) images catalog functions shared dispatcher creator)
  obtain ⟨dispatchClosure, createClosure, dispatchCapture, createCapture, dispatchRead, creatorRead⟩ := capturedCallbacks
  let callbackCapture : ObjectCallbackCapture slots (others.length + 1) images catalog functionsValue cells
      (initial ++ suffix).length ((initial ++ suffix).length + 1) allocated := {
    depth := depth + 1 + sharedExtra.length + 2
    environment := .cellRef (Core.OptionalCell.cellType Creation.callbackType) ((initial ++ suffix).length + 1) ::
      .cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) (initial ++ suffix).length ::
      sharedExtra ++ bundleValues functionsValue :: environment
    functions := functions
    shared := shared
    dispatcher := dispatcher
    creator := creator
    functionValues := (functionsRelated.prepend sharedExtra).prepend
      [.cellRef (Core.OptionalCell.cellType Creation.callbackType) ((initial ++ suffix).length + 1),
       .cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) (initial ++ suffix).length]
    names := shared_description_names
      (by simpa only [List.map_nil, List.append_nil] using description)
      (by simpa only [List.length_map] using Nat.le_of_eq inputs.length)
    references := references.prepend
      [.cellRef (Core.OptionalCell.cellType Creation.callbackType) ((initial ++ suffix).length + 1),
       .cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) (initial ++ suffix).length]
    dispatcherValue := dispatcherCaptured
    creatorValue := creatorCaptured
    closure := dispatchClosure
    captured := dispatchCapture
    stored := dispatchRead }
  have allRetained : StoreRetains initial allocated := (StoreRetains.append initial suffix).trans callbacksRetained
  have functionsFinal := (functionsRelated.prepend sharedExtra).prepend callbackExtra
  have referencesFinal := references.prepend callbackExtra
  have initializedFinal := initialized.retained callbacksRetained
  have descriptionFinal : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip initialValues).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := by
    simpa only [List.map_nil, List.append_nil] using description
  obtain ⟨result, final, completed, observed⟩ := continued functions shared dispatcher creator
    (callbackExtra ++ sharedExtra ++ [bundleValues functionsValue]) allocated cells
    (initial ++ suffix).length ((initial ++ suffix).length + 1)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using functionsFinal)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using referencesFinal)
    initializedFinal separate descriptionFinal allRetained
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using dispatcherRelated)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using creatorRelated) ⟨_, creatorRead⟩
    (fun cell member => Nat.lt_trans (initialized.location_bound member) (Nat.lt_succ_self _))
    (fun _ member => initialized.location_bound member) (Nat.lt_succ_self _) callbackCapture
    createClosure creatorRead createCapture
  refine ⟨result, final, Core.Evaluates.letE bundleEvaluated ?_, observed⟩
  apply sharedEvaluated
  apply callbacksEvaluated
  simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using completed

theorem objectRuntime_evaluates_callbacks {depth : Nat} {environment : Core.Environment}
    {initial : Core.Store} (observes : Core.Value → Core.Store → Prop)
    {slots : List (String × Core.Ty)} {compiled : Core.Expr} {others : List Core.Expr}
    {images : List (Nat × List UInt8)} {codeBytes : Option (List UInt8)}
    {catalog : List AccountRuntime.CodeDefinition} {context : Code}
    {functionsValue initialValues : List Core.Value}
    (captured : CapturedClosures environment (compiled :: others) functionsValue)
    (inputs : CodeValues depth environment ((AccountRuntime.sharedInitializers context).map (·.2.2)) initialValues)
    (continued : ∀ functions shared dispatcher creator extra allocated cells dispatcherLocation creatorLocation,
      CodeValue (depth + extra.length) (extra ++ environment) functions (bundleValues functionsValue) →
      RuntimeReferences (depth + extra.length) (extra ++ environment) shared cells →
      InitializedCells cells allocated →
      CellLocations cells →
      cells.map (fun cell => (cell.name, cell.type, cell.value)) =
        (((AccountRuntime.sharedInitializers context).zip initialValues).map
          (fun (entry, value) => (entry.1, entry.2.1, value))).reverse →
      StoreRetains initial allocated →
      CodeValue (depth + extra.length) (extra ++ environment) dispatcher
        (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation) →
      CodeValue (depth + extra.length) (extra ++ environment) creator
        (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation) →
      (∃ value, allocated.read? creatorLocation = some value) →
      (∀ cell ∈ cells, cell.location < creatorLocation) →
      (∀ cell ∈ cells, cell.location < dispatcherLocation) →
      dispatcherLocation < creatorLocation →
      ObjectCallbackCapture slots (others.length + 1) images catalog functionsValue cells
        dispatcherLocation creatorLocation allocated →
      ∃ result final, Core.Evaluates (extra ++ environment) allocated
        (AccountRuntime.objectFrame slots (others.length + 1) images codeBytes context functions shared dispatcher creator
          (depth + extra.length)) result final ∧ observes result final) :
    ∃ result final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime slots compiled others images codeBytes catalog context depth) result final ∧ observes result final := by
  apply objectRuntime_evaluates_creator observes captured inputs
  intro functions shared dispatcher creator extra allocated cells dispatcherLocation creatorLocation functionsRelated
    references initialized separate description retained dispatcherRelated creatorRelated creatorFound creatorAfter
    dispatcherAfter dispatcherBefore capture _ _ _
  exact continued functions shared dispatcher creator extra allocated cells dispatcherLocation creatorLocation
    functionsRelated references initialized separate description retained dispatcherRelated creatorRelated creatorFound
    creatorAfter dispatcherAfter dispatcherBefore capture

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.StorageEffectCorrespondence
/-! Account-storage effects discharge the external-call boundary of the Hull
simulation. Existing local cells and installed functions survive successful
writes, missing-account faults and static-write termination. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.StorageEffectCorrespondence
open Correspondence DerivationCorrespondence ScalarExecution

abbrev Locations := StorageBuiltinCorrespondence.Locations

def required (locations : Locations) : List Nat :=
  [locations.world, locations.address, locations.complete, locations.isStatic,
    locations.exit, locations.returnOffset, locations.returnSize]

structure Layout where
  boundary : Nat
  locations : Locations
  distinct : locations.all.Nodup
  below : ∀ location, location ∈ required locations → location < boundary

structure Resources (layout : Layout) (baseline : Nat → Option Core.Value)
    (state : StorageSemantics.State) (read : Nat → Option Core.Value) : Prop where
  world : ∃ accounts : StorageCorrespondence.Accounts,
    accounts.map Prod.fst = state.world ∧ read layout.locations.world = some (StorageCorrespondence.world accounts)
  address : read layout.locations.address = some (.word state.address)
  complete : read layout.locations.complete = some (.bool state.complete)
  isStatic : read layout.locations.isStatic = some (.bool state.isStatic)
  exit : read layout.locations.exit = some (.word state.exit)
  returnOffset : read layout.locations.returnOffset = some (.word state.returnOffset)
  returnSize : read layout.locations.returnSize = some (.word state.returnSize)
  other : ∀ location, location ∉ layout.locations.mutable → read location = baseline location

def model (layout : Layout) (baseline : Nat → Option Core.Value) : StateModel StorageSemantics.State :=
  StateModel.cutoff layout.boundary (Resources layout baseline)

private theorem read_below {layout : Layout} (location : Nat)
    (member : location ∈ required layout.locations) (store : Core.Store) :
    prefixRead layout.boundary store location = store.read? location := by
  simp only [prefixRead, layout.below location member, ↓reduceIte]

theorem storage_related {layout : Layout} {baseline : Nat → Option Core.Value}
    {world : World} {state : Semantics.State StorageSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline) world state store) :
    StorageBuiltinCorrespondence.StateRel layout.locations state.external store := by
  have resources := related.external.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, layout.distinct⟩
  · obtain ⟨accounts, same, found⟩ := resources.world
    exact ⟨accounts, same, (read_below (layout := layout) layout.locations.world (by simp [required]) store).symm.trans found⟩
  all_goals first
    | exact (read_below _ (by simp [required]) store).symm.trans resources.address
    | exact (read_below _ (by simp [required]) store).symm.trans resources.complete
    | exact (read_below _ (by simp [required]) store).symm.trans resources.isStatic
    | exact (read_below _ (by simp [required]) store).symm.trans resources.exit
    | exact (read_below _ (by simp [required]) store).symm.trans resources.returnOffset
    | exact (read_below _ (by simp [required]) store).symm.trans resources.returnSize

theorem frame_above {layout : Layout} {initial final : Core.Store}
    (frame : StorageBuiltinCorrespondence.Frame layout.locations initial final) :
    StoreRetainsFrom layout.boundary initial final := by
  refine ⟨frame.length_le, ?_⟩
  intro location separated bounded
  have found : initial.read? location = some initial[location] := List.getElem?_eq_getElem bounded
  rw [found]
  apply frame.preserved location _ _ found
  intro member
  have below := layout.below location (by
    simp [StorageBuiltinCorrespondence.Locations.mutable] at member
    simp [required]
    rcases member with same | same | same | same <;> simp [same])
  omega

theorem resources_preserved {layout : Layout} {baseline : Nat → Option Core.Value}
    {initial final : Core.Store} {before after : StorageSemantics.State}
    (bounded : layout.boundary ≤ initial.length)
    (beforeResources : Resources layout baseline before (prefixRead layout.boundary initial))
    (afterStorage : StorageBuiltinCorrespondence.StateRel layout.locations after final)
    (frame : StorageBuiltinCorrespondence.Frame layout.locations initial final) :
    Resources layout baseline after (prefixRead layout.boundary final) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨accounts, same, found⟩ := afterStorage.world
    exact ⟨accounts, same, (read_below (layout := layout) layout.locations.world (by simp [required]) final).trans found⟩
  · exact (read_below _ (by simp [required]) final).trans afterStorage.address
  · exact (read_below _ (by simp [required]) final).trans afterStorage.complete
  · exact (read_below _ (by simp [required]) final).trans afterStorage.isStatic
  · exact (read_below _ (by simp [required]) final).trans afterStorage.exit
  · exact (read_below _ (by simp [required]) final).trans afterStorage.returnOffset
  · exact (read_below _ (by simp [required]) final).trans afterStorage.returnSize
  · intro location outside
    rw [← beforeResources.other location outside]
    by_cases below : location < layout.boundary
    · simp only [prefixRead, below, ↓reduceIte]
      have bound : location < initial.length := Nat.lt_of_lt_of_le below bounded
      have found : initial.read? location = some initial[location] := List.getElem?_eq_getElem bound
      rw [found]
      exact frame.preserved location _ outside found
    · simp only [prefixRead, below, ↓reduceIte]

theorem closures_preserved {locations : Locations} {before : StorageSemantics.State}
    {initial final : Core.Store}
    (related : StorageBuiltinCorrespondence.StateRel locations before initial)
    (frame : StorageBuiltinCorrespondence.Frame locations initial final) :
    ClosuresPreserved initial final := by
  intro location parameter result body environment found
  apply frame.preserved location _ _ found
  intro member
  simp [StorageBuiltinCorrespondence.Locations.mutable] at member
  rcases member with same | same | same | same
  · subst location
    obtain ⟨accounts, _, read⟩ := related.world
    have equal := Option.some.inj (read.symm.trans found)
    cases accounts <;> simp [StorageCorrespondence.world, StorageCorrespondence.entries,
      Core.OrderedMapping.encode] at equal
  · subst location
    cases Option.some.inj (related.exit.symm.trans found)
  · subst location
    cases Option.some.inj (related.returnOffset.symm.trans found)
  · subst location
    cases Option.some.inj (related.returnSize.symm.trans found)

def supported (name : String) : Prop :=
  ∃ operation : StorageBuiltinCorrespondence.Operation, operation.name = name

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot)
    (worldMember : ⟨"world", AccountState.type, layout.locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.locations.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.locations.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.locations.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.locations.returnSize⟩ ∈ slots) :
    ExternalCallPreservation supported (model layout baseline) slots StorageSemantics.effects := by
  intro functions name type sources initial final result available notFunction called
  obtain ⟨operation, rfl⟩ := available
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed =>
      cases operation with | load transient | store transient =>
        cases transient <;> simp [StorageBuiltinCorrespondence.Operation.name, Semantics.primitive?] at computed
  | external absent notPrimitive computed =>
      intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
      obtain ⟨computedResult, computedState, target, finalStore, meaning, resultRelated, evaluated, storageFinal, frame⟩ :=
        StorageBuiltinCorrespondence.preserves operation compiled related runtime worldMember addressMember
          completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
          (storage_related state) packed type
      have same := Option.some.inj (computed.symm.trans meaning)
      cases same
      have retained : ClosuresPreserved argumentStore finalStore := closures_preserved (storage_related state) frame
      exact ⟨target, finalStore, resultRelated, evaluated,
        state.cutoff_effect (frame_above frame)
          (resources_preserved state.external.1 state.external.2.2 storageFinal frame),
        installed.preserved retained, retained⟩

/-- The initialized cells establish all boundary assumptions. -/
def initialLayout {locations : Locations} {state : StorageSemantics.State} {store : Core.Store}
    (related : StorageBuiltinCorrespondence.StateRel locations state store) : Layout where
  boundary := store.length
  locations := locations
  distinct := related.distinct
  below := by
    intro location member
    simp [required] at member
    rcases member with same | same | same | same | same | same | same
    · subst location
      obtain ⟨_, _, read⟩ := related.world
      exact (List.getElem?_eq_some_iff.mp read).1
    all_goals subst location
    all_goals first
      | exact (List.getElem?_eq_some_iff.mp related.address).1
      | exact (List.getElem?_eq_some_iff.mp related.complete).1
      | exact (List.getElem?_eq_some_iff.mp related.isStatic).1
      | exact (List.getElem?_eq_some_iff.mp related.exit).1
      | exact (List.getElem?_eq_some_iff.mp related.returnOffset).1
      | exact (List.getElem?_eq_some_iff.mp related.returnSize).1

theorem initial_state {locations : Locations} {state : StorageSemantics.State} {store : Core.Store}
    (related : StorageBuiltinCorrespondence.StateRel locations state store) :
    StateRel (model (initialLayout related) (prefixRead store.length store)) [] ⟨[], state⟩ store := by
  apply StateRel.cutoff_initial
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ => rfl⟩
  · obtain ⟨accounts, same, read⟩ := related.world
    exact ⟨accounts, same, (read_below (layout := initialLayout related) _ (by simp [required, initialLayout]) store).trans read⟩
  all_goals first
    | exact (read_below (layout := initialLayout related) _ (by simp [required, initialLayout]) store).trans related.address
    | exact (read_below (layout := initialLayout related) _ (by simp [required, initialLayout]) store).trans related.complete
    | exact (read_below (layout := initialLayout related) _ (by simp [required, initialLayout]) store).trans related.isStatic
    | exact (read_below (layout := initialLayout related) _ (by simp [required, initialLayout]) store).trans related.exit
    | exact (read_below (layout := initialLayout related) _ (by simp [required, initialLayout]) store).trans related.returnOffset
    | exact (read_below (layout := initialLayout related) _ (by simp [required, initialLayout]) store).trans related.returnSize

/-- Storage calls inside recursive functions and loops reach actual assembly,
with the external-call premise discharged by the concrete storage code. -/
theorem assemble_program (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot)
    (worldMember : ⟨"world", AccountState.type, layout.locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.locations.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.locations.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.locations.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.locations.returnSize⟩ ∈ slots)
    {functions : List Function} {function : Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (eligible : ExecutableProgram supported functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State StorageSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions StorageSemantics.effects function sources initial sourceResult final)
    {world : World} {runtimeValues caller : Core.Environment} {store : Core.Store}
    (runtimeLength : runtimeValues.length = runtime.length)
    (covered : ScopeCoverage [] runtime)
    (runtimeRelated : EffectEnvironmentRel slots runtime Core.Renaming.id
      (runtimeValues ++ bundleValues targets :: caller))
    (separated : EffectSlotsSeparate slots)
    (state : StateRel (model layout baseline) world initial store) :
    ∃ extension target finalStore,
      ResultRel own.result sourceResult target ∧
      Core.Evaluates (runtimeValues ++ bundleValues targets :: caller) store allocated target finalStore ∧
      StateRel (model layout baseline) (world ++ extension) final finalStore ∧
      ClosuresPreserved store finalStore :=
  assemble_recursive_program_effects accepted selected
    (external_preserves layout baseline slots worldMember addressMember completeMember staticMember
      memorySizeMember exitMember offsetMember sizeMember) eligible values evaluated
    runtimeLength covered runtimeRelated separated state

end Solcore.Frontend.RustHull.StorageEffectCorrespondence
end
