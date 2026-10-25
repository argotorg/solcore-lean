import Solcore.Frontend.RustHull.ChildFrameSharedResources
import Solcore.Frontend.RustHull.RuntimeChildCallStateCorrespondence

/-! Captured ambient and creator cells remain available to child allocation.
Mutable shared values are read afresh from the current transport resources. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildCallbackContextCorrespondence
open Core Correspondence ScalarExecution ContractCallCorrespondence
open RuntimeCallEffectsCorrespondence (Layout sharedLocations)

structure Inventory (layout : Layout) (cells : List InitializedCell) (creator : Nat) : Prop where
  signature : cells.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse
  shared : SharedCells cells (sharedLocations layout)
  separate : CellLocations cells
  below : ∀ cell ∈ cells, cell.location < layout.boundary
  creatorBelow : creator < layout.boundary
  creatorSeparate : ∀ cell ∈ cells, cell.location ≠ creator
  ambientOutside : ∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
    cell.location ∉ RuntimeCallEffectsCorrespondence.mutable layout
  creatorOutside : creator ∉ RuntimeCallEffectsCorrespondence.mutable layout

def context {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator) : RuntimeChildCallEffectsCorrespondence.Context layout where
  valid read := (∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
    read cell.location = some cell.value) ∧ ∃ value, read creator = some value
  frame := by
    intro before after retained valid
    refine ⟨fun cell member ambient => ?_, ?_⟩
    · rw [retained _ (inventory.ambientOutside cell member ambient)]
      exact valid.1 cell member ambient
    · obtain ⟨value, found⟩ := valid.2
      exact ⟨value, (retained _ inventory.creatorOutside).trans found⟩

theorem initial {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator) {store : Store}
    (stored : InitializedCells cells store) (present : ∃ value, store.read? creator = some value) :
    (context inventory).valid (prefixRead layout.boundary store) := by
  refine ⟨fun cell member _ => ?_, ?_⟩
  · simpa only [prefixRead, inventory.below cell member, ↓reduceIte] using stored cell member
  · simpa only [prefixRead, inventory.creatorBelow, ↓reduceIte] using present

theorem reads {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator) {store : Store}
    (valid : (context inventory).valid (prefixRead layout.boundary store)) :
    (∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst → store.read? cell.location = some cell.value) ∧
      ∃ value, store.read? creator = some value := by
  refine ⟨fun cell member ambient => ?_, ?_⟩
  · simpa only [prefixRead, inventory.below cell member, ↓reduceIte] using valid.1 cell member ambient
  · simpa only [prefixRead, inventory.creatorBelow, ↓reduceIte] using valid.2

theorem Inventory.unique {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator) : (cells.map InitializedCell.name).Nodup := by
  have names := congrArg (List.map Prod.fst) inventory.signature
  simp only [List.map_reverse, List.map_map, Function.comp_def] at names
  rw [names]
  decide

private theorem same_named {cells : List InitializedCell} (unique : (cells.map InitializedCell.name).Nodup)
    {left right : InitializedCell} (leftMember : left ∈ cells) (rightMember : right ∈ cells)
    (named : left.name = right.name) : left = right := by
  obtain ⟨leftIndex, leftFound⟩ := List.mem_iff_getElem?.mp leftMember
  obtain ⟨rightIndex, rightFound⟩ := List.mem_iff_getElem?.mp rightMember
  have leftName : (cells.map InitializedCell.name)[leftIndex]? = some left.name := by
    simp only [List.getElem?_map, leftFound, Option.map_some]
  have rightName : (cells.map InitializedCell.name)[rightIndex]? = some left.name := by
    simp only [List.getElem?_map, rightFound, Option.map_some, named]
  have same := (List.getElem?_inj (List.getElem?_eq_some_iff.mp leftName).1 unique).mp (leftName.trans rightName.symm)
  subst rightIndex
  exact Option.some.inj (leftFound.symm.trans rightFound)

private theorem named_location {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator) {cell : InitializedCell} (member : cell ∈ cells)
    {name : String} {type : Core.Ty} {location : Nat} (named : cell.name = name)
    (selected : ∃ other ∈ cells, other.name = name ∧ other.reference = .cellRef type location) :
    cell.location = location := by
  obtain ⟨other, otherMember, otherName, reference⟩ := selected
  have same := same_named inventory.unique member otherMember (named.trans otherName.symm)
  subst other
  exact (Core.Value.cellRef.inj reference).2

/-- Every shared name is reused, and an older local reference is either a
shared reference or the explicitly installed creator reference. -/
def Origin (shared : List InitializedCell) (boundary : Nat) (cell : InitializedCell) : Prop :=
  (cell.name ∈ sharedSlotTypes.map Prod.fst → cell ∈ shared) ∧
  (cell.location < boundary → cell ∈ shared ∨ cell.name = "createHandler")

theorem fresh_origin {depth : Nat} {environment : Environment} {store : Store}
    {frame dispatcher gas code size known : CodeBuilder.Code} {shared : AccountRuntime.References}
    {cells : List InitializedCell} (references : RuntimeReferences depth environment shared cells)
    (signature : cells.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse)
    {values : List Value} {gasValue codeValue sizeValue knownValue : Value}
    (frameRelated : CodeValue depth environment frame (bundleValues values)) (length : values.length = 8)
    (gasRelated : CodeValue depth environment gas gasValue)
    (codeRelated : CodeValue depth environment code codeValue)
    (sizeRelated : CodeValue depth environment size sizeValue)
    (knownRelated : CodeValue depth environment known knownValue) :
    FrameInitializersValid depth environment store frame dispatcher gas code size known shared (Origin cells store.length) := by
  have names : shared.map Prod.fst = (sharedSlotTypes.map Prod.fst).reverse := by
    rw [references.names]
    have names := congrArg (List.map Prod.fst) signature
    simpa only [List.map_map, List.map_reverse, Function.comp_def] using names
  apply frameInitializers_valid frameRelated length gasRelated codeRelated sizeRelated knownRelated
  intro name type location value absent bounded _
  exact ⟨fun member => False.elim (ChildFrameCorrespondence.absent_shared_name names absent member),
    fun before => False.elim (Nat.not_lt_of_ge bounded before)⟩

theorem creator_origin (cells : List InitializedCell) (boundary location : Nat) (value : Value) :
    Origin cells boundary (ContractRuntimeEffectsCorrespondence.creatorCell location value) := by
  refine ⟨?_, fun _ => Or.inr rfl⟩
  intro impossible
  simp [ContractRuntimeEffectsCorrespondence.creatorCell, sharedSlotTypes, Ambient.slots] at impossible

theorem shared_included {shared cells : List InitializedCell} {withCode : Bool} {boundary : Nat}
    (sharedSignature : shared.map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse)
    (signature : cells.map (fun cell => (cell.name, cell.type)) = RuntimeExtendedInitializedEffects.slots withCode)
    (origin : ∀ cell ∈ cells, Origin shared boundary cell) : ∀ cell ∈ shared, cell ∈ cells := by
  have unique : (shared.map InitializedCell.name).Nodup := by
    have names := congrArg (List.map Prod.fst) sharedSignature
    simp only [List.map_map, List.map_reverse, Function.comp_def] at names
    rw [names]
    decide
  intro cell member
  have typed : (cell.name, cell.type) ∈ sharedSlotTypes := by
    have listed := List.mem_map_of_mem (f := fun cell : InitializedCell => (cell.name, cell.type)) member
    rw [sharedSignature] at listed
    exact List.mem_reverse.mp listed
  have included : (cell.name, cell.type) ∈ RuntimeExtendedInitializedEffects.slots withCode := by
    have all : ∀ entry ∈ sharedSlotTypes, entry ∈ RuntimeExtendedInitializedEffects.slots withCode := by
      intro entry member
      simp only [sharedSlotTypes, Ambient.slots, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with (rfl | rfl | rfl | rfl | rfl) |
        (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals cases withCode <;> simp [RuntimeExtendedInitializedEffects.slots, Effects.slots, Ambient.slots]
    exact all _ typed
  rw [← signature] at included
  obtain ⟨other, otherMember, equal⟩ := List.mem_map.mp included
  have sameName := (Prod.mk.inj equal).1
  have otherShared := (origin other otherMember).1 (sameName ▸ List.mem_map_of_mem (f := Prod.fst) typed)
  exact (same_named unique otherShared member sameName) ▸ otherMember

private def mutableSlots (layout : Layout) : List EffectSlot :=
  [⟨"balances", WordMapping.type, layout.balances⟩,
   ⟨"returnData", WordMapping.type, layout.returnData⟩,
   ⟨"returnDataSize", .word, layout.returnDataSize⟩,
   ⟨"logs", WordMapping.type, layout.logs⟩,
   ⟨"logSize", .word, layout.logSize⟩,
   ⟨"memory", WordMapping.type, layout.memory⟩,
   ⟨"memorySize", .word, layout.storage.memorySize⟩,
   ⟨"world", AccountState.type, layout.storage.world⟩,
   ⟨"exit", .word, layout.storage.exit⟩,
   ⟨"returnOffset", .word, layout.storage.returnOffset⟩,
   ⟨"returnSize", .word, layout.storage.returnSize⟩]

private theorem mutable_members {layout : Layout} {cells : List InitializedCell}
    (members : ∀ slot ∈ RuntimeCallInitializedEffects.baseSlots layout.toReturnDataLayout,
      slot ∈ cells.map InitializedCell.effectSlot) :
    ∀ slot ∈ mutableSlots layout, slot ∈ cells.map InitializedCell.effectSlot := by
  intro slot member
  apply members slot
  simp only [mutableSlots, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [RuntimeCallInitializedEffects.baseSlots]

theorem ambient_outside {layout : Layout} {shared cells : List InitializedCell}
    (included : ∀ cell ∈ shared, cell ∈ cells) (separate : CellLocations cells)
    (members : ∀ slot ∈ RuntimeCallInitializedEffects.baseSlots layout.toReturnDataLayout,
      slot ∈ cells.map InitializedCell.effectSlot) :
    ∀ cell ∈ shared, cell.name ∈ Ambient.slots.map Prod.fst →
      cell.location ∉ RuntimeCallEffectsCorrespondence.mutable layout := by
  intro cell member ambient inside
  change cell.location ∈ (mutableSlots layout).map EffectSlot.location at inside
  obtain ⟨slot, slotMember, same⟩ := List.mem_map.mp inside
  obtain ⟨other, otherMember, equal⟩ := List.mem_map.mp (mutable_members members slot slotMember)
  have named : cell.name = slot.name := by
    rw [← equal]
    exact separate cell (included cell member) other otherMember (same ▸ congrArg EffectSlot.location equal).symm
  have names := List.mem_map_of_mem (f := EffectSlot.name) slotMember
  rw [← named] at names
  simp only [mutableSlots, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at names
  rcases names with named | named | named | named | named | named | named | named | named | named | named
  all_goals simp [named, Ambient.slots] at ambient

theorem creator_outside {layout : Layout} {shared cells : List InitializedCell} {creator boundary : Nat}
    (before : creator < boundary) (afterShared : ∀ cell ∈ shared, cell.location < creator)
    (origin : ∀ cell ∈ cells, Origin shared boundary cell)
    (members : ∀ slot ∈ RuntimeCallInitializedEffects.baseSlots layout.toReturnDataLayout,
      slot ∈ cells.map InitializedCell.effectSlot) : creator ∉ RuntimeCallEffectsCorrespondence.mutable layout := by
  intro inside
  change creator ∈ (mutableSlots layout).map EffectSlot.location at inside
  obtain ⟨slot, slotMember, same⟩ := List.mem_map.mp inside
  obtain ⟨cell, cellMember, equal⟩ := List.mem_map.mp (mutable_members members slot slotMember)
  have location : cell.location = creator := (congrArg EffectSlot.location equal).trans same
  rcases (origin cell cellMember).2 (location ▸ before) with sharedMember | named
  · have impossible := afterShared cell sharedMember
    rw [location] at impossible
    exact Nat.lt_irrefl _ impossible
  · have names := List.mem_map_of_mem (f := EffectSlot.name) slotMember
    have slotName : slot.name = "createHandler" := (congrArg EffectSlot.name equal).symm.trans named
    simp [mutableSlots, slotName] at names


/-- The current parent observations follow from its ordinary runtime relation
and the same concrete ambient reads retained by the callback context. -/
theorem parent_observed {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator) {slots : List EffectSlot}
    (members : ∀ cell ∈ cells, cell.effectSlot ∈ slots)
    {baseline : Nat → Option Value} {image : Option (List UInt8)}
    {handlers : RuntimeCallEffectsCorrespondence.Handlers layout} {world : World}
    {state : Semantics.State RuntimeCallEffectsSemantics.State} {store : Store}
    (related : StateRel (RuntimeCallEffectsCorrespondence.model layout baseline slots image handlers) world state store)
    (valid : (context inventory).valid (prefixRead layout.boundary store)) :
    ∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
      ContractEnvironmentCorrespondence.initializedValue state.external.runtime.runtime.runtime.runtime.environment cell := by
  have environment := RuntimeEnvironmentEffectsCorrespondence.observations_related
    (RuntimeLogEffectsCorrespondence.runtime_related
    (RuntimeAccountEffectsCorrespondence.runtime_related (RuntimeCallEffectsCorrespondence.account_related related)))
  intro cell member ambient value specified
  have actual := environment _ (members cell member) value specified
  exact Option.some.inj (((reads inventory valid).1 cell member ambient).symm.trans actual)

/-- All reused cells are justified by their current reads; catalog links choose
one exact encoded world witness for both storage and child initialization. -/
theorem current_observed {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator) {store : Store}
    (valid : (context inventory).valid (prefixRead layout.boundary store))
    (parent : RuntimeCallEffectsSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8)
    (ambient : ∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
      ContractEnvironmentCorrespondence.initializedValue parent.runtime.runtime.runtime.runtime.environment cell)
    {anchors : List CatalogWorldCorrespondence.Anchor}
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors shared.world layout.storage.world store)
    (resources : AccountCallCorrespondence.SharedStateRel (sharedLocations layout) shared store) :
    ∃ accounts, accounts.map Prod.fst = shared.world ∧ CatalogWorldCorrespondence.Links anchors accounts ∧
      ∀ cell ∈ cells, ∀ value, store.read? cell.location = some value →
        ChildFrameCorrespondence.Observed accounts (ChildFrameCorrespondence.Initial parent request shared bytes) bytes
          {cell with value := value} := by
  obtain ⟨accounts, same, links, worldRead⟩ := linked
  refine ⟨accounts, same, links, ?_⟩
  intro cell member value found
  have signature : (cell.name, cell.type) ∈ sharedSlotTypes := by
    have present := List.mem_map_of_mem (f := fun cell : InitializedCell => (cell.name, cell.type)) member
    rw [inventory.signature] at present
    exact List.mem_reverse.mp present
  have readValue : ∀ name type location expected,
      (selected : ∃ other ∈ cells, other.name = name ∧ other.reference = .cellRef type location) →
      cell.name = name → store.read? location = some expected → value = expected := by
    intro name type location expected selected named read
    have located := named_location inventory member named selected
    exact Option.some.inj ((located ▸ found).symm.trans read)
  have world := readValue "world" AccountState.type layout.storage.world (StorageCorrespondence.world accounts) inventory.shared.world
  have complete := readValue "worldComplete" .bool layout.storage.complete (Value.bool shared.complete) inventory.shared.complete
  have logs := readValue "logs" WordMapping.type layout.logs (WordMapping.encode shared.logs) inventory.shared.logs
  have logSize := readValue "logSize" .word layout.logSize (Value.word shared.logSize) inventory.shared.logSize
  have balances := readValue "balances" WordMapping.type layout.balances (WordMapping.encode shared.balances) inventory.shared.balances
  constructor
  · intro expected specified
    change RuntimeInitializedEffects.expected accounts
      (ChildFrameCorrespondence.Initial parent request shared bytes).runtime.runtime.runtime.runtime cell.name = some expected at specified
    change value = expected
    simp only [sharedSlotTypes, Ambient.slots, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at signature
    rcases signature with (signature | signature | signature | signature | signature) | signature
    all_goals try (obtain ⟨named, typed⟩ := Prod.mk.inj signature; rw [named] at specified)
    · cases specified
      exact world named worldRead
    · cases specified
      exact complete named resources.complete
    · contradiction
    · contradiction
    · contradiction
    · rcases signature with signature | signature | signature | signature | signature | signature | signature | signature | signature | signature | signature | signature
      all_goals obtain ⟨named, _⟩ := Prod.mk.inj signature
      all_goals rw [named] at specified
      all_goals contradiction
  · intro expected specified
    change EnvironmentBuiltinCorrespondence.observation
      (ChildFrameCorrespondence.Initial parent request shared bytes).runtime.runtime.runtime.environment cell.name cell.type = some expected at specified
    change value = expected
    have ambientPair : (cell.name, cell.type) ∈ Ambient.slots := by
      simp only [sharedSlotTypes, List.mem_append] at signature
      rcases signature with sharedMember | ambientMember
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at sharedMember
        rcases sharedMember with equal | equal | equal | equal | equal
        all_goals obtain ⟨named, typed⟩ := Prod.mk.inj equal
        all_goals rw [named, typed] at specified
        all_goals contradiction
      · exact ambientMember
    have ambientName : cell.name ∈ Ambient.slots.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) ambientPair
    have inherited : EnvironmentBuiltinCorrespondence.observation
        (ChildFrameCorrespondence.Initial parent request shared bytes).runtime.runtime.runtime.environment cell.name cell.type =
        EnvironmentBuiltinCorrespondence.observation parent.runtime.runtime.runtime.runtime.environment cell.name cell.type := by
      simp only [Ambient.slots, List.mem_cons, List.not_mem_nil, or_false] at ambientPair
      rcases ambientPair with equal | equal | equal | equal | equal | equal | equal | equal | equal | equal | equal | equal
      all_goals obtain ⟨named, typed⟩ := Prod.mk.inj equal
      all_goals rw [named, typed]
      all_goals rfl
    rw [inherited] at specified
    have sameValue := ambient cell member ambientName expected specified
    have sameRead := (reads inventory valid).1 cell member ambientName
    exact (Option.some.inj (found.symm.trans sameRead)).trans sameValue
  · intro named
    change cell.name = "code" at named
    have present := List.mem_map_of_mem (f := Prod.fst) signature
    simp [named, sharedSlotTypes, Ambient.slots] at present
  · intro named
    change cell.name = "codeKnown" at named
    have present := List.mem_map_of_mem (f := Prod.fst) signature
    simp [named, sharedSlotTypes, Ambient.slots] at present
  · intro named
    change cell.name = "returnData" at named
    have present := List.mem_map_of_mem (f := Prod.fst) signature
    simp [named, sharedSlotTypes, Ambient.slots] at present
  · exact fun named => logs named resources.logs
  · exact fun named => logSize named resources.logSize
  · exact fun named => balances named resources.balances

/-- The exact inventory expected by actual allocateFrame is reconstructed at
callback entry, including writes performed since the closure was captured. -/
theorem refresh_ready {layout : Layout} {cells : List InitializedCell} {creator : Nat}
    (inventory : Inventory layout cells creator) {store : Store}
    (bounded : layout.boundary ≤ store.length)
    (valid : (context inventory).valid (prefixRead layout.boundary store))
    (parent : RuntimeCallEffectsSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8)
    (ambient : ∀ cell ∈ cells, cell.name ∈ Ambient.slots.map Prod.fst →
      ContractEnvironmentCorrespondence.initializedValue parent.runtime.runtime.runtime.runtime.environment cell)
    {anchors : List CatalogWorldCorrespondence.Anchor}
    (linked : RuntimeLinkedWorldCorrespondence.StateRel anchors shared.world layout.storage.world store)
    (resources : AccountCallCorrespondence.SharedStateRel (sharedLocations layout) shared store) :
    ∃ accounts creatorValue, accounts.map Prod.fst = shared.world ∧ CatalogWorldCorrespondence.Links anchors accounts ∧
      InitializedCells (ChildFrameCorrespondence.refresh store cells) store ∧
      (ChildFrameCorrespondence.refresh store cells).map (fun cell => (cell.name, cell.type)) = sharedSlotTypes.reverse ∧
      CellLocations (ChildFrameCorrespondence.refresh store cells) ∧
      (∀ cell ∈ ChildFrameCorrespondence.refresh store cells,
        ChildFrameCorrespondence.Observed accounts (ChildFrameCorrespondence.Initial parent request shared bytes) bytes cell) ∧
      store.read? creator = some creatorValue ∧
      (∀ cell ∈ ChildFrameCorrespondence.refresh store cells, cell.location ≠ creator) := by
  obtain ⟨accounts, same, links, observed⟩ := current_observed inventory valid parent request shared bytes ambient linked resources
  obtain ⟨creatorValue, creatorRead⟩ := (reads inventory valid).2
  have below : ∀ cell ∈ cells, cell.location < store.length :=
    fun cell member => Nat.lt_of_lt_of_le (inventory.below cell member) bounded
  refine ⟨accounts, creatorValue, same, links, ChildFrameCorrespondence.refresh_stored below,
    (ChildFrameCorrespondence.refresh_signature store cells).trans inventory.signature,
    ChildFrameCorrespondence.refresh_locations inventory.separate,
    ChildFrameCorrespondence.refresh_observed observed below, creatorRead, ?_⟩
  intro cell member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact inventory.creatorSeparate original present


end Solcore.Frontend.RustHull.ChildCallbackContextCorrespondence
