import Solcore.Frontend.RustHull.Semantics.Layers
import Solcore.Frontend.RustHull.Internal.RuntimeObjects
import Solcore.Frontend.RustHull.Internal.StorageState
import Solcore.Frontend.RustHull.Internal.EffectBuiltins

/-!
# Effect layers: storage, environment, logs

The frame and message proofs of the storage, environment and log layers.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeEffectsCorrespondence
/-! Memory and account-storage calls share one concrete resource model. Each
operation preserves the other component, and all remaining resource cells keep
their initialized observations across recursive Hull evaluation and assembly. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeEffectsCorrespondence
open Correspondence DerivationCorrespondence ScalarExecution

structure Layout where
  boundary : Nat
  memory : Nat
  storage : StorageBuiltinCorrespondence.Locations
  distinct : (memory :: storage.all).Nodup
  below : ∀ location, location ∈ memory :: storage.all → location < boundary

def mutable (layout : Layout) : List Nat :=
  [layout.memory, layout.storage.memorySize] ++ layout.storage.mutable

structure Resources (layout : Layout) (baseline : Nat → Option Core.Value)
    (state : RuntimeEffectsSemantics.State) (read : Nat → Option Core.Value) : Prop where
  memory : read layout.memory = some (Core.WordMapping.encode state.memory.words)
  size : read layout.storage.memorySize = some (.word state.memory.size)
  world : ∃ accounts : StorageCorrespondence.Accounts,
    accounts.map Prod.fst = state.storage.world ∧ read layout.storage.world = some (StorageCorrespondence.world accounts)
  address : read layout.storage.address = some (.word state.storage.address)
  complete : read layout.storage.complete = some (.bool state.storage.complete)
  isStatic : read layout.storage.isStatic = some (.bool state.storage.isStatic)
  exit : read layout.storage.exit = some (.word state.storage.exit)
  returnOffset : read layout.storage.returnOffset = some (.word state.storage.returnOffset)
  returnSize : read layout.storage.returnSize = some (.word state.storage.returnSize)
  other : ∀ location, location ∉ mutable layout → read location = baseline location

def model (layout : Layout) (baseline : Nat → Option Core.Value) : StateModel RuntimeEffectsSemantics.State :=
  StateModel.cutoff layout.boundary (Resources layout baseline)

private theorem read_below {layout : Layout} (location : Nat)
    (member : location ∈ layout.memory :: layout.storage.all) (store : Core.Store) :
    prefixRead layout.boundary store location = store.read? location := by
  simp only [prefixRead, layout.below location member, ↓reduceIte]

private theorem mutable_member {layout : Layout} {location : Nat} (member : location ∈ mutable layout) :
    location ∈ layout.memory :: layout.storage.all := by
  simp [mutable, StorageBuiltinCorrespondence.Locations.mutable] at member
  simp [StorageBuiltinCorrespondence.Locations.all]
  rcases member with same | same | same | same | same | same <;> simp [same]

private theorem storage_disjoint {layout : Layout} {location : Nat}
    (member : location ∈ StorageEffectCorrespondence.required layout.storage) :
    location ≠ layout.memory ∧ location ≠ layout.storage.memorySize := by
  have head := (List.nodup_cons.mp layout.distinct).1
  have tail : (StorageEffectCorrespondence.required layout.storage ++ [layout.storage.memorySize]).Nodup :=
    (List.nodup_cons.mp layout.distinct).2
  refine ⟨?_, (List.nodup_append.mp tail).2.2 location member _ (by simp)⟩
  intro same
  apply head
  rw [← same]
  change location ∈ StorageEffectCorrespondence.required layout.storage ++ [layout.storage.memorySize]
  simpa only [List.mem_append, List.mem_singleton] using (Or.inl member : location ∈ StorageEffectCorrespondence.required layout.storage ∨ location = layout.storage.memorySize)

theorem memory_related {layout : Layout} {baseline : Nat → Option Core.Value}
    {world : World} {state : Semantics.State RuntimeEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline) world state store) :
    MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize state.external.memory store := by
  refine ⟨?_, ?_, ?_⟩
  · intro same
    have absent := (List.nodup_cons.mp layout.distinct).1
    apply absent
    simp [StorageBuiltinCorrespondence.Locations.all, same]
  · exact (read_below (layout := layout) _ (by simp) store).symm.trans related.external.2.2.memory
  · exact (read_below (layout := layout) _ (by simp [StorageBuiltinCorrespondence.Locations.all]) store).symm.trans related.external.2.2.size

theorem storage_related {layout : Layout} {baseline : Nat → Option Core.Value}
    {world : World} {state : Semantics.State RuntimeEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline) world state store) :
    StorageBuiltinCorrespondence.StateRel layout.storage state.external.storage store := by
  have resources := related.external.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, (List.nodup_cons.mp layout.distinct).2⟩
  · obtain ⟨accounts, same, found⟩ := resources.world
    exact ⟨accounts, same, (read_below (layout := layout) layout.storage.world
      (by simp [StorageBuiltinCorrespondence.Locations.all]) store).symm.trans found⟩
  all_goals first
    | exact (read_below (layout := layout) _ (by simp [StorageBuiltinCorrespondence.Locations.all]) store).symm.trans resources.address
    | exact (read_below (layout := layout) _ (by simp [StorageBuiltinCorrespondence.Locations.all]) store).symm.trans resources.complete
    | exact (read_below (layout := layout) _ (by simp [StorageBuiltinCorrespondence.Locations.all]) store).symm.trans resources.isStatic
    | exact (read_below (layout := layout) _ (by simp [StorageBuiltinCorrespondence.Locations.all]) store).symm.trans resources.exit
    | exact (read_below (layout := layout) _ (by simp [StorageBuiltinCorrespondence.Locations.all]) store).symm.trans resources.returnOffset
    | exact (read_below (layout := layout) _ (by simp [StorageBuiltinCorrespondence.Locations.all]) store).symm.trans resources.returnSize

structure Frame (layout : Layout) (initial final : Core.Store) : Prop where
  length_le : initial.length ≤ final.length
  read : ∀ location value, location ∉ mutable layout → initial.read? location = some value → final.read? location = some value

theorem Frame.of_memory {layout : Layout} {initial final : Core.Store}
    (frame : MemoryCorrespondence.Frame layout.memory layout.storage.memorySize initial final) :
    Frame layout initial final :=
  ⟨frame.length, fun location value outside found => frame.read location value
    (fun same => outside (by simp [mutable, same])) (fun same => outside (by simp [mutable, same])) found⟩

theorem Frame.of_storage {layout : Layout} {initial final : Core.Store}
    (frame : StorageBuiltinCorrespondence.Frame layout.storage initial final) : Frame layout initial final :=
  ⟨frame.length_le, fun location value outside found => frame.preserved location value
    (fun member => outside (by simp [mutable, member])) found⟩

theorem frame_above {layout : Layout} {initial final : Core.Store}
    (frame : Frame layout initial final) : StoreRetainsFrom layout.boundary initial final := by
  refine ⟨frame.length_le, ?_⟩
  intro location separated bounded
  have found : initial.read? location = some initial[location] := List.getElem?_eq_getElem bounded
  rw [found]
  apply frame.read location _ _ found
  intro member
  have below := layout.below location (mutable_member member)
  omega

theorem memory_preserves_storage {layout : Layout} {state : StorageSemantics.State}
    {initial final : Core.Store}
    (related : StorageBuiltinCorrespondence.StateRel layout.storage state initial)
    (frame : MemoryCorrespondence.Frame layout.memory layout.storage.memorySize initial final) :
    StorageBuiltinCorrespondence.StateRel layout.storage state final := by
  have retain : ∀ location value, location ∈ StorageEffectCorrespondence.required layout.storage →
      initial.read? location = some value → final.read? location = some value := by
    intro location value member found
    have separate := storage_disjoint (layout := layout) member
    exact frame.read location value separate.1 separate.2 found
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, related.distinct⟩
  · obtain ⟨accounts, same, found⟩ := related.world
    exact ⟨accounts, same, retain _ _ (by simp [StorageEffectCorrespondence.required]) found⟩
  all_goals first
    | exact retain _ _ (by simp [StorageEffectCorrespondence.required]) related.address
    | exact retain _ _ (by simp [StorageEffectCorrespondence.required]) related.complete
    | exact retain _ _ (by simp [StorageEffectCorrespondence.required]) related.isStatic
    | exact retain _ _ (by simp [StorageEffectCorrespondence.required]) related.exit
    | exact retain _ _ (by simp [StorageEffectCorrespondence.required]) related.returnOffset
    | exact retain _ _ (by simp [StorageEffectCorrespondence.required]) related.returnSize

theorem storage_preserves_memory {layout : Layout} {state : MemorySemantics.State}
    {initial final : Core.Store}
    (related : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize state initial)
    (frame : StorageBuiltinCorrespondence.Frame layout.storage initial final) :
    MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize state final := by
  have outside : ∀ location, location ∈ layout.storage.mutable →
      location ≠ layout.memory ∧ location ≠ layout.storage.memorySize := by
    intro location member
    apply storage_disjoint
    simp [StorageBuiltinCorrespondence.Locations.mutable] at member
    simp [StorageEffectCorrespondence.required]
    rcases member with same | same | same | same <;> simp [same]
  exact ⟨related.distinct,
    frame.preserved _ _ (fun member => (outside _ member).1 rfl) related.memory,
    frame.preserved _ _ (fun member => (outside _ member).2 rfl) related.size⟩

theorem resources_preserved {layout : Layout} {baseline : Nat → Option Core.Value}
    {initial final : Core.Store} {before after : RuntimeEffectsSemantics.State}
    (bounded : layout.boundary ≤ initial.length)
    (beforeResources : Resources layout baseline before (prefixRead layout.boundary initial))
    (afterMemory : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize after.memory final)
    (afterStorage : StorageBuiltinCorrespondence.StateRel layout.storage after.storage final)
    (frame : Frame layout initial final) : Resources layout baseline after (prefixRead layout.boundary final) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (read_below (layout := layout) _ (by simp) final).trans afterMemory.memory
  · exact (read_below (layout := layout) _ (by simp [StorageBuiltinCorrespondence.Locations.all]) final).trans afterMemory.size
  · obtain ⟨accounts, same, found⟩ := afterStorage.world
    exact ⟨accounts, same, (read_below (layout := layout) layout.storage.world
      (by simp [StorageBuiltinCorrespondence.Locations.all]) final).trans found⟩
  · exact (read_below (layout := layout) _ (by simp [StorageBuiltinCorrespondence.Locations.all]) final).trans afterStorage.address
  · exact (read_below (layout := layout) _ (by simp [StorageBuiltinCorrespondence.Locations.all]) final).trans afterStorage.complete
  · exact (read_below (layout := layout) _ (by simp [StorageBuiltinCorrespondence.Locations.all]) final).trans afterStorage.isStatic
  · exact (read_below (layout := layout) _ (by simp [StorageBuiltinCorrespondence.Locations.all]) final).trans afterStorage.exit
  · exact (read_below (layout := layout) _ (by simp [StorageBuiltinCorrespondence.Locations.all]) final).trans afterStorage.returnOffset
  · exact (read_below (layout := layout) _ (by simp [StorageBuiltinCorrespondence.Locations.all]) final).trans afterStorage.returnSize
  · intro location outside
    rw [← beforeResources.other location outside]
    by_cases below : location < layout.boundary
    · simp only [prefixRead, below, ↓reduceIte]
      have bound : location < initial.length := Nat.lt_of_lt_of_le below bounded
      have found : initial.read? location = some initial[location] := List.getElem?_eq_getElem bound
      rw [found]
      exact frame.read location _ outside found
    · simp only [prefixRead, below, ↓reduceIte]

def supported (name : String) : Prop :=
  MemoryEffectCorrespondence.supported name ∨ StorageEffectCorrespondence.supported name

private theorem memory_unsupported (operation : StorageBuiltinCorrespondence.Operation)
    (type : Ty) (arguments : List Semantics.Value) (state : MemorySemantics.State) :
    MemorySemantics.builtin operation.name type arguments state = none := by
  cases operation with | load transient | store transient => cases transient <;> rfl

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots) :
    ExternalCallPreservation supported (model layout baseline) slots RuntimeEffectsSemantics.effects := by
  intro functions name type sources initial final result available notFunction called
  rcases available with memory | storage
  · obtain ⟨operation, rfl⟩ := memory
    cases called with
    | function selected called => rw [notFunction] at selected; contradiction
    | primitive absent computed =>
        cases operation <;> simp [MemoryBuiltinCorrespondence.Operation.name, Semantics.primitive?] at computed
    | external absent notPrimitive computed =>
        intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
        obtain ⟨computedResult, computedState, target, finalStore, meaning, resultRelated, evaluated, memoryFinal, frame⟩ :=
          MemoryBuiltinCorrespondence.preserves operation compiled related runtime memoryMember memorySizeMember
            (memory_related state) packed type
        have combined : RuntimeEffectsSemantics.builtin operation.name type sources initial.external =
            some (computedResult, {initial.external with memory := computedState}) := by
          simp only [RuntimeEffectsSemantics.builtin, meaning]
        have same := Option.some.inj (computed.symm.trans combined)
        cases same
        have retained : ClosuresPreserved argumentStore finalStore :=
          MemoryEffectCorrespondence.closures_preserved (memory_related state) frame
        exact ⟨target, finalStore, resultRelated, evaluated,
          state.cutoff_effect (frame_above (Frame.of_memory frame))
            (resources_preserved state.external.1 state.external.2.2 memoryFinal
              (memory_preserves_storage (storage_related state) frame) (Frame.of_memory frame)),
          installed.preserved retained, retained⟩
  · obtain ⟨operation, rfl⟩ := storage
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
        have combined : RuntimeEffectsSemantics.builtin operation.name type sources initial.external =
            some (computedResult, {initial.external with storage := computedState}) := by
          simp only [RuntimeEffectsSemantics.builtin, memory_unsupported, meaning, Option.map_some]
        have same := Option.some.inj (computed.symm.trans combined)
        cases same
        have retained : ClosuresPreserved argumentStore finalStore :=
          StorageEffectCorrespondence.closures_preserved (storage_related state) frame
        exact ⟨target, finalStore, resultRelated, evaluated,
          state.cutoff_effect (frame_above (Frame.of_storage frame))
            (resources_preserved state.external.1 state.external.2.2
              (storage_preserves_memory (memory_related state) frame) storageFinal (Frame.of_storage frame)),
          installed.preserved retained, retained⟩

/-- Concrete initialization supplies the common boundary. Distinctness covers
all cells allocated for memory and account storage in that initialization. -/
def initialLayout {memory : Nat} {locations : StorageBuiltinCorrespondence.Locations}
    {state : RuntimeEffectsSemantics.State} {store : Core.Store}
    (memoryRelated : MemoryCorrespondence.StateRel memory locations.memorySize state.memory store)
    (storageRelated : StorageBuiltinCorrespondence.StateRel locations state.storage store)
    (distinct : (memory :: locations.all).Nodup) : Layout where
  boundary := store.length
  memory := memory
  storage := locations
  distinct := distinct
  below := by
    intro location member
    simp [StorageBuiltinCorrespondence.Locations.all] at member
    rcases member with same | same | same | same | same | same | same | same | same
    · subst location; exact (List.getElem?_eq_some_iff.mp memoryRelated.memory).1
    · subst location
      obtain ⟨_, _, read⟩ := storageRelated.world
      exact (List.getElem?_eq_some_iff.mp read).1
    all_goals subst location
    all_goals first
      | exact (List.getElem?_eq_some_iff.mp storageRelated.address).1
      | exact (List.getElem?_eq_some_iff.mp storageRelated.complete).1
      | exact (List.getElem?_eq_some_iff.mp storageRelated.isStatic).1
      | exact (List.getElem?_eq_some_iff.mp storageRelated.exit).1
      | exact (List.getElem?_eq_some_iff.mp storageRelated.returnOffset).1
      | exact (List.getElem?_eq_some_iff.mp storageRelated.returnSize).1
      | exact (List.getElem?_eq_some_iff.mp memoryRelated.size).1

theorem initial_state {memory : Nat} {locations : StorageBuiltinCorrespondence.Locations}
    {state : RuntimeEffectsSemantics.State} {store : Core.Store}
    (memoryRelated : MemoryCorrespondence.StateRel memory locations.memorySize state.memory store)
    (storageRelated : StorageBuiltinCorrespondence.StateRel locations state.storage store)
    (distinct : (memory :: locations.all).Nodup) :
    StateRel (model (initialLayout memoryRelated storageRelated distinct) (prefixRead store.length store))
      [] ⟨[], state⟩ store := by
  apply StateRel.cutoff_initial
  let layout := initialLayout memoryRelated storageRelated distinct
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ => rfl⟩
  · exact (read_below (layout := layout) _ (by simp [layout, initialLayout]) store).trans memoryRelated.memory
  · exact (read_below (layout := layout) _
      (by simp [layout, initialLayout, StorageBuiltinCorrespondence.Locations.all]) store).trans memoryRelated.size
  · obtain ⟨accounts, same, found⟩ := storageRelated.world
    exact ⟨accounts, same, (read_below (layout := layout) locations.world
      (by simp [layout, initialLayout, StorageBuiltinCorrespondence.Locations.all]) store).trans found⟩
  all_goals first
    | exact (read_below (layout := layout) _ (by simp [layout, initialLayout, StorageBuiltinCorrespondence.Locations.all]) store).trans storageRelated.address
    | exact (read_below (layout := layout) _ (by simp [layout, initialLayout, StorageBuiltinCorrespondence.Locations.all]) store).trans storageRelated.complete
    | exact (read_below (layout := layout) _ (by simp [layout, initialLayout, StorageBuiltinCorrespondence.Locations.all]) store).trans storageRelated.isStatic
    | exact (read_below (layout := layout) _ (by simp [layout, initialLayout, StorageBuiltinCorrespondence.Locations.all]) store).trans storageRelated.exit
    | exact (read_below (layout := layout) _ (by simp [layout, initialLayout, StorageBuiltinCorrespondence.Locations.all]) store).trans storageRelated.returnOffset
    | exact (read_below (layout := layout) _ (by simp [layout, initialLayout, StorageBuiltinCorrespondence.Locations.all]) store).trans storageRelated.returnSize

/-- Interleaved memory and persistent/transient storage effects preserve their
independent meaning through the compiler's actual multi-function assembly. -/
theorem assemble_program (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    {functions : List Function} {function : Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (eligible : ExecutableProgram supported functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State RuntimeEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions RuntimeEffectsSemantics.effects function sources initial sourceResult final)
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
    (external_preserves layout baseline slots memoryMember worldMember addressMember completeMember staticMember
      memorySizeMember exitMember offsetMember sizeMember) eligible values evaluated
    runtimeLength covered runtimeRelated separated state

end Solcore.Frontend.RustHull.RuntimeEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeEffectsFrameCorrespondence
/-! Interleaved memory and storage effects reach actual frame compilation,
installed closure calls and snapshots of the final independent source state. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeEffectsFrameCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence RuntimeEffectsCorrespondence

abbrev slotTypes := MemoryFrameCorrespondence.slotTypes

/-- Passive observations are supplied by concrete initialization. They exclude
all locations that either component may change. -/
def PassiveCell (layout : Layout) (slots : List EffectSlot) (store : Core.Store)
    (name : String) (value : Core.Value) : Prop :=
  ∃ slot ∈ slots, slot.name = name ∧ slot.location ∉ mutable layout ∧
    slot.location < layout.boundary ∧ store.read? slot.location = some value

def passiveSnapshotNames : List String := ["logs", "logSize", "balances"]

theorem cell_observed {slots : List EffectSlot} {store : Core.Store}
    {cells : AccountRuntime.References} {environment : Core.Environment}
    (references : AccountRuntime.frameReferences (slotTypes slots) = .ok cells)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id environment)
    {name : String} {type : Core.Ty} {location : Nat} {value : Core.Value}
    (member : ⟨name, type, location⟩ ∈ slots) (found : store.read? location = some value) :
    FrameCellObserved cells environment store name value := by
  apply FrameCellObserved.of_compilation references
    (List.mem_map.mpr ⟨⟨name, type, location⟩, member, rfl⟩)
  · exact runtime _ member
  · exact found

theorem passive_observed {layout : Layout} {slots : List EffectSlot} {initial final : Core.Store}
    {world : World} {source : Semantics.State RuntimeEffectsSemantics.State}
    {cells : AccountRuntime.References} {environment : Core.Environment}
    (references : AccountRuntime.frameReferences (slotTypes slots) = .ok cells)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id environment)
    (related : StateRel (model layout (prefixRead layout.boundary initial)) world source final)
    {name : String} {value : Core.Value} (observed : PassiveCell layout slots initial name value) :
    FrameCellObserved cells environment final name value := by
  obtain ⟨slot, member, named, outside, below, stored⟩ := observed
  apply FrameCellObserved.of_compilation (type := slot.type) references
    (List.mem_map.mpr ⟨slot, member, by simp only [named]⟩)
  · intro binding index looked
    exact runtime slot member binding index (by simpa only [named] using looked)
  · have retained := related.external.2.2.other slot.location outside
    simpa only [prefixRead, below, ↓reduceIte, stored] using retained

def snapshotValues (values : String → Core.Value) (state : RuntimeEffectsSemantics.State)
    (accounts : StorageCorrespondence.Accounts) (name : String) : Core.Value :=
  match name with
  | "memory" => Core.WordMapping.encode state.memory.words
  | "world" => StorageCorrespondence.world accounts
  | "exit" => .word state.storage.exit
  | "returnOffset" => .word state.storage.returnOffset
  | "returnSize" => .word state.storage.returnSize
  | _ => values name

/-- A frame installed earlier retains its captured environment. The body and
completion wrapper observe the final source world, including storage writes
and static-write termination, through the compiler's actual frame references. -/
theorem compileFrame_call_preserves_observed {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {memoryLocation : Nat} {locations : StorageBuiltinCorrespondence.Locations}
    {initial : RuntimeEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, memoryLocation⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, locations.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (memoryInitial : MemoryCorrespondence.StateRel memoryLocation locations.memorySize initial.memory store)
    (storageInitial : StorageBuiltinCorrespondence.StateRel locations initial.storage store)
    (distinct : (memoryLocation :: locations.all).Nodup)
    {final : Semantics.State RuntimeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell (initialLayout memoryInitial storageInitial distinct) slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues snapshot final.external accounts)
          (StorageCorrespondence.get accounts final.external.storage.address final.external.storage.complete)) finalStore ∧
      StateRel (model (initialLayout memoryInitial storageInitial distinct) (prefixRead store.length store))
        extension final finalStore ∧
      finalStore.read? locations.world = some (StorageCorrespondence.world accounts) := by
  obtain ⟨own, body, cells, assembled, references, rfl⟩ := compileFrame_components accepted
  have selected := MemoryFrameCorrespondence.frame_selected accepted
  obtain ⟨signatures, codes, selectedFunction, selectedCode, index, _, sourceSelected,
    signatureCompiled, _, _, _, _, _⟩ := assemble_selection assembled
  have sameFunction := Option.some.inj (sourceSelected.symm.trans selected)
  subst selectedFunction
  obtain ⟨parameters, resultType⟩ := MemoryFrameCorrespondence.frame_signature signatureCompiled
  have argumentValues : ValuesRel own.parameters [] [] := by rw [parameters]; exact .nil
  obtain ⟨extension, status, bodyStore, related, executed, state, _⟩ :=
    assemble_program (initialLayout memoryInitial storageInitial distinct) (prefixRead store.length store) slots
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      assembled selected eligible argumentValues evaluated
      (runtimeValues := values.reverse) (caller := bundleValues values :: captured)
      (by simpa [AccountRuntime.frameScope, slotTypes, MemoryFrameCorrespondence.slotTypes] using length)
      (MemoryFrameCorrespondence.frame_coverage _) runtime separated
      (initial_state memoryInitial storageInitial distinct)
  have finalStorage := storage_related state
  obtain ⟨accounts, sourceWorld, worldRead⟩ := finalStorage.world
  have finalWorld := cell_observed references runtime worldMember worldRead
  have finalAddress := cell_observed references runtime addressMember finalStorage.address
  have finalComplete := cell_observed references runtime completeMember finalStorage.complete
  have finalSnapshot : ∀ name ∈ frameSnapshotNames,
      FrameCellObserved cells (values.reverse ++ .unit :: bundleValues values :: captured)
        bodyStore name (snapshotValues snapshot final.external accounts name) := by
    intro name member
    simp [frameSnapshotNames] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cell_observed references runtime exitMember finalStorage.exit
    · exact cell_observed references runtime offsetMember finalStorage.returnOffset
    · exact cell_observed references runtime sizeMember finalStorage.returnSize
    · exact cell_observed references runtime memoryMember (memory_related state).memory
    · exact passive_observed references runtime state (snapshotObserved "logs" (by simp [passiveSnapshotNames]))
    · exact passive_observed references runtime state (snapshotObserved "logSize" (by simp [passiveSnapshotNames]))
    · exact passive_observed references runtime state (snapshotObserved "balances" (by simp [passiveSnapshotNames]))
    · exact finalWorld
  have completed := frameCompletion_evaluates executed accounts final.external.storage.address final.external.storage.complete
    finalWorld finalAddress finalComplete finalSnapshot
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.getStore_extension accounts
    final.external.storage.address final.external.storage.complete
    (status :: (values.reverse ++ .unit :: bundleValues values :: captured)) bodyStore
  refine ⟨extension, status, accounts, _, sourceWorld, by simpa only [resultType] using related,
    frameUnpack_call_evaluates (by simpa only [slotTypes, MemoryFrameCorrespondence.slotTypes, List.length_map] using length)
      closureRelated resolved supplied completed, ?_, ?_⟩
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    simpa only [List.nil_append] using state.appendCore suffix
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    exact ((StoreRetains.append bodyStore suffix).read locations.world
      (List.getElem?_eq_some_iff.mp worldRead).1).trans worldRead

theorem compileFrame_call_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {memoryLocation : Nat} {locations : StorageBuiltinCorrespondence.Locations}
    {initial : RuntimeEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, memoryLocation⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, locations.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (memoryInitial : MemoryCorrespondence.StateRel memoryLocation locations.memorySize initial.memory store)
    (storageInitial : StorageBuiltinCorrespondence.StateRel locations initial.storage store)
    (distinct : (memoryLocation :: locations.all).Nodup)
    {final : Semantics.State RuntimeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell (initialLayout memoryInitial storageInitial distinct) slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues snapshot final.external accounts)
          (StorageCorrespondence.get accounts final.external.storage.address final.external.storage.complete)) finalStore ∧
      StateRel (model (initialLayout memoryInitial storageInitial distinct) (prefixRead store.length store))
        extension final finalStore := by
  obtain ⟨extension, status, accounts, finalStore, represented, related, executed, state, _⟩ :=
    compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length runtime separated
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      memoryInitial storageInitial distinct evaluated snapshot snapshotObserved
  exact ⟨extension, status, accounts, finalStore, represented, related, executed, state⟩

/-- Direct evaluation of freshly compiled frame code is a special case of the
same theorem for captured calls. -/
theorem compileFrame_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {memoryLocation : Nat} {locations : StorageBuiltinCorrespondence.Locations}
    {initial : RuntimeEffectsSemantics.State}
    {initialStore store : Core.Store} {values environment : Core.Environment} {argument : Core.Expr}
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: environment))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, memoryLocation⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, locations.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (memoryInitial : MemoryCorrespondence.StateRel memoryLocation locations.memorySize initial.memory store)
    (storageInitial : StorageBuiltinCorrespondence.StateRel locations initial.storage store)
    (distinct : (memoryLocation :: locations.all).Nodup)
    {final : Semantics.State RuntimeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell (initialLayout memoryInitial storageInitial distinct) slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment initialStore (.apply compiled argument)
        (frameCompletionValue status (snapshotValues snapshot final.external accounts)
          (StorageCorrespondence.get accounts final.external.storage.address final.external.storage.complete)) finalStore ∧
      StateRel (model (initialLayout memoryInitial storageInitial distinct) (prefixRead store.length store))
        extension final finalStore := by
  obtain ⟨own, body, cells, _, _, rfl⟩ := compileFrame_components accepted
  exact compileFrame_call_preserves accepted eligible (CapturedClosure.lambda _ _ _ environment)
    Core.Evaluates.lambda supplied length runtime separated memoryMember worldMember addressMember completeMember
    staticMember memorySizeMember exitMember offsetMember sizeMember memoryInitial storageInitial distinct
    evaluated snapshot snapshotObserved

end Solcore.Frontend.RustHull.RuntimeEffectsFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeEffectsProjectionPreservation
/-! Immutable account observations of the independent memory/storage model.
The public runtime uses the entry address to complete a message; this theorem
identifies it with the address observed after an arbitrary source execution. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeEffectsProjectionPreservation

structure Context where
  address : Core.Word
  complete : Bool
  isStatic : Bool

def storageContext (state : StorageSemantics.State) : Context :=
  ⟨state.address, state.complete, state.isStatic⟩

def context (state : RuntimeEffectsSemantics.State) : Context := storageContext state.storage

theorem load_context (state : StorageSemantics.State) (key : Core.Word) (transient : Bool) :
    storageContext (StorageSemantics.load state key transient).2 = storageContext state := by
  unfold StorageSemantics.load
  split <;> rfl

theorem store_context (state : StorageSemantics.State) (key value : Core.Word) (transient : Bool) :
    storageContext (StorageSemantics.store state key value transient).2 = storageContext state := by
  unfold StorageSemantics.store
  split
  · rfl
  · split <;> rfl

theorem storage_builtin_context {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : StorageSemantics.State} {result : Semantics.Result Semantics.Value}
    (called : StorageSemantics.builtin name type arguments initial = some (result, final)) :
    storageContext final = storageContext initial := by
  unfold StorageSemantics.builtin at called
  split at called
  all_goals try contradiction
  all_goals have changed := congrArg (fun output => storageContext output.2) (Option.some.inj called)
  all_goals simp only [load_context, store_context] at changed
  all_goals exact changed.symm

theorem builtin_context {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : RuntimeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (called : RuntimeEffectsSemantics.builtin name type arguments initial = some (result, final)) :
    context final = context initial := by
  unfold RuntimeEffectsSemantics.builtin at called
  split at called
  · cases Option.some.inj called
    rfl
  · rename_i memory
    cases storage : StorageSemantics.builtin name type arguments initial.storage with
    | none => simp [storage] at called
    | some output =>
      rcases output with ⟨storageResult, storageState⟩
      simp only [storage, Option.map_some, Option.some.injEq, Prod.mk.injEq] at called
      rcases called with ⟨rfl, rfl⟩
      exact storage_builtin_context storage

theorem preserves : EffectProjectionPreservation.Preserves RuntimeEffectsSemantics.effects context where
  builtin := builtin_context
  assembly := False.elim
  revert := False.elim

theorem function_context {functions : List Function} {function : Function}
    {arguments : List Semantics.Value}
    {initial final : Semantics.State RuntimeEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions RuntimeEffectsSemantics.effects
      function arguments initial result final) :
    context final.external = context initial.external :=
  EffectProjectionPreservation.function_preserves preserves evaluated

theorem function_observations {functions : List Function} {function : Function}
    {arguments : List Semantics.Value}
    {initial final : Semantics.State RuntimeEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions RuntimeEffectsSemantics.effects
      function arguments initial result final) :
    final.external.storage.address = initial.external.storage.address ∧
    final.external.storage.complete = initial.external.storage.complete ∧
    final.external.storage.isStatic = initial.external.storage.isStatic :=
  ⟨congrArg Context.address (function_context evaluated),
   congrArg Context.complete (function_context evaluated),
   congrArg Context.isStatic (function_context evaluated)⟩

end Solcore.Frontend.RustHull.RuntimeEffectsProjectionPreservation
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractRuntimeEffectsCorrespondence
/-! Independent memory and storage outcomes pass through the actual message
completion code, including static-write exit status and account finalization. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractRuntimeEffectsCorrespondence
open Correspondence ScalarExecution CodeBuilder

abbrev resultValue := ContractMemoryCorrespondence.resultValue

def succeeded : Semantics.Result Semantics.Value → Bool
  | .value _ => true
  | .fault _ => false

def passiveValues (balances : StorageSemantics.Words) (name : String) : Core.Value :=
  if name = "balances" then Core.WordMapping.encode balances
  else if name = "logs" then Core.WordMapping.encode []
  else .word (Core.Word.ofNatModulo 0)

def snapshotValues (state : RuntimeEffectsSemantics.State) (accounts : StorageCorrespondence.Accounts)
    (balances : StorageSemantics.Words) : String → Core.Value :=
  RuntimeEffectsFrameCorrespondence.snapshotValues (passiveValues balances) state accounts

def messageValue (result : Semantics.Result Semantics.Value) (state : RuntimeEffectsSemantics.State)
    (accounts : StorageCorrespondence.Accounts) (target : Core.Word) (balances : StorageSemantics.Words) : Core.Value :=
  let snapshot := snapshotValues state accounts balances
  match StorageCorrespondence.get accounts state.storage.address state.storage.complete with
  | .error reason => completedMessageValue (.inLeft .unit (.word reason)) false state.storage.exit
      snapshot (Core.WordMapping.encode []) accounts target balances
  | .ok (account, _) => completedMessageValue (resultValue result) (succeeded result) state.storage.exit
      snapshot (Core.WordMapping.encode account.storage) accounts target balances

def MessageRel (result : Semantics.Result Semantics.Value) (state : RuntimeEffectsSemantics.State)
    (target : Core.Word) (balances : StorageSemantics.Words) (value : Core.Value) : Prop :=
  ∃ accounts : StorageCorrespondence.Accounts,
    accounts.map Prod.fst = state.storage.world ∧ value = messageValue result state accounts target balances

theorem message_evaluates {depth : Nat} {environment : Core.Environment}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {target deploying framed : Code}
    {worldLocation balancesLocation : Nat} {initial : Core.Store}
    (sourceResult : Semantics.Result Semantics.Value) (state : RuntimeEffectsSemantics.State)
    (accounts : StorageCorrespondence.Accounts) (address : Core.Word) (balances : StorageSemantics.Words)
    {status : Core.Value} (statusRelated : ResultRel .unit sourceResult status)
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type worldLocation))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false))
    (framedValue : CodeValue depth environment framed
      (frameCompletionValue status (snapshotValues state accounts balances)
        (StorageCorrespondence.get accounts state.storage.address state.storage.complete)))
    (worldFound : initial.read? worldLocation = some (StorageCorrespondence.world accounts))
    (balancesFound : initial.read? balancesLocation = some (Core.WordMapping.encode balances)) :
    ∃ final, Core.Evaluates environment initial
      (AccountRuntime.completeMessage shared images target deploying framed depth)
      (messageValue sourceResult state accounts address balances) final := by
  cases got : StorageCorrespondence.get accounts state.storage.address state.storage.complete with
  | error reason =>
      have framedRelated : CodeValue depth environment framed
          (.pair (.inLeft .unit (.word reason))
            (frameSnapshotValue (snapshotValues state accounts balances) (Core.WordMapping.encode []))) := by
        simpa only [got, frameCompletionValue] using framedValue
      obtain ⟨final, evaluated⟩ := completeMessage_evaluates accounts balances worldReference balancesReference
        targetValue deployingValue framedRelated (MessageStatus.failure (.word reason)) rfl worldFound balancesFound
      exact ⟨final, by simpa only [messageValue, got] using evaluated⟩
  | ok pair =>
      rcases pair with ⟨account, identity⟩
      have framedRelated : CodeValue depth environment framed
          (.pair status (frameSnapshotValue (snapshotValues state accounts balances) (Core.WordMapping.encode account.storage))) := by
        simpa only [got, frameCompletionValue] using framedValue
      cases statusRelated with
      | value related =>
          cases related
          obtain ⟨final, evaluated⟩ := completeMessage_evaluates accounts balances worldReference balancesReference
            targetValue deployingValue framedRelated MessageStatus.success rfl worldFound balancesFound
          exact ⟨final, by simpa only [messageValue, got, resultValue, ContractMemoryCorrespondence.resultValue, succeeded] using evaluated⟩
      | language reason =>
          obtain ⟨final, evaluated⟩ := completeMessage_evaluates accounts balances worldReference balancesReference
            targetValue deployingValue framedRelated (MessageStatus.failure (.word reason)) rfl worldFound balancesFound
          exact ⟨final, by simpa only [messageValue, got, resultValue, ContractMemoryCorrespondence.resultValue, succeeded] using evaluated⟩

theorem frameCall_message_evaluates {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (RuntimeEffectsFrameCorrespondence.slotTypes slots) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram RuntimeEffectsCorrespondence.supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {memoryLocation : Nat} {locations : StorageBuiltinCorrespondence.Locations}
    {initial : RuntimeEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument target deploying : Code} {depth : Nat}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before (function depth) closure initialStore)
    (supplied : Core.Evaluates environment initialStore (argument depth) (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeEffectsFrameCorrespondence.slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, memoryLocation⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, locations.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (memoryInitial : MemoryCorrespondence.StateRel memoryLocation locations.memorySize initial.memory store)
    (storageInitial : StorageBuiltinCorrespondence.StateRel locations initial.storage store)
    (distinct : (memoryLocation :: locations.all).Nodup)
    {final : Semantics.State RuntimeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (address : Core.Word) (balances : StorageSemantics.Words)
    (snapshotObserved : ∀ name ∈ RuntimeEffectsFrameCorrespondence.passiveSnapshotNames,
      RuntimeEffectsFrameCorrespondence.PassiveCell
        (RuntimeEffectsCorrespondence.initialLayout memoryInitial storageInitial distinct) slots store name (passiveValues balances name))
    {balancesLocation : Nat}
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type locations.world))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false))
    (balancesFound : store.read? balancesLocation = some (Core.WordMapping.encode balances))
    (balancesOutside : balancesLocation ∉ RuntimeEffectsCorrespondence.mutable
      (RuntimeEffectsCorrespondence.initialLayout memoryInitial storageInitial distinct)) :
    ∃ value finalStore, Core.Evaluates environment before
      (bind (apply function argument) (fun framed => AccountRuntime.completeMessage shared images target deploying framed) depth)
      value finalStore ∧ MessageRel result final.external address balances value := by
  obtain ⟨extension, status, accounts, bodyStore, represented, statusRelated, executed, related, worldFinal⟩ :=
    RuntimeEffectsFrameCorrespondence.compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length
      runtime separated memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      memoryInitial storageInitial distinct evaluated (passiveValues balances) snapshotObserved
  have balancesBound := (List.getElem?_eq_some_iff.mp balancesFound).1
  have balancesFinal : bodyStore.read? balancesLocation = some (Core.WordMapping.encode balances) := by
    have retained := related.external.2.2.other balancesLocation balancesOutside
    simpa only [prefixRead, RuntimeEffectsCorrespondence.initialLayout, balancesBound, ↓reduceIte, balancesFound] using retained
  let frameResult := frameCompletionValue status (snapshotValues final.external accounts balances)
    (StorageCorrespondence.get accounts final.external.storage.address final.external.storage.complete)
  obtain ⟨finalStore, completed⟩ := message_evaluates result final.external accounts address balances
    statusRelated (worldReference.prepend [frameResult]) (balancesReference.prepend [frameResult])
    (targetValue.prepend [frameResult]) (deployingValue.prepend [frameResult])
    (CodeValue.bound depth environment frameResult) worldFinal balancesFinal
  exact ⟨_, finalStore, .letE executed completed, accounts, represented, rfl⟩

end Solcore.Frontend.RustHull.ContractRuntimeEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeEnvironmentEffectsCorrespondence
/-! Concrete environment reads compose with the memory/storage resource model.
Only initialized resource cells represent observations; the common recursive
proof sees no assumed external-call implementation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeEnvironmentEffectsCorrespondence
open Correspondence DerivationCorrespondence ScalarExecution

abbrev Layout := RuntimeEffectsCorrespondence.Layout

def Observations (slots : List EffectSlot) (state : EnvironmentSemantics.State)
    (read : Nat → Option Core.Value) : Prop :=
  ∀ slot ∈ slots, ∀ value, EnvironmentBuiltinCorrespondence.observation state slot.name slot.type = some value →
    read slot.location = some value

def Resources (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot)
    (state : RuntimeEnvironmentEffectsSemantics.State) (read : Nat → Option Core.Value) : Prop :=
  RuntimeEffectsCorrespondence.Resources layout baseline state.runtime read ∧
  Observations slots state.environment read

def model (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot) :
    StateModel RuntimeEnvironmentEffectsSemantics.State :=
  StateModel.cutoff layout.boundary (Resources layout baseline slots)

/-- Runtime allocation separates observation cells from writable resources.
This condition concerns the concrete layout, not execution correctness. -/
def Passive (layout : Layout) (slots : List EffectSlot) : Prop :=
  ∀ slot ∈ slots, ∀ state value,
    EnvironmentBuiltinCorrespondence.observation state slot.name slot.type = some value →
    slot.location ∉ RuntimeEffectsCorrespondence.mutable layout

/-- Injective allocation of distinct names discharges observation separation
from the six concrete cells changed by memory and storage operations. -/
theorem Passive.of_names {layout : Layout} {slots : List EffectSlot}
    (names : ∀ first ∈ slots, ∀ second ∈ slots, first.location = second.location → first.name = second.name)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots) : Passive layout slots := by
  intro slot member state value observed mutable
  have witness : ∃ other ∈ slots,
      other.name ∈ ["memory", "memorySize", "world", "exit", "returnOffset", "returnSize"] ∧
      slot.location = other.location := by
    simp [RuntimeEffectsCorrespondence.mutable, StorageBuiltinCorrespondence.Locations.mutable] at mutable
    rcases mutable with same | same | same | same | same | same
    · exact ⟨_, memoryMember, by simp, same⟩
    · exact ⟨_, memorySizeMember, by simp, same⟩
    · exact ⟨_, worldMember, by simp, same⟩
    · exact ⟨_, exitMember, by simp, same⟩
    · exact ⟨_, offsetMember, by simp, same⟩
    · exact ⟨_, sizeMember, by simp, same⟩
  obtain ⟨other, otherMember, writable, same⟩ := witness
  have named := names slot member other otherMember same
  rw [named] at observed
  simp only [List.mem_cons, List.not_mem_nil, or_false] at writable
  rcases writable with named | named | named | named | named | named
  all_goals rw [named] at observed
  all_goals cases slot.type <;> contradiction

def sourceRuntime (state : Semantics.State RuntimeEnvironmentEffectsSemantics.State) :
    Semantics.State RuntimeEffectsSemantics.State := ⟨state.heap, state.external.runtime⟩

theorem runtime_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {world : World} {state : Semantics.State RuntimeEnvironmentEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots) world state store) :
    StateRel (RuntimeEffectsCorrespondence.model layout baseline) world (sourceRuntime state) store :=
  ⟨related.toHeapRel, related.external.1, related.external.2.1, related.external.2.2.1⟩

theorem observations_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {world : World} {state : Semantics.State RuntimeEnvironmentEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots) world state store) :
    EnvironmentBuiltinCorrespondence.StateRel slots state.external.environment store := by
  intro slot member value observed
  have found := related.external.2.2.2 slot member value observed
  unfold prefixRead at found
  split at found
  · exact found
  · contradiction

theorem runtime_updated {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    (passive : Passive layout slots)
    {world : World} {state : Semantics.State RuntimeEnvironmentEffectsSemantics.State}
    {initial final : Core.Store} {runtime : RuntimeEffectsSemantics.State}
    (before : StateRel (model layout baseline slots) world state initial)
    (after : StateRel (RuntimeEffectsCorrespondence.model layout baseline) world
      {sourceRuntime state with external := runtime} final) :
    StateRel (model layout baseline slots) world
      {state with external := {state.external with runtime := runtime}} final := by
  refine ⟨after.toHeapRel, after.external.1, after.external.2.1, after.external.2.2, ?_⟩
  intro slot member value observed
  have outside := passive slot member state.external.environment value observed
  rw [after.external.2.2.other slot.location outside,
    ← before.external.2.2.1.other slot.location outside]
  exact before.external.2.2.2 slot member value observed

def supported (slots : List EffectSlot) (name : String) : Prop := RuntimeEffectsCorrespondence.supported name ∨
  ∃ operation : EnvironmentSemantics.Operation, operation.name = name ∧
    EnvironmentBuiltinCorrespondence.Available slots operation

private theorem environment_unsupported {name : String} (available : RuntimeEffectsCorrespondence.supported name)
    (type : Ty) (arguments : List Semantics.Value) (state : EnvironmentSemantics.State) :
    EnvironmentSemantics.builtin name type arguments state = none := by
  rcases available with ⟨operation, rfl⟩ | ⟨operation, rfl⟩
  · cases operation <;> rfl
  · cases operation with | load transient | store transient => cases transient <;> rfl

private theorem runtime_unsupported (operation : EnvironmentSemantics.Operation)
    (type : Ty) (arguments : List Semantics.Value) (state : RuntimeEffectsSemantics.State) :
    RuntimeEffectsSemantics.builtin operation.name type arguments state = none := by
  cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
  all_goals rfl

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (passive : Passive layout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots) :
    ExternalCallPreservation (supported slots) (model layout baseline slots) slots RuntimeEnvironmentEffectsSemantics.effects := by
  intro functions name type sources initial final result enabled notFunction called
  rcases enabled with runtimeEnabled | ⟨operation, rfl, available⟩
  · cases called with
    | function selected called => rw [notFunction] at selected; contradiction
    | primitive absent computed =>
        rcases runtimeEnabled with ⟨operation, rfl⟩ | ⟨operation, rfl⟩
        · cases operation <;> simp [MemoryBuiltinCorrespondence.Operation.name, Semantics.primitive?] at computed
        · cases operation with | load transient | store transient =>
            cases transient <;> simp [StorageBuiltinCorrespondence.Operation.name, Semantics.primitive?] at computed
    | external absent notPrimitive computed =>
        change RuntimeEnvironmentEffectsSemantics.builtin _ _ _ _ = some _ at computed
        cases runtimeComputed : RuntimeEffectsSemantics.builtin name type sources initial.external.runtime with
        | none =>
            simp [RuntimeEnvironmentEffectsSemantics.builtin, runtimeComputed,
              environment_unsupported runtimeEnabled] at computed
        | some output =>
            rcases output with ⟨runtimeResult, runtimeState⟩
            simp only [RuntimeEnvironmentEffectsSemantics.builtin, runtimeComputed, Option.some.injEq,
              Prod.mk.injEq] at computed
            rcases computed with ⟨rfl, rfl⟩
            intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
            have call : Semantics.EvalCall functions RuntimeEffectsSemantics.effects name type sources
                (sourceRuntime initial) runtimeResult {sourceRuntime initial with external := runtimeState} :=
              .external absent notPrimitive runtimeComputed
            obtain ⟨target, finalStore, resultRelated, evaluated, finalState, installedFinal, retained⟩ :=
              RuntimeEffectsCorrespondence.external_preserves layout baseline slots memoryMember worldMember
                addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
                runtimeEnabled notFunction call typeCompiled compiled related packed runtime (runtime_related state) installed
            exact ⟨target, finalStore, resultRelated, evaluated, runtime_updated passive state finalState,
              installedFinal, retained⟩
  · cases called with
    | function selected called => rw [notFunction] at selected; contradiction
    | primitive absent computed =>
        cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
        all_goals simp [EnvironmentSemantics.Operation.name, EnvironmentSemantics.Direct.name,
          EnvironmentSemantics.AmbientWord.name, Semantics.primitive?] at computed
    | external absent notPrimitive computed =>
        intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
        obtain ⟨computedResult, target, finalStore, meaning, resultRelated, evaluated, observations, retained⟩ :=
          EnvironmentBuiltinCorrespondence.preserves operation compiled related runtime available
            (observations_related state) packed type
        have combined : RuntimeEnvironmentEffectsSemantics.builtin operation.name type sources initial.external =
            some (computedResult, initial.external) := by
          simp only [RuntimeEnvironmentEffectsSemantics.builtin, runtime_unsupported, meaning, Option.map_some]
        have same := Option.some.inj (computed.symm.trans combined)
        cases same
        have closures : ClosuresPreserved argumentStore finalStore := by
          intro location parameter result body environment found
          exact (retained.read location (List.getElem?_eq_some_iff.mp found).1).trans found
        exact ⟨target, finalStore, resultRelated, evaluated,
          state.cutoff_effect (.ofRetains retained)
            (by rw [prefixRead_retained state.external.1 retained]; exact state.external.2.2),
          installed.preserved closures, closures⟩

/-- Each observed value is checked in the actual post-initialization store.
The cutoff and the unchanged baseline come from that same store. -/
theorem initial_state {memory : Nat} {locations : StorageBuiltinCorrespondence.Locations}
    {state : RuntimeEnvironmentEffectsSemantics.State} {store : Core.Store} {slots : List EffectSlot}
    (memoryRelated : MemoryCorrespondence.StateRel memory locations.memorySize state.runtime.memory store)
    (storageRelated : StorageBuiltinCorrespondence.StateRel locations state.runtime.storage store)
    (distinct : (memory :: locations.all).Nodup)
    (observations : EnvironmentBuiltinCorrespondence.StateRel slots state.environment store) :
    StateRel (model (RuntimeEffectsCorrespondence.initialLayout memoryRelated storageRelated distinct)
      (prefixRead store.length store) slots) [] ⟨[], state⟩ store := by
  apply StateRel.cutoff_initial
  refine ⟨(RuntimeEffectsCorrespondence.initial_state memoryRelated storageRelated distinct).external.2.2, ?_⟩
  intro slot member value observed
  have found := observations slot member value observed
  simp only [prefixRead, (List.getElem?_eq_some_iff.mp found).1, ↓reduceIte, found]

/-- Concrete leaves discharge the external-call boundary before the common
recursive simulation reaches the compiler's actual assembled expression. -/
theorem assemble_program (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (passive : Passive layout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    {functions : List Function} {function : Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (eligible : ExecutableProgram (supported slots) functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State RuntimeEnvironmentEffectsSemantics.State}
    {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions RuntimeEnvironmentEffectsSemantics.effects
      function sources initial sourceResult final)
    {world : World} {runtimeValues caller : Core.Environment} {store : Core.Store}
    (runtimeLength : runtimeValues.length = runtime.length)
    (covered : ScopeCoverage [] runtime)
    (runtimeRelated : EffectEnvironmentRel slots runtime Core.Renaming.id
      (runtimeValues ++ bundleValues targets :: caller))
    (separated : EffectSlotsSeparate slots)
    (state : StateRel (model layout baseline slots) world initial store) :
    ∃ extension target finalStore,
      ResultRel own.result sourceResult target ∧
      Core.Evaluates (runtimeValues ++ bundleValues targets :: caller) store allocated target finalStore ∧
      StateRel (model layout baseline slots) (world ++ extension) final finalStore ∧
      ClosuresPreserved store finalStore :=
  assemble_recursive_program_effects accepted selected
    (external_preserves layout baseline slots passive memoryMember worldMember addressMember completeMember staticMember
      memorySizeMember exitMember offsetMember sizeMember) eligible values evaluated
    runtimeLength covered runtimeRelated separated state

theorem environment_unchanged {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : EnvironmentSemantics.State} {result : Semantics.Result Semantics.Value}
    (called : EnvironmentSemantics.builtin name type arguments initial = some (result, final)) :
    final = initial := by
  change ((EnvironmentSemantics.operations.find? (fun operation => operation.name == name)).bind
    fun operation => (EnvironmentSemantics.observe initial operation arguments).bind
      fun result => some (result, initial)) = some (result, final) at called
  simp only [Option.bind_eq_some_iff] at called
  obtain ⟨operation, _, resultValue, _, returned⟩ := called
  exact (congrArg Prod.snd (Option.some.inj returned)).symm

def context (state : RuntimeEnvironmentEffectsSemantics.State) :=
  (RuntimeEffectsProjectionPreservation.context state.runtime, state.environment)

theorem builtin_context {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : RuntimeEnvironmentEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (called : RuntimeEnvironmentEffectsSemantics.builtin name type arguments initial = some (result, final)) :
    context final = context initial := by
  unfold RuntimeEnvironmentEffectsSemantics.builtin at called
  split at called
  · rename_i runtimeResult runtimeState computed
    cases Option.some.inj called
    exact congrArg (fun value => (value, initial.environment))
      (RuntimeEffectsProjectionPreservation.builtin_context computed)
  · obtain ⟨⟨environmentResult, environmentState⟩, computed, returned⟩ := Option.map_eq_some_iff.mp called
    have same := environment_unchanged computed
    cases returned
    simp only [context, same]

theorem context_preserves :
    EffectProjectionPreservation.Preserves RuntimeEnvironmentEffectsSemantics.effects context where
  builtin := builtin_context
  assembly := False.elim
  revert := False.elim

theorem function_context {functions : List Function} {function : Function}
    {arguments : List Semantics.Value}
    {initial final : Semantics.State RuntimeEnvironmentEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions RuntimeEnvironmentEffectsSemantics.effects
      function arguments initial result final) :
    context final.external = context initial.external :=
  EffectProjectionPreservation.function_preserves context_preserves evaluated

end Solcore.Frontend.RustHull.RuntimeEnvironmentEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeEnvironmentEffectsFrameCorrespondence
/-! Interleaved memory, storage and environment observations reach actual frame compilation,
installed closure calls and snapshots of the final independent source state. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeEnvironmentEffectsFrameCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence RuntimeEnvironmentEffectsCorrespondence

abbrev slotTypes := MemoryFrameCorrespondence.slotTypes
abbrev PassiveCell := RuntimeEffectsFrameCorrespondence.PassiveCell
abbrev passiveSnapshotNames := RuntimeEffectsFrameCorrespondence.passiveSnapshotNames
abbrev cell_observed := @RuntimeEffectsFrameCorrespondence.cell_observed
abbrev snapshotValues := RuntimeEffectsFrameCorrespondence.snapshotValues
abbrev initialLayout := @RuntimeEffectsCorrespondence.initialLayout

theorem passive_observed {layout : Layout} {slots : List EffectSlot} {initial final : Core.Store}
    {world : World} {source : Semantics.State RuntimeEnvironmentEffectsSemantics.State}
    {cells : AccountRuntime.References} {environment : Core.Environment}
    (references : AccountRuntime.frameReferences (slotTypes slots) = .ok cells)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id environment)
    (related : StateRel (model layout (prefixRead layout.boundary initial) slots) world source final)
    {name : String} {value : Core.Value} (observed : PassiveCell layout slots initial name value) :
    FrameCellObserved cells environment final name value :=
  RuntimeEffectsFrameCorrespondence.passive_observed references runtime (runtime_related related) observed

/-- A frame installed earlier retains its captured environment. The body and
completion wrapper observe the final source world, including storage writes
and static-write termination, through the compiler's actual frame references. -/
theorem compileFrame_call_preserves_observed {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {memoryLocation : Nat} {locations : StorageBuiltinCorrespondence.Locations}
    {initial : RuntimeEnvironmentEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, memoryLocation⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, locations.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (memoryInitial : MemoryCorrespondence.StateRel memoryLocation locations.memorySize initial.runtime.memory store)
    (storageInitial : StorageBuiltinCorrespondence.StateRel locations initial.runtime.storage store)
    (distinct : (memoryLocation :: locations.all).Nodup)
    (observationsInitial : EnvironmentBuiltinCorrespondence.StateRel slots initial.environment store)
    (passive : Passive (initialLayout memoryInitial storageInitial distinct) slots)
    {final : Semantics.State RuntimeEnvironmentEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEnvironmentEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell (initialLayout memoryInitial storageInitial distinct) slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues snapshot final.external.runtime accounts)
          (StorageCorrespondence.get accounts final.external.runtime.storage.address final.external.runtime.storage.complete)) finalStore ∧
      StateRel (model (initialLayout memoryInitial storageInitial distinct) (prefixRead store.length store) slots)
        extension final finalStore ∧
      finalStore.read? locations.world = some (StorageCorrespondence.world accounts) := by
  obtain ⟨own, body, cells, assembled, references, rfl⟩ := compileFrame_components accepted
  have selected := MemoryFrameCorrespondence.frame_selected accepted
  obtain ⟨signatures, codes, selectedFunction, selectedCode, index, _, sourceSelected,
    signatureCompiled, _, _, _, _, _⟩ := assemble_selection assembled
  have sameFunction := Option.some.inj (sourceSelected.symm.trans selected)
  subst selectedFunction
  obtain ⟨parameters, resultType⟩ := MemoryFrameCorrespondence.frame_signature signatureCompiled
  have argumentValues : ValuesRel own.parameters [] [] := by rw [parameters]; exact .nil
  obtain ⟨extension, status, bodyStore, related, executed, state, _⟩ :=
    assemble_program (initialLayout memoryInitial storageInitial distinct) (prefixRead store.length store) slots passive
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      assembled selected eligible argumentValues evaluated
      (runtimeValues := values.reverse) (caller := bundleValues values :: captured)
      (by simpa [AccountRuntime.frameScope, slotTypes, MemoryFrameCorrespondence.slotTypes] using length)
      (MemoryFrameCorrespondence.frame_coverage _) runtime separated
      (initial_state memoryInitial storageInitial distinct observationsInitial)
  have finalStorage := RuntimeEffectsCorrespondence.storage_related (runtime_related state)
  obtain ⟨accounts, sourceWorld, worldRead⟩ := finalStorage.world
  have finalWorld := cell_observed references runtime worldMember worldRead
  have finalAddress := cell_observed references runtime addressMember finalStorage.address
  have finalComplete := cell_observed references runtime completeMember finalStorage.complete
  have finalSnapshot : ∀ name ∈ frameSnapshotNames,
      FrameCellObserved cells (values.reverse ++ .unit :: bundleValues values :: captured)
        bodyStore name (snapshotValues snapshot final.external.runtime accounts name) := by
    intro name member
    simp [frameSnapshotNames] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cell_observed references runtime exitMember finalStorage.exit
    · exact cell_observed references runtime offsetMember finalStorage.returnOffset
    · exact cell_observed references runtime sizeMember finalStorage.returnSize
    · exact cell_observed references runtime memoryMember (RuntimeEffectsCorrespondence.memory_related (runtime_related state)).memory
    · exact passive_observed references runtime state (snapshotObserved "logs" (by decide))
    · exact passive_observed references runtime state (snapshotObserved "logSize" (by decide))
    · exact passive_observed references runtime state (snapshotObserved "balances" (by decide))
    · exact finalWorld
  have completed := frameCompletion_evaluates executed accounts final.external.runtime.storage.address final.external.runtime.storage.complete
    finalWorld finalAddress finalComplete finalSnapshot
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.getStore_extension accounts
    final.external.runtime.storage.address final.external.runtime.storage.complete
    (status :: (values.reverse ++ .unit :: bundleValues values :: captured)) bodyStore
  refine ⟨extension, status, accounts, _, sourceWorld, by simpa only [resultType] using related,
    frameUnpack_call_evaluates (by simpa only [slotTypes, MemoryFrameCorrespondence.slotTypes, List.length_map] using length)
      closureRelated resolved supplied completed, ?_, ?_⟩
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    simpa only [List.nil_append] using state.appendCore suffix
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    exact ((StoreRetains.append bodyStore suffix).read locations.world
      (List.getElem?_eq_some_iff.mp worldRead).1).trans worldRead

theorem compileFrame_call_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {memoryLocation : Nat} {locations : StorageBuiltinCorrespondence.Locations}
    {initial : RuntimeEnvironmentEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, memoryLocation⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, locations.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (memoryInitial : MemoryCorrespondence.StateRel memoryLocation locations.memorySize initial.runtime.memory store)
    (storageInitial : StorageBuiltinCorrespondence.StateRel locations initial.runtime.storage store)
    (distinct : (memoryLocation :: locations.all).Nodup)
    (observationsInitial : EnvironmentBuiltinCorrespondence.StateRel slots initial.environment store)
    (passive : Passive (initialLayout memoryInitial storageInitial distinct) slots)
    {final : Semantics.State RuntimeEnvironmentEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEnvironmentEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell (initialLayout memoryInitial storageInitial distinct) slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues snapshot final.external.runtime accounts)
          (StorageCorrespondence.get accounts final.external.runtime.storage.address final.external.runtime.storage.complete)) finalStore ∧
      StateRel (model (initialLayout memoryInitial storageInitial distinct) (prefixRead store.length store) slots)
        extension final finalStore := by
  obtain ⟨extension, status, accounts, finalStore, represented, related, executed, state, _⟩ :=
    compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length runtime separated
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      memoryInitial storageInitial distinct observationsInitial passive evaluated snapshot snapshotObserved
  exact ⟨extension, status, accounts, finalStore, represented, related, executed, state⟩

/-- Direct evaluation of freshly compiled frame code is a special case of the
same theorem for captured calls. -/
theorem compileFrame_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {memoryLocation : Nat} {locations : StorageBuiltinCorrespondence.Locations}
    {initial : RuntimeEnvironmentEffectsSemantics.State}
    {initialStore store : Core.Store} {values environment : Core.Environment} {argument : Core.Expr}
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: environment))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, memoryLocation⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, locations.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (memoryInitial : MemoryCorrespondence.StateRel memoryLocation locations.memorySize initial.runtime.memory store)
    (storageInitial : StorageBuiltinCorrespondence.StateRel locations initial.runtime.storage store)
    (distinct : (memoryLocation :: locations.all).Nodup)
    (observationsInitial : EnvironmentBuiltinCorrespondence.StateRel slots initial.environment store)
    (passive : Passive (initialLayout memoryInitial storageInitial distinct) slots)
    {final : Semantics.State RuntimeEnvironmentEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEnvironmentEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell (initialLayout memoryInitial storageInitial distinct) slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment initialStore (.apply compiled argument)
        (frameCompletionValue status (snapshotValues snapshot final.external.runtime accounts)
          (StorageCorrespondence.get accounts final.external.runtime.storage.address final.external.runtime.storage.complete)) finalStore ∧
      StateRel (model (initialLayout memoryInitial storageInitial distinct) (prefixRead store.length store) slots)
        extension final finalStore := by
  obtain ⟨own, body, cells, _, _, rfl⟩ := compileFrame_components accepted
  exact compileFrame_call_preserves accepted eligible (CapturedClosure.lambda _ _ _ environment)
    Core.Evaluates.lambda supplied length runtime separated memoryMember worldMember addressMember completeMember
    staticMember memorySizeMember exitMember offsetMember sizeMember memoryInitial storageInitial distinct observationsInitial passive
    evaluated snapshot snapshotObserved

end Solcore.Frontend.RustHull.RuntimeEnvironmentEffectsFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractEnvironmentCorrespondence
/-! Environment observations join memory and storage through the same actual
frame completion and account finalization code. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractEnvironmentCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence

def supported (name : String) : Prop := RuntimeEffectsCorrespondence.supported name ∨
  ∃ operation : EnvironmentSemantics.Operation, operation.name = name ∧
    ∀ input ∈ EnvironmentBuiltinCorrespondence.inputs operation, input ∈ Effects.slots

theorem supported_actual {slots : List EffectSlot}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots) :
    RuntimeEnvironmentEffectsCorrespondence.supported slots = supported := by
  funext name
  apply propext
  constructor
  · rintro (runtime | ⟨operation, named, available⟩)
    · exact .inl runtime
    · refine .inr ⟨operation, named, ?_⟩
      intro input member
      obtain ⟨location, present⟩ := available input.1 input.2 member
      rw [← signature]
      exact List.mem_map.mpr ⟨⟨input.1, input.2, location⟩, present, rfl⟩
  · rintro (runtime | ⟨operation, named, available⟩)
    · exact .inl runtime
    · refine .inr ⟨operation, named, ?_⟩
      intro inputName inputType member
      have present := available (inputName, inputType) member
      rw [← signature] at present
      obtain ⟨slot, slotMember, equal⟩ := List.mem_map.mp present
      obtain ⟨nameEqual, typeEqual⟩ := Prod.mk.inj equal
      exact ⟨slot.location, by simpa only [← nameEqual, ← typeEqual] using slotMember⟩

theorem frameCall_message_evaluates {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (RuntimeEffectsFrameCorrespondence.slotTypes slots) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram (RuntimeEnvironmentEffectsCorrespondence.supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {memoryLocation : Nat} {locations : StorageBuiltinCorrespondence.Locations}
    {initial : RuntimeEnvironmentEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument target deploying : Code} {depth : Nat}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before (function depth) closure initialStore)
    (supplied : Core.Evaluates environment initialStore (argument depth) (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeEffectsFrameCorrespondence.slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, memoryLocation⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, locations.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, locations.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, locations.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ slots)
    (memoryInitial : MemoryCorrespondence.StateRel memoryLocation locations.memorySize initial.runtime.memory store)
    (storageInitial : StorageBuiltinCorrespondence.StateRel locations initial.runtime.storage store)
    (distinct : (memoryLocation :: locations.all).Nodup)
    (observationsInitial : EnvironmentBuiltinCorrespondence.StateRel slots initial.environment store)
    (passive : RuntimeEnvironmentEffectsCorrespondence.Passive
      (RuntimeEffectsCorrespondence.initialLayout memoryInitial storageInitial distinct) slots)
    {final : Semantics.State RuntimeEnvironmentEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeEnvironmentEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (address : Core.Word) (balances : StorageSemantics.Words)
    (snapshotObserved : ∀ name ∈ RuntimeEffectsFrameCorrespondence.passiveSnapshotNames,
      RuntimeEffectsFrameCorrespondence.PassiveCell
        (RuntimeEffectsCorrespondence.initialLayout memoryInitial storageInitial distinct) slots store name (passiveValues balances name))
    {balancesLocation : Nat}
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type locations.world))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false))
    (balancesFound : store.read? balancesLocation = some (Core.WordMapping.encode balances))
    (balancesOutside : balancesLocation ∉ RuntimeEffectsCorrespondence.mutable
      (RuntimeEffectsCorrespondence.initialLayout memoryInitial storageInitial distinct)) :
    ∃ value finalStore, Core.Evaluates environment before
      (bind (apply function argument) (fun framed => AccountRuntime.completeMessage shared images target deploying framed) depth)
      value finalStore ∧ MessageRel result final.external.runtime address balances value := by
  obtain ⟨extension, status, accounts, bodyStore, represented, statusRelated, executed, related, worldFinal⟩ :=
    RuntimeEnvironmentEffectsFrameCorrespondence.compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length
      runtime separated memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      memoryInitial storageInitial distinct observationsInitial passive evaluated (passiveValues balances) snapshotObserved
  have balancesBound := (List.getElem?_eq_some_iff.mp balancesFound).1
  have balancesFinal : bodyStore.read? balancesLocation = some (Core.WordMapping.encode balances) := by
    have retained := (RuntimeEnvironmentEffectsCorrespondence.runtime_related related).external.2.2.other balancesLocation balancesOutside
    simpa only [prefixRead, RuntimeEffectsCorrespondence.initialLayout, balancesBound, ↓reduceIte, balancesFound] using retained
  let frameResult := frameCompletionValue status (snapshotValues final.external.runtime accounts balances)
    (StorageCorrespondence.get accounts final.external.runtime.storage.address final.external.runtime.storage.complete)
  obtain ⟨finalStore, completed⟩ := message_evaluates result final.external.runtime accounts address balances
    statusRelated (worldReference.prepend [frameResult]) (balancesReference.prepend [frameResult])
    (targetValue.prepend [frameResult]) (deployingValue.prepend [frameResult])
    (CodeValue.bound depth environment frameResult) worldFinal balancesFinal
  exact ⟨_, finalStore, .letE executed completed, accounts, represented, rfl⟩

end Solcore.Frontend.RustHull.ContractEnvironmentCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeLogEffectsCorrespondence
/-! Concrete event-stream cells compose with the existing runtime model.
The runtime component sees the current log values as its unchanged baseline. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.RustHull.RuntimeLogEffectsCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence

structure Layout extends RuntimeEffectsCorrespondence.Layout where
  logs : Nat
  logSize : Nat
  jointDistinct : (logs :: logSize :: memory :: storage.all).Nodup
  logsBelow : logs < boundary
  logSizeBelow : logSize < boundary

def logLocations (layout : Layout) : LogBuiltinCorrespondence.Locations :=
  ⟨⟨layout.memory, layout.storage.memorySize, layout.logs, layout.logSize⟩,
    layout.storage.address, layout.storage.isStatic, layout.storage.exit,
    layout.storage.returnOffset, layout.storage.returnSize⟩

def mutable (layout : Layout) : List Nat := layout.logs :: layout.logSize :: RuntimeEffectsCorrespondence.mutable layout.toLayout

def patched (layout : Layout) (baseline : Nat → Option Core.Value) (state : RuntimeLogEffectsSemantics.State)
    (location : Nat) : Option Core.Value :=
  if location = layout.logs then some (Core.WordMapping.encode state.words)
  else if location = layout.logSize then some (.word state.cursor)
  else baseline location

def Resources (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot)
    (state : RuntimeLogEffectsSemantics.State) (read : Nat → Option Core.Value) : Prop :=
  RuntimeEnvironmentEffectsCorrespondence.Resources layout.toLayout (patched layout baseline state) slots state.runtime read ∧
  read layout.logs = some (Core.WordMapping.encode state.words) ∧ read layout.logSize = some (.word state.cursor)

def model (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot) : StateModel RuntimeLogEffectsSemantics.State :=
  StateModel.cutoff layout.boundary (Resources layout baseline slots)

def sourceRuntime (state : Semantics.State RuntimeLogEffectsSemantics.State) : Semantics.State RuntimeEnvironmentEffectsSemantics.State :=
  ⟨state.heap, state.external.runtime⟩

def Passive (layout : Layout) (slots : List EffectSlot) : Prop :=
  ∀ slot ∈ slots, ∀ state value,
    EnvironmentBuiltinCorrespondence.observation state slot.name slot.type = some value → slot.location ∉ mutable layout

theorem passive_runtime {layout : Layout} {slots : List EffectSlot} (passive : Passive layout slots) :
    RuntimeEnvironmentEffectsCorrespondence.Passive layout.toLayout slots := by
  intro slot member state value observed inside
  exact passive slot member state value observed (.tail _ (.tail _ inside))

theorem runtime_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {world : World} {state : Semantics.State RuntimeLogEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots) world state store) :
    StateRel (RuntimeEnvironmentEffectsCorrespondence.model layout.toLayout (patched layout baseline state.external) slots)
      world (sourceRuntime state) store :=
  ⟨related.toHeapRel, related.external.1, related.external.2.1, related.external.2.2.1⟩

theorem other_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {world : World} {state : Semantics.State RuntimeLogEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots) world state store)
    {location : Nat} (outside : location ∉ mutable layout) :
    prefixRead layout.boundary store location = baseline location := by
  have logs : location ≠ layout.logs := fun same => outside (by simp [mutable, same])
  have size : location ≠ layout.logSize := fun same => outside (by simp [mutable, same])
  have runtime : location ∉ RuntimeEffectsCorrespondence.mutable layout.toLayout := fun member => outside (.tail _ (.tail _ member))
  simpa only [patched, logs, size, ↓reduceIte] using related.external.2.2.1.1.other location runtime

theorem logs_distinct (layout : Layout) : (logLocations layout).all.Nodup := by
  have joint := layout.jointDistinct
  simp only [StorageBuiltinCorrespondence.Locations.all, List.nodup_cons, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false, not_or] at joint
  simp only [logLocations, LogBuiltinCorrespondence.Locations.all, LogsCorrespondence.Locations.all,
    List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
  simp_all [ne_comm]

theorem logs_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {world : World} {state : Semantics.State RuntimeLogEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots) world state store) :
    LogBuiltinCorrespondence.StateRel (logLocations layout) (RuntimeLogEffectsSemantics.logsState state.external) store := by
  have runtime := RuntimeEnvironmentEffectsCorrespondence.runtime_related (runtime_related related)
  have memory := RuntimeEffectsCorrespondence.memory_related runtime
  have storage := RuntimeEffectsCorrespondence.storage_related runtime
  have distinct := logs_distinct layout
  refine ⟨⟨(List.nodup_append.mp distinct).1, memory.memory, memory.size, ?_, ?_⟩,
    storage.address, storage.isStatic, storage.exit, storage.returnOffset, storage.returnSize, distinct⟩
  · simpa only [prefixRead, layout.logsBelow, ↓reduceIte, logLocations, RuntimeLogEffectsSemantics.logsState] using related.external.2.2.2.1
  · simpa only [prefixRead, layout.logSizeBelow, ↓reduceIte, logLocations, RuntimeLogEffectsSemantics.logsState] using related.external.2.2.2.2

theorem logs_outside (layout : Layout) : layout.logs ∉ RuntimeEffectsCorrespondence.mutable layout.toLayout ∧
    layout.logSize ∉ RuntimeEffectsCorrespondence.mutable layout.toLayout := by
  have joint := layout.jointDistinct
  simp only [StorageBuiltinCorrespondence.Locations.all, List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at joint
  simp only [RuntimeEffectsCorrespondence.mutable, StorageBuiltinCorrespondence.Locations.mutable,
    List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
  simp_all [ne_comm]

theorem runtime_updated {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {world : World} {state : Semantics.State RuntimeLogEffectsSemantics.State} {store : Core.Store}
    {runtime : RuntimeEnvironmentEffectsSemantics.State}
    (related : StateRel (RuntimeEnvironmentEffectsCorrespondence.model layout.toLayout
      (patched layout baseline state.external) slots) world {sourceRuntime state with external := runtime} store) :
    StateRel (model layout baseline slots) world
      {state with external := {state.external with runtime := runtime}} store := by
  have logs := related.external.2.2.1.other layout.logs (logs_outside layout).1
  have size := related.external.2.2.1.other layout.logSize (logs_outside layout).2
  have different : layout.logSize ≠ layout.logs := by
    have joint := (List.nodup_cons.mp layout.jointDistinct).1
    intro same
    exact joint (by simp [same])
  refine ⟨related.toHeapRel, related.external.1, related.external.2.1, related.external.2.2, ?_, ?_⟩
  · simpa only [patched, RuntimeLogEffectsSemantics.withLogs, ↓reduceIte] using logs
  · simpa only [patched, different, ↓reduceIte] using size

theorem log_mutable_subset (layout : Layout) {location : Nat}
    (member : location ∈ (logLocations layout).mutable) : location ∈ mutable layout := by
  simp only [logLocations, LogBuiltinCorrespondence.Locations.mutable, LogsCorrespondence.Locations.all,
    List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
  simp only [mutable, RuntimeEffectsCorrespondence.mutable, StorageBuiltinCorrespondence.Locations.mutable,
    List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
  rcases member with (same | same | same | same) | same | same | same <;> simp [same]

theorem mutable_below (layout : Layout) {location : Nat} (member : location ∈ mutable layout) :
    location < layout.boundary := by
  rcases List.mem_cons.mp member with rfl | member
  · exact layout.logsBelow
  rcases List.mem_cons.mp member with rfl | member
  · exact layout.logSizeBelow
  apply layout.below
  simp only [RuntimeEffectsCorrespondence.mutable, StorageBuiltinCorrespondence.Locations.mutable,
    List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
  rcases member with (same | same) | same | same | same | same <;>
    simp [StorageBuiltinCorrespondence.Locations.all, same]

theorem frame_above {layout : Layout} {initial final : Core.Store}
    (frame : LogBuiltinCorrespondence.Frame (logLocations layout) initial final) :
    StoreRetainsFrom layout.boundary initial final := by
  refine ⟨frame.length_le, ?_⟩
  intro location above below
  have outside : location ∉ (logLocations layout).mutable := fun member =>
    Nat.not_lt_of_ge above (mutable_below layout (log_mutable_subset layout member))
  exact (frame.preserved location _ outside (List.getElem?_eq_getElem below)).trans
    (List.getElem?_eq_getElem below).symm

theorem closures_preserved {locations : LogBuiltinCorrespondence.Locations} {before : LogsSemantics.State}
    {initial final : Core.Store} (related : LogBuiltinCorrespondence.StateRel locations before initial)
    (frame : LogBuiltinCorrespondence.Frame locations initial final) : ClosuresPreserved initial final := by
  intro location parameter result body environment found
  apply frame.preserved location _ _ found
  intro member
  simp only [LogBuiltinCorrespondence.Locations.mutable, LogsCorrespondence.Locations.all,
    List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
  rcases member with (same | same | same | same) | same | same | same
  · subst location
    have equal := Option.some.inj (related.logs.memory.symm.trans found)
    cases entries : before.memory.words <;> simp only [entries, Core.WordMapping.encode] at equal <;> cases equal
  · subst location; cases Option.some.inj (related.logs.memorySize.symm.trans found)
  · subst location
    have equal := Option.some.inj (related.logs.logs.symm.trans found)
    cases entries : before.words <;> simp only [entries, Core.WordMapping.encode] at equal <;> cases equal
  · subst location; cases Option.some.inj (related.logs.logSize.symm.trans found)
  · subst location; cases Option.some.inj (related.exit.symm.trans found)
  · subst location; cases Option.some.inj (related.returnOffset.symm.trans found)
  · subst location; cases Option.some.inj (related.returnSize.symm.trans found)

theorem logs_updated {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {world : World} {state : Semantics.State RuntimeLogEffectsSemantics.State} {initial final : Core.Store}
    {logs : LogsSemantics.State}
    (passive : Passive layout slots)
    (before : StateRel (model layout baseline slots) world state initial)
    (after : LogBuiltinCorrespondence.StateRel (logLocations layout) logs final)
    (frame : LogBuiltinCorrespondence.Frame (logLocations layout) initial final) :
    StateRel (model layout baseline slots) world
      {state with external := RuntimeLogEffectsSemantics.withLogs state.external logs} final := by
  have runtime := RuntimeEnvironmentEffectsCorrespondence.runtime_related (runtime_related before)
  have storage := RuntimeEffectsCorrespondence.storage_related runtime
  have finalRead {location : Nat} {value : Core.Value} (below : location < layout.boundary)
      (found : final.read? location = some value) : prefixRead layout.boundary final location = some value := by
    simpa only [prefixRead, below, ↓reduceIte] using found
  have sharedOutside (location : Nat) (member : location ∈ [layout.storage.world, layout.storage.complete]) :
      location ∉ (logLocations layout).mutable := by
    have joint := layout.jointDistinct
    simp only [StorageBuiltinCorrespondence.Locations.all, List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at joint
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals simp only [logLocations, LogBuiltinCorrespondence.Locations.mutable, LogsCorrespondence.Locations.all,
      List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
    all_goals simp_all [ne_comm]
  apply before.cutoff_effect (frame_above frame)
  refine ⟨⟨?_, ?_⟩, finalRead layout.logsBelow after.logs.logs, finalRead layout.logSizeBelow after.logs.logSize⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact finalRead (layout.below _ (by simp)) after.logs.memory
    · exact finalRead (layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all])) after.logs.memorySize
    · obtain ⟨accounts, same, found⟩ := storage.world
      exact ⟨accounts, same, finalRead (layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all]))
        (frame.preserved _ _ (sharedOutside _ (by simp)) found)⟩
    · exact finalRead (layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all])) after.address
    · exact finalRead (layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all]))
        (frame.preserved _ _ (sharedOutside _ (by simp)) storage.complete)
    · exact finalRead (layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all])) after.isStatic
    · exact finalRead (layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all])) after.exit
    · exact finalRead (layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all])) after.returnOffset
    · exact finalRead (layout.below _ (by simp [StorageBuiltinCorrespondence.Locations.all])) after.returnSize
    · intro location outside
      by_cases atLogs : location = layout.logs
      · subst location
        simpa only [patched, RuntimeLogEffectsSemantics.withLogs, ↓reduceIte] using finalRead layout.logsBelow after.logs.logs
      by_cases atSize : location = layout.logSize
      · subst location
        simpa only [patched, RuntimeLogEffectsSemantics.withLogs, atLogs, ↓reduceIte] using finalRead layout.logSizeBelow after.logs.logSize
      have allOutside : location ∉ mutable layout := by simpa only [mutable, List.mem_cons, not_or] using ⟨atLogs, atSize, outside⟩
      have logOutside := fun member => allOutside (log_mutable_subset layout member)
      rw [show patched layout baseline (RuntimeLogEffectsSemantics.withLogs state.external logs) location = baseline location by simp [patched, atLogs, atSize]]
      rw [← other_related before allOutside]
      by_cases below : location < layout.boundary
      · have bound := Nat.lt_of_lt_of_le below before.external.1
        simpa only [prefixRead, below, ↓reduceIte, Core.Store.read?] using
          (frame.preserved location _ logOutside (List.getElem?_eq_getElem bound)).trans (List.getElem?_eq_getElem bound).symm
      · simp only [prefixRead, below, ↓reduceIte]
  · intro slot member value observed
    have found := RuntimeEnvironmentEffectsCorrespondence.observations_related (runtime_related before) slot member value observed
    have outside := fun inside => passive slot member _ _ observed (log_mutable_subset layout inside)
    have below : slot.location < layout.boundary := by
      have observedRead := before.external.2.2.1.2 slot member value observed
      unfold prefixRead at observedRead
      split at observedRead
      · assumption
      · contradiction
    exact finalRead below (frame.preserved slot.location _ outside found)

def supported (slots : List EffectSlot) (name : String) : Prop :=
  RuntimeEnvironmentEffectsCorrespondence.supported slots name ∨ ∃ operation : LogsSemantics.Operation, operation.name = name

private theorem primitive_none {slots : List EffectSlot} {name : String}
    (enabled : supported slots name) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = none := by
  rcases enabled with ((memory | storage) | environment) | ⟨operation, rfl⟩
  · obtain ⟨operation, rfl⟩ := memory
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := storage
    cases operation with | load transient | store transient => cases transient <;> rfl
  · obtain ⟨operation, rfl, _⟩ := environment
    cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals rfl
  · cases operation <;> rfl

private theorem runtime_unsupported (operation : LogsSemantics.Operation)
    (type : Ty) (arguments : List Semantics.Value) (state : RuntimeEnvironmentEffectsSemantics.State) :
    RuntimeEnvironmentEffectsSemantics.builtin operation.name type arguments state = none := by
  cases operation <;> rfl

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (passive : Passive layout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots) :
    ExternalCallPreservation (supported slots) (model layout baseline slots) slots RuntimeLogEffectsSemantics.effects := by
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | @runtime finalRuntime computed =>
          have runtimeEnabled : RuntimeEnvironmentEffectsCorrespondence.supported slots name := by
            rcases enabled with runtime | ⟨operation, rfl⟩
            · exact runtime
            · rw [runtime_unsupported] at computed
              contradiction
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          have call : Semantics.EvalCall functions RuntimeEnvironmentEffectsSemantics.effects name type sources
              (sourceRuntime initial) result {sourceRuntime initial with external := finalRuntime} :=
            .external absent notPrimitive computed
          obtain ⟨target, finalStore, resultRelated, evaluated, finalState, installedFinal, retained⟩ :=
            RuntimeEnvironmentEffectsCorrespondence.external_preserves layout.toLayout (patched layout baseline initial.external)
              slots (passive_runtime passive) memoryMember worldMember addressMember completeMember staticMember
              memorySizeMember exitMember offsetMember sizeMember runtimeEnabled notFunction call
              typeCompiled compiled related packed runtime (runtime_related state) installed
          exact ⟨target, finalStore, resultRelated, evaluated, runtime_updated finalState, installedFinal, retained⟩
      | logs computed =>
          cases computed with
          | log operation resultType offset length topics count executed =>
              intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
              obtain ⟨target, finalStore, resultRelated, evaluated, finalState, frame⟩ :=
                LogBuiltinCorrespondence.preserves operation compiled count executed related runtime
                  memoryMember memorySizeMember logsMember logSizeMember addressMember staticMember exitMember offsetMember sizeMember
                  (logs_related state) packed
              have retained : ClosuresPreserved argumentStore finalStore := closures_preserved (logs_related state) frame
              exact ⟨target, finalStore, resultRelated, evaluated, logs_updated passive state finalState frame,
                installed.preserved retained, retained⟩

theorem assemble_program (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (passive : Passive layout slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    {functions : List Function} {function : Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (eligible : ExecutableProgram (supported slots) functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State RuntimeLogEffectsSemantics.State}
    {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions RuntimeLogEffectsSemantics.effects
      function sources initial sourceResult final)
    {world : World} {runtimeValues caller : Core.Environment} {store : Core.Store}
    (runtimeLength : runtimeValues.length = runtime.length)
    (covered : ScopeCoverage [] runtime)
    (runtimeRelated : EffectEnvironmentRel slots runtime Core.Renaming.id
      (runtimeValues ++ bundleValues targets :: caller))
    (separated : EffectSlotsSeparate slots)
    (state : StateRel (model layout baseline slots) world initial store) :
    ∃ extension target finalStore,
      ResultRel own.result sourceResult target ∧
      Core.Evaluates (runtimeValues ++ bundleValues targets :: caller) store allocated target finalStore ∧
      StateRel (model layout baseline slots) (world ++ extension) final finalStore ∧
      ClosuresPreserved store finalStore :=
  assemble_recursive_program_effects accepted selected
    (external_preserves layout baseline slots passive memoryMember worldMember addressMember completeMember staticMember
      memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember) eligible values evaluated
    runtimeLength covered runtimeRelated separated state

end Solcore.Frontend.RustHull.RuntimeLogEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeLogEffectsFrameCorrespondence
/-! Interleaved memory, storage, environment and event operations reach actual frame compilation,
installed closure calls and snapshots of the final independent source state. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeLogEffectsFrameCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence RuntimeLogEffectsCorrespondence

abbrev slotTypes := MemoryFrameCorrespondence.slotTypes
abbrev cell_observed := @RuntimeEffectsFrameCorrespondence.cell_observed

def PassiveCell (layout : Layout) (slots : List EffectSlot) (store : Core.Store)
    (name : String) (value : Core.Value) : Prop :=
  ∃ slot ∈ slots, slot.name = name ∧ slot.location ∉ mutable layout ∧
    slot.location < layout.boundary ∧ store.read? slot.location = some value

def passiveSnapshotNames : List String := ["balances"]

def snapshotValues (values : String → Core.Value) (state : RuntimeLogEffectsSemantics.State)
    (accounts : StorageCorrespondence.Accounts) (name : String) : Core.Value :=
  match name with
  | "memory" => Core.WordMapping.encode state.runtime.runtime.memory.words
  | "world" => StorageCorrespondence.world accounts
  | "exit" => .word state.runtime.runtime.storage.exit
  | "returnOffset" => .word state.runtime.runtime.storage.returnOffset
  | "returnSize" => .word state.runtime.runtime.storage.returnSize
  | "logs" => Core.WordMapping.encode state.words
  | "logSize" => .word state.cursor
  | _ => values name

theorem passive_observed {layout : Layout} {slots : List EffectSlot} {initial final : Core.Store}
    {world : World} {source : Semantics.State RuntimeLogEffectsSemantics.State}
    {cells : AccountRuntime.References} {environment : Core.Environment}
    (references : AccountRuntime.frameReferences (slotTypes slots) = .ok cells)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id environment)
    (related : StateRel (model layout (prefixRead layout.boundary initial) slots) world source final)
    {name : String} {value : Core.Value} (observed : PassiveCell layout slots initial name value) :
    FrameCellObserved cells environment final name value :=
by
  obtain ⟨slot, member, named, outside, below, stored⟩ := observed
  apply FrameCellObserved.of_compilation (type := slot.type) references
    (List.mem_map.mpr ⟨slot, member, by simp only [named]⟩)
  · intro binding index looked
    exact runtime slot member binding index (by simpa only [named] using looked)
  · have retained := other_related related outside
    simpa only [prefixRead, below, ↓reduceIte, stored] using retained

/-- A frame installed earlier retains its captured environment. The body and
completion wrapper observe the final source world, including storage writes
and static-write termination, through the compiler's actual frame references. -/
theorem compileFrame_call_preserves_observed {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout}
    {initial : RuntimeLogEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : Passive layout slots)
    {final : Semantics.State RuntimeLogEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeLogEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell layout slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues snapshot final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots)
        extension final finalStore ∧
      finalStore.read? layout.storage.world = some (StorageCorrespondence.world accounts) := by
  obtain ⟨own, body, cells, assembled, references, rfl⟩ := compileFrame_components accepted
  have selected := MemoryFrameCorrespondence.frame_selected accepted
  obtain ⟨signatures, codes, selectedFunction, selectedCode, index, _, sourceSelected,
    signatureCompiled, _, _, _, _, _⟩ := assemble_selection assembled
  have sameFunction := Option.some.inj (sourceSelected.symm.trans selected)
  subst selectedFunction
  obtain ⟨parameters, resultType⟩ := MemoryFrameCorrespondence.frame_signature signatureCompiled
  have argumentValues : ValuesRel own.parameters [] [] := by rw [parameters]; exact .nil
  obtain ⟨extension, status, bodyStore, related, executed, state, _⟩ :=
    assemble_program layout (prefixRead layout.boundary store) slots passive
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember assembled selected eligible argumentValues evaluated
      (runtimeValues := values.reverse) (caller := bundleValues values :: captured)
      (by simpa [AccountRuntime.frameScope, slotTypes, MemoryFrameCorrespondence.slotTypes] using length)
      (MemoryFrameCorrespondence.frame_coverage _) runtime separated
      initialRelated
  have finalStorage := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related (runtime_related state))
  have finalLogs := logs_related state
  obtain ⟨accounts, sourceWorld, worldRead⟩ := finalStorage.world
  have finalWorld := cell_observed references runtime worldMember worldRead
  have finalAddress := cell_observed references runtime addressMember finalStorage.address
  have finalComplete := cell_observed references runtime completeMember finalStorage.complete
  have finalSnapshot : ∀ name ∈ frameSnapshotNames,
      FrameCellObserved cells (values.reverse ++ .unit :: bundleValues values :: captured)
        bodyStore name (snapshotValues snapshot final.external accounts name) := by
    intro name member
    simp [frameSnapshotNames] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cell_observed references runtime exitMember finalStorage.exit
    · exact cell_observed references runtime offsetMember finalStorage.returnOffset
    · exact cell_observed references runtime sizeMember finalStorage.returnSize
    · exact cell_observed references runtime memoryMember finalLogs.logs.memory
    · exact cell_observed references runtime logsMember finalLogs.logs.logs
    · exact cell_observed references runtime logSizeMember finalLogs.logs.logSize
    · exact passive_observed references runtime state (snapshotObserved "balances" (by decide))
    · exact finalWorld
  have completed := frameCompletion_evaluates executed accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete
    finalWorld finalAddress finalComplete finalSnapshot
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.getStore_extension accounts
    final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete
    (status :: (values.reverse ++ .unit :: bundleValues values :: captured)) bodyStore
  refine ⟨extension, status, accounts, _, sourceWorld, by simpa only [resultType] using related,
    frameUnpack_call_evaluates (by simpa only [slotTypes, MemoryFrameCorrespondence.slotTypes, List.length_map] using length)
      closureRelated resolved supplied completed, ?_, ?_⟩
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    simpa only [List.nil_append] using state.appendCore suffix
  · rw [show bundleValues ([] : List Core.Value) = .unit from rfl, extended]
    exact ((StoreRetains.append bodyStore suffix).read layout.storage.world
      (List.getElem?_eq_some_iff.mp worldRead).1).trans worldRead

theorem compileFrame_call_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout}
    {initial : RuntimeLogEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument : Core.Expr} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before function closure initialStore)
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : Passive layout slots)
    {final : Semantics.State RuntimeLogEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeLogEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell layout slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues snapshot final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots)
        extension final finalStore := by
  obtain ⟨extension, status, accounts, finalStore, represented, related, executed, state, _⟩ :=
    compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length runtime separated
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember initialRelated passive evaluated snapshot snapshotObserved
  exact ⟨extension, status, accounts, finalStore, represented, related, executed, state⟩

/-- Direct evaluation of freshly compiled frame code is a special case of the
same theorem for captured calls. -/
theorem compileFrame_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout}
    {initial : RuntimeLogEffectsSemantics.State}
    {initialStore store : Core.Store} {values environment : Core.Environment} {argument : Core.Expr}
    (supplied : Core.Evaluates environment initialStore argument (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: environment))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : Passive layout slots)
    {final : Semantics.State RuntimeLogEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeLogEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (snapshot : String → Core.Value)
    (snapshotObserved : ∀ name ∈ passiveSnapshotNames,
      PassiveCell layout slots store name (snapshot name)) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment initialStore (.apply compiled argument)
        (frameCompletionValue status (snapshotValues snapshot final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots)
        extension final finalStore := by
  obtain ⟨own, body, cells, _, _, rfl⟩ := compileFrame_components accepted
  exact compileFrame_call_preserves accepted eligible (CapturedClosure.lambda _ _ _ environment)
    Core.Evaluates.lambda supplied length runtime separated memoryMember worldMember addressMember completeMember
    staticMember memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember initialRelated passive
    evaluated snapshot snapshotObserved

end Solcore.Frontend.RustHull.RuntimeLogEffectsFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractLogCorrespondence
/-! Source event snapshots pass through actual account finalization and
message completion together with the memory/storage result. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractLogCorrespondence
open Correspondence ScalarExecution CodeBuilder
abbrev resultValue := ContractRuntimeEffectsCorrespondence.resultValue
abbrev succeeded := ContractRuntimeEffectsCorrespondence.succeeded
abbrev passiveValues := ContractRuntimeEffectsCorrespondence.passiveValues

def supported (name : String) : Prop := ContractEnvironmentCorrespondence.supported name ∨
  ∃ operation : LogsSemantics.Operation, operation.name = name

theorem supported_actual {slots : List EffectSlot}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots) :
    RuntimeLogEffectsCorrespondence.supported slots = supported := by
  funext name
  simp only [RuntimeLogEffectsCorrespondence.supported, supported, ContractEnvironmentCorrespondence.supported_actual signature]

def snapshotValues (state : RuntimeLogEffectsSemantics.State) (accounts : StorageCorrespondence.Accounts)
    (balances : StorageSemantics.Words) : String → Core.Value :=
  RuntimeLogEffectsFrameCorrespondence.snapshotValues (passiveValues balances) state accounts

def messageValue (result : Semantics.Result Semantics.Value) (state : RuntimeLogEffectsSemantics.State)
    (accounts : StorageCorrespondence.Accounts) (target : Core.Word) (balances : StorageSemantics.Words) : Core.Value :=
  let snapshot := snapshotValues state accounts balances
  match StorageCorrespondence.get accounts state.runtime.runtime.storage.address state.runtime.runtime.storage.complete with
  | .error reason => completedMessageValue (.inLeft .unit (.word reason)) false state.runtime.runtime.storage.exit
      snapshot (Core.WordMapping.encode []) accounts target balances
  | .ok (account, _) => completedMessageValue (resultValue result) (succeeded result) state.runtime.runtime.storage.exit
      snapshot (Core.WordMapping.encode account.storage) accounts target balances

def MessageRel (result : Semantics.Result Semantics.Value) (state : RuntimeLogEffectsSemantics.State)
    (target : Core.Word) (balances : StorageSemantics.Words) (value : Core.Value) : Prop :=
  ∃ accounts : StorageCorrespondence.Accounts,
    accounts.map Prod.fst = state.runtime.runtime.storage.world ∧ value = messageValue result state accounts target balances

theorem message_evaluates {depth : Nat} {environment : Core.Environment}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {target deploying framed : Code}
    {worldLocation balancesLocation : Nat} {initial : Core.Store}
    (sourceResult : Semantics.Result Semantics.Value) (state : RuntimeLogEffectsSemantics.State)
    (accounts : StorageCorrespondence.Accounts) (address : Core.Word) (balances : StorageSemantics.Words)
    {status : Core.Value} (statusRelated : ResultRel .unit sourceResult status)
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type worldLocation))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false))
    (framedValue : CodeValue depth environment framed
      (frameCompletionValue status (snapshotValues state accounts balances)
        (StorageCorrespondence.get accounts state.runtime.runtime.storage.address state.runtime.runtime.storage.complete)))
    (worldFound : initial.read? worldLocation = some (StorageCorrespondence.world accounts))
    (balancesFound : initial.read? balancesLocation = some (Core.WordMapping.encode balances)) :
    ∃ final, Core.Evaluates environment initial
      (AccountRuntime.completeMessage shared images target deploying framed depth)
      (messageValue sourceResult state accounts address balances) final := by
  cases got : StorageCorrespondence.get accounts state.runtime.runtime.storage.address state.runtime.runtime.storage.complete with
  | error reason =>
      have framedRelated : CodeValue depth environment framed
          (.pair (.inLeft .unit (.word reason))
            (frameSnapshotValue (snapshotValues state accounts balances) (Core.WordMapping.encode []))) := by
        simpa only [got, frameCompletionValue] using framedValue
      obtain ⟨final, evaluated⟩ := completeMessage_evaluates accounts balances worldReference balancesReference
        targetValue deployingValue framedRelated (MessageStatus.failure (.word reason)) rfl worldFound balancesFound
      exact ⟨final, by simpa only [messageValue, got] using evaluated⟩
  | ok pair =>
      rcases pair with ⟨account, identity⟩
      have framedRelated : CodeValue depth environment framed
          (.pair status (frameSnapshotValue (snapshotValues state accounts balances) (Core.WordMapping.encode account.storage))) := by
        simpa only [got, frameCompletionValue] using framedValue
      cases statusRelated with
      | value related =>
          cases related
          obtain ⟨final, evaluated⟩ := completeMessage_evaluates accounts balances worldReference balancesReference
            targetValue deployingValue framedRelated MessageStatus.success rfl worldFound balancesFound
          exact ⟨final, by simpa only [messageValue, got, resultValue, ContractMemoryCorrespondence.resultValue, succeeded, ContractRuntimeEffectsCorrespondence.succeeded] using evaluated⟩
      | language reason =>
          obtain ⟨final, evaluated⟩ := completeMessage_evaluates accounts balances worldReference balancesReference
            targetValue deployingValue framedRelated (MessageStatus.failure (.word reason)) rfl worldFound balancesFound
          exact ⟨final, by simpa only [messageValue, got, resultValue, ContractMemoryCorrespondence.resultValue, succeeded, ContractRuntimeEffectsCorrespondence.succeeded] using evaluated⟩

theorem frameCall_message_evaluates {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (RuntimeLogEffectsFrameCorrespondence.slotTypes slots) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram (RuntimeLogEffectsCorrespondence.supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : RuntimeLogEffectsCorrespondence.Layout}
    {initial : RuntimeLogEffectsSemantics.State}
    {before initialStore store : Core.Store} {values environment captured : Core.Environment}
    {function argument target deploying : Code} {depth : Nat}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {closure : Core.Value}
    (closureRelated : CapturedClosure compiled captured closure)
    (resolved : Core.Evaluates environment before (function depth) closure initialStore)
    (supplied : Core.Evaluates environment initialStore (argument depth) (bundleValues values) store)
    (length : values.length = slots.length)
    (runtime : EffectEnvironmentRel slots (AccountRuntime.frameScope (RuntimeLogEffectsFrameCorrespondence.slotTypes slots)) Core.Renaming.id
      (values.reverse ++ .unit :: bundleValues values :: captured))
    (separated : EffectSlotsSeparate slots)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (addressMember : ⟨"address", .word, layout.storage.address⟩ ∈ slots)
    (completeMember : ⟨"worldComplete", .bool, layout.storage.complete⟩ ∈ slots)
    (staticMember : ⟨"isStatic", .bool, layout.storage.isStatic⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots)
    (initialRelated : StateRel (RuntimeLogEffectsCorrespondence.model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout slots)
    {final : Semantics.State RuntimeLogEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeLogEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (address : Core.Word) (balances : StorageSemantics.Words)
    (snapshotObserved : ∀ name ∈ RuntimeLogEffectsFrameCorrespondence.passiveSnapshotNames,
      RuntimeLogEffectsFrameCorrespondence.PassiveCell layout slots store name (passiveValues balances name))
    {balancesLocation : Nat}
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type layout.storage.world))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false))
    (balancesFound : store.read? balancesLocation = some (Core.WordMapping.encode balances))
    (balancesBound : balancesLocation < layout.boundary)
    (balancesOutside : balancesLocation ∉ RuntimeLogEffectsCorrespondence.mutable layout) :
    ∃ value finalStore, Core.Evaluates environment before
      (bind (apply function argument) (fun framed => AccountRuntime.completeMessage shared images target deploying framed) depth)
      value finalStore ∧ MessageRel result final.external address balances value := by
  obtain ⟨extension, status, accounts, bodyStore, represented, statusRelated, executed, related, worldFinal⟩ :=
    RuntimeLogEffectsFrameCorrespondence.compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length
      runtime separated memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember initialRelated passive evaluated (passiveValues balances) snapshotObserved
  have balancesFinal : bodyStore.read? balancesLocation = some (Core.WordMapping.encode balances) := by
    have retained := RuntimeLogEffectsCorrespondence.other_related related balancesOutside
    simpa only [prefixRead, balancesBound, ↓reduceIte, balancesFound] using retained
  let frameResult := frameCompletionValue status (snapshotValues final.external accounts balances)
    (StorageCorrespondence.get accounts final.external.runtime.runtime.storage.address final.external.runtime.runtime.storage.complete)
  obtain ⟨finalStore, completed⟩ := message_evaluates result final.external accounts address balances
    statusRelated (worldReference.prepend [frameResult]) (balancesReference.prepend [frameResult])
    (targetValue.prepend [frameResult]) (deployingValue.prepend [frameResult])
    (CodeValue.bound depth environment frameResult) worldFinal balancesFinal
  exact ⟨_, finalStore, .letE executed completed, accounts, represented, rfl⟩

end Solcore.Frontend.RustHull.ContractLogCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeInitializedEffects
/-! The actual allocator's named cells establish the concrete memory and
storage state relation, including every required disjoint location. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeInitializedEffects
open Correspondence ScalarExecution

def expected (accounts : StorageCorrespondence.Accounts) (state : RuntimeEffectsSemantics.State) :
    String → Option Core.Value
  | "memory" => some (Core.WordMapping.encode state.memory.words)
  | "memorySize" => some (.word state.memory.size)
  | "world" => some (StorageCorrespondence.world accounts)
  | "address" => some (.word state.storage.address)
  | "worldComplete" => some (.bool state.storage.complete)
  | "isStatic" => some (.bool state.storage.isStatic)
  | "exit" => some (.word state.storage.exit)
  | "returnOffset" => some (.word state.storage.returnOffset)
  | "returnSize" => some (.word state.storage.returnSize)
  | _ => none

def Observed (accounts : StorageCorrespondence.Accounts) (state : RuntimeEffectsSemantics.State)
    (cell : InitializedCell) : Prop :=
  ∀ value, expected accounts state cell.name = some value → cell.value = value

structure Cell (cells : List InitializedCell) (store : Core.Store)
    (name : String) (type : Core.Ty) (value : Core.Value) where
  cell : InitializedCell
  member : cell ∈ cells
  named : cell.name = name
  typed : cell.type = type
  stored : store.read? cell.location = some value

theorem Cell.slot {cells : List InitializedCell} {store : Core.Store}
    {name : String} {type : Core.Ty} {value : Core.Value}
    (selected : Cell cells store name type value) :
    ⟨name, type, selected.cell.location⟩ ∈ cells.map InitializedCell.effectSlot := by
  exact List.mem_map.mpr ⟨selected.cell, selected.member,
    by simp only [InitializedCell.effectSlot, selected.named, selected.typed]⟩

theorem observe {cells : List InitializedCell} {store : Core.Store}
    {accounts : StorageCorrespondence.Accounts} {state : RuntimeEffectsSemantics.State}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots)
    (initialized : InitializedCells cells store)
    (observed : ∀ cell ∈ cells, Observed accounts state cell)
    {name : String} {type : Core.Ty} {value : Core.Value}
    (member : (name, type) ∈ Effects.slots)
    (specified : expected accounts state name = some value) :
    Nonempty (Cell cells store name type value) := by
  rw [← signature] at member
  obtain ⟨cell, present, same⟩ := List.mem_map.mp member
  obtain ⟨named, typed⟩ := Prod.mk.inj same
  have valued := observed cell present value (by simpa only [named] using specified)
  exact ⟨cell, present, named, typed, by simpa only [valued] using initialized cell present⟩

structure StateReady (cells : List InitializedCell) (store : Core.Store)
    (state : RuntimeEffectsSemantics.State) where
  memory : Nat
  locations : StorageBuiltinCorrespondence.Locations
  memoryMember : ⟨"memory", Core.WordMapping.type, memory⟩ ∈ cells.map InitializedCell.effectSlot
  worldMember : ⟨"world", AccountState.type, locations.world⟩ ∈ cells.map InitializedCell.effectSlot
  addressMember : ⟨"address", .word, locations.address⟩ ∈ cells.map InitializedCell.effectSlot
  completeMember : ⟨"worldComplete", .bool, locations.complete⟩ ∈ cells.map InitializedCell.effectSlot
  staticMember : ⟨"isStatic", .bool, locations.isStatic⟩ ∈ cells.map InitializedCell.effectSlot
  sizeMember : ⟨"memorySize", .word, locations.memorySize⟩ ∈ cells.map InitializedCell.effectSlot
  exitMember : ⟨"exit", .word, locations.exit⟩ ∈ cells.map InitializedCell.effectSlot
  offsetMember : ⟨"returnOffset", .word, locations.returnOffset⟩ ∈ cells.map InitializedCell.effectSlot
  returnSizeMember : ⟨"returnSize", .word, locations.returnSize⟩ ∈ cells.map InitializedCell.effectSlot
  memoryRelated : MemoryCorrespondence.StateRel memory locations.memorySize state.memory store
  storageRelated : StorageBuiltinCorrespondence.StateRel locations state.storage store
  distinct : (memory :: locations.all).Nodup

/-- Every input is an observation of the real initialized cells. No abstract
runtime layout or aliasing condition is assumed. -/
theorem state_ready {cells : List InitializedCell} {store : Core.Store}
    {accounts : StorageCorrespondence.Accounts} {state : RuntimeEffectsSemantics.State}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots)
    (initialized : InitializedCells cells store) (separate : CellLocations cells)
    (observed : ∀ cell ∈ cells, Observed accounts state cell)
    (world : accounts.map Prod.fst = state.storage.world) :
    Nonempty (StateReady cells store state) := by
  obtain ⟨memory⟩ := observe signature initialized observed (name := "memory") (type := Core.WordMapping.type) (by simp [Effects.slots]) rfl
  obtain ⟨size⟩ := observe signature initialized observed (name := "memorySize") (type := .word) (by simp [Effects.slots]) rfl
  obtain ⟨worldCell⟩ := observe signature initialized observed (name := "world") (type := AccountState.type) (by simp [Effects.slots]) rfl
  obtain ⟨address⟩ := observe signature initialized observed (name := "address") (type := .word) (by simp [Effects.slots]) rfl
  obtain ⟨complete⟩ := observe signature initialized observed (name := "worldComplete") (type := .bool) (by simp [Effects.slots]) rfl
  obtain ⟨isStatic⟩ := observe signature initialized observed (name := "isStatic") (type := .bool) (by simp [Effects.slots]) rfl
  obtain ⟨exit⟩ := observe signature initialized observed (name := "exit") (type := .word) (by simp [Effects.slots]) rfl
  obtain ⟨offset⟩ := observe signature initialized observed (name := "returnOffset") (type := .word) (by simp [Effects.slots]) rfl
  obtain ⟨returnSize⟩ := observe signature initialized observed (name := "returnSize") (type := .word) (by simp [Effects.slots]) rfl
  let selected := [memory.cell, worldCell.cell, address.cell, complete.cell, isStatic.cell,
    exit.cell, offset.cell, returnSize.cell, size.cell]
  have included : ∀ cell ∈ selected, cell ∈ cells := by
    intro cell member
    simp only [selected, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | exact memory.member
      | exact worldCell.member
      | exact address.member
      | exact complete.member
      | exact isStatic.member
      | exact exit.member
      | exact offset.member
      | exact returnSize.member
      | exact size.member
  have names : (selected.map InitializedCell.name).Nodup := by
    simp only [selected, List.map_cons, List.map_nil, memory.named, worldCell.named, address.named,
      complete.named, isStatic.named, exit.named, offset.named, returnSize.named, size.named]
    decide
  have distinct := (separate.subset included).nodup names
  let locations : StorageBuiltinCorrespondence.Locations :=
    ⟨worldCell.cell.location, address.cell.location, complete.cell.location, isStatic.cell.location,
      exit.cell.location, offset.cell.location, returnSize.cell.location, size.cell.location⟩
  have joint : (memory.cell.location :: locations.all).Nodup := distinct
  refine ⟨⟨memory.cell.location, locations, memory.slot, worldCell.slot, address.slot,
    complete.slot, isStatic.slot, size.slot, exit.slot, offset.slot, returnSize.slot,
    ⟨?_, memory.stored, size.stored⟩, ?_, joint⟩⟩
  · exact separate.different memory.member size.member (by simp only [memory.named, size.named]; decide)
  · exact ⟨⟨accounts, world, worldCell.stored⟩, address.stored, complete.stored, isStatic.stored,
      exit.stored, offset.stored, returnSize.stored, (List.nodup_cons.mp joint).2⟩

theorem cell_location_ne {cells : List InitializedCell} (separate : CellLocations cells)
    {cell : InitializedCell} (member : cell ∈ cells) {slot : EffectSlot}
    (slotMember : slot ∈ cells.map InitializedCell.effectSlot) (different : cell.name ≠ slot.name) :
    cell.location ≠ slot.location := by
  obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp slotMember
  exact separate.different member otherMember different

theorem StateReady.passive_cell {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} (ready : StateReady cells store state)
    (separate : CellLocations cells) (initialized : InitializedCells cells store)
    {cell : InitializedCell} (member : cell ∈ cells)
    (outside : cell.name ∉ ["memory", "memorySize", "world", "exit", "returnOffset", "returnSize"]) :
    RuntimeEffectsFrameCorrespondence.PassiveCell
      (RuntimeEffectsCorrespondence.initialLayout ready.memoryRelated ready.storageRelated ready.distinct)
      (cells.map InitializedCell.effectSlot) store cell.name cell.value := by
  refine ⟨cell.effectSlot, List.mem_map.mpr ⟨cell, member, rfl⟩, rfl, ?_,
    initialized.location_bound member, initialized cell member⟩
  intro inside
  change cell.location ∈ [ready.memory, ready.locations.memorySize] ++ ready.locations.mutable at inside
  simp only [StorageBuiltinCorrespondence.Locations.mutable, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at inside
  rcases inside with (same | same) | same | same | same | same
  · exact cell_location_ne separate member ready.memoryMember (fun named => outside (by simp [named])) same
  · exact cell_location_ne separate member ready.sizeMember (fun named => outside (by simp [named])) same
  · exact cell_location_ne separate member ready.worldMember (fun named => outside (by simp [named])) same
  · exact cell_location_ne separate member ready.exitMember (fun named => outside (by simp [named])) same
  · exact cell_location_ne separate member ready.offsetMember (fun named => outside (by simp [named])) same
  · exact cell_location_ne separate member ready.returnSizeMember (fun named => outside (by simp [named])) same

end Solcore.Frontend.RustHull.RuntimeInitializedEffects
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeLogInitializationCorrespondence
/-! Concrete initialized log values extend the already established runtime
relation. Distinct cell names establish environment-read separation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeLogEffectsCorrespondence
open Correspondence ScalarExecution

theorem initial_state {layout : Layout} {slots : List EffectSlot} {state : RuntimeLogEffectsSemantics.State}
    {store : Core.Store}
    (runtime : StateRel (RuntimeEnvironmentEffectsCorrespondence.model layout.toLayout
      (prefixRead layout.boundary store) slots) [] ⟨[], state.runtime⟩ store)
    (logs : store.read? layout.logs = some (Core.WordMapping.encode state.words))
    (cursor : store.read? layout.logSize = some (.word state.cursor)) :
    StateRel (model layout (prefixRead layout.boundary store) slots) [] ⟨[], state⟩ store := by
  have logsRead : prefixRead layout.boundary store layout.logs = some (Core.WordMapping.encode state.words) := by
    simpa only [prefixRead, layout.logsBelow, ↓reduceIte] using logs
  have cursorRead : prefixRead layout.boundary store layout.logSize = some (.word state.cursor) := by
    simpa only [prefixRead, layout.logSizeBelow, ↓reduceIte] using cursor
  have unchanged : patched layout (prefixRead layout.boundary store) state = prefixRead layout.boundary store := by
    funext location
    unfold patched
    split
    · subst location; exact logsRead.symm
    · split
      · subst location; exact cursorRead.symm
      · rfl
  exact ⟨runtime.toHeapRel, runtime.external.1, runtime.external.2.1,
    by simpa only [unchanged] using runtime.external.2.2, logsRead, cursorRead⟩

theorem Passive.of_names {layout : Layout} {slots : List EffectSlot}
    (names : ∀ first ∈ slots, ∀ second ∈ slots, first.location = second.location → first.name = second.name)
    (memoryMember : ⟨"memory", Core.WordMapping.type, layout.memory⟩ ∈ slots)
    (worldMember : ⟨"world", AccountState.type, layout.storage.world⟩ ∈ slots)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots)
    (logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ slots)
    (logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ slots) : Passive layout slots := by
  have runtimePassive := RuntimeEnvironmentEffectsCorrespondence.Passive.of_names names memoryMember worldMember memorySizeMember
    exitMember offsetMember sizeMember
  intro slot member state value observed inside
  rcases List.mem_cons.mp inside with same | inside
  · have named := names slot member _ logsMember same
    rw [named] at observed
    cases slot.type <;> contradiction
  rcases List.mem_cons.mp inside with same | inside
  · have named := names slot member _ logSizeMember same
    rw [named] at observed
    cases slot.type <;> contradiction
  · exact runtimePassive slot member state value observed inside

end Solcore.Frontend.RustHull.RuntimeLogEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeLogInitializedEffects
/-! Event cells are recovered from actual initialization, with their separation
from the other runtime cells derived from the allocator's named locations. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeLogInitializedEffects
open Correspondence ScalarExecution RuntimeInitializedEffects

structure Ready {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} (runtime : StateReady cells store state)
    (words : LogsSemantics.Words) (cursor : Core.Word) where
  layout : RuntimeLogEffectsCorrespondence.Layout
  base : layout.toLayout = RuntimeEffectsCorrespondence.initialLayout
    runtime.memoryRelated runtime.storageRelated runtime.distinct
  logsMember : ⟨"logs", Core.WordMapping.type, layout.logs⟩ ∈ cells.map InitializedCell.effectSlot
  logSizeMember : ⟨"logSize", .word, layout.logSize⟩ ∈ cells.map InitializedCell.effectSlot
  logsRead : store.read? layout.logs = some (Core.WordMapping.encode words)
  logSizeRead : store.read? layout.logSize = some (.word cursor)

theorem observe {cells : List InitializedCell} {store : Core.Store}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots)
    (initialized : InitializedCells cells store)
    {name : String} {type : Core.Ty} {value : Core.Value}
    (member : (name, type) ∈ Effects.slots)
    (observed : ∀ cell ∈ cells, cell.name = name → cell.value = value) :
    Nonempty (Cell cells store name type value) := by
  rw [← signature] at member
  obtain ⟨cell, present, same⟩ := List.mem_map.mp member
  obtain ⟨named, typed⟩ := Prod.mk.inj same
  exact ⟨cell, present, named, typed,
    by simpa only [observed cell present named] using initialized cell present⟩

theorem outside_runtime {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} (runtime : StateReady cells store state)
    (separate : CellLocations cells) {cell : InitializedCell} (member : cell ∈ cells)
    (outside : cell.name ∉ ["memory", "world", "address", "worldComplete", "isStatic",
      "exit", "returnOffset", "returnSize", "memorySize"]) :
    cell.location ∉ runtime.memory :: runtime.locations.all := by
  intro inside
  simp only [StorageBuiltinCorrespondence.Locations.all, List.mem_cons,
    List.not_mem_nil, or_false] at inside
  rcases inside with same | same | same | same | same | same | same | same | same
  all_goals
    first
    | exact cell_location_ne separate member runtime.memoryMember (fun named => outside (by simp [named])) same
    | exact cell_location_ne separate member runtime.worldMember (fun named => outside (by simp [named])) same
    | exact cell_location_ne separate member runtime.addressMember (fun named => outside (by simp [named])) same
    | exact cell_location_ne separate member runtime.completeMember (fun named => outside (by simp [named])) same
    | exact cell_location_ne separate member runtime.staticMember (fun named => outside (by simp [named])) same
    | exact cell_location_ne separate member runtime.exitMember (fun named => outside (by simp [named])) same
    | exact cell_location_ne separate member runtime.offsetMember (fun named => outside (by simp [named])) same
    | exact cell_location_ne separate member runtime.returnSizeMember (fun named => outside (by simp [named])) same
    | exact cell_location_ne separate member runtime.sizeMember (fun named => outside (by simp [named])) same

theorem ready {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {words : LogsSemantics.Words} {cursor : Core.Word}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots)
    (initialized : InitializedCells cells store) (separate : CellLocations cells)
    (runtime : StateReady cells store state)
    (logsObserved : ∀ cell ∈ cells, cell.name = "logs" → cell.value = Core.WordMapping.encode words)
    (cursorObserved : ∀ cell ∈ cells, cell.name = "logSize" → cell.value = .word cursor) :
    Nonempty (Ready runtime words cursor) := by
  obtain ⟨logs⟩ := observe signature initialized (type := Core.WordMapping.type) (by simp [Effects.slots]) logsObserved
  obtain ⟨size⟩ := observe signature initialized (type := .word) (by simp [Effects.slots]) cursorObserved
  have logOutside := outside_runtime runtime separate logs.member (by rw [logs.named]; decide)
  have sizeOutside := outside_runtime runtime separate size.member (by rw [size.named]; decide)
  have different := separate.different logs.member size.member (by rw [logs.named, size.named]; decide)
  let layout : RuntimeLogEffectsCorrespondence.Layout := {
    toLayout := RuntimeEffectsCorrespondence.initialLayout runtime.memoryRelated runtime.storageRelated runtime.distinct
    logs := logs.cell.location
    logSize := size.cell.location
    jointDistinct := List.nodup_cons.mpr ⟨(by simpa only [RuntimeEffectsCorrespondence.initialLayout, List.mem_cons, not_or] using And.intro different logOutside),
      List.nodup_cons.mpr ⟨sizeOutside, runtime.distinct⟩⟩
    logsBelow := initialized.location_bound logs.member
    logSizeBelow := initialized.location_bound size.member }
  exact ⟨layout, rfl, logs.slot, size.slot, logs.stored, size.stored⟩

theorem Ready.passive_cell {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : StateReady cells store state}
    {words : LogsSemantics.Words} {cursor : Core.Word} (ready : Ready runtime words cursor)
    (separate : CellLocations cells) (initialized : InitializedCells cells store)
    {cell : InitializedCell} (member : cell ∈ cells)
    (outside : cell.name ∉ ["logs", "logSize", "memory", "memorySize", "world", "exit", "returnOffset", "returnSize"]) :
    RuntimeLogEffectsFrameCorrespondence.PassiveCell ready.layout
      (cells.map InitializedCell.effectSlot) store cell.name cell.value := by
  obtain ⟨slot, present, named, passive, below, stored⟩ := runtime.passive_cell separate initialized member
    (fun inside => outside (.tail _ (.tail _ inside)))
  refine ⟨slot, present, named, ?_, ?_, stored⟩
  · intro inside
    rcases List.mem_cons.mp inside with same | inside
    · obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp present
      exact cell_location_ne separate otherMember ready.logsMember
        (fun eq => outside (by simp [← named, InitializedCell.effectSlot, eq])) same
    rcases List.mem_cons.mp inside with same | inside
    · obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp present
      exact cell_location_ne separate otherMember ready.logSizeMember
        (fun eq => outside (by simp [← named, InitializedCell.effectSlot, eq])) same
    · exact passive (by simpa only [ready.base] using inside)
  · simpa only [ready.base] using below

end Solcore.Frontend.RustHull.RuntimeLogInitializedEffects
end
