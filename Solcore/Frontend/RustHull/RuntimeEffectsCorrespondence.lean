import Solcore.Frontend.RustHull.RuntimeEffectsSemantics
import Solcore.Frontend.RustHull.MemoryEffectCorrespondence
import Solcore.Frontend.RustHull.StorageEffectCorrespondence

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
