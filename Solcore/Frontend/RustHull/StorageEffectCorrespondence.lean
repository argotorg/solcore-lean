import Solcore.Frontend.RustHull.StorageBuiltinCorrespondence
import Solcore.Frontend.RustHull.ExternalCallCorrespondence
import Solcore.Frontend.RustHull.RuntimeAssemblyCorrespondence

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
