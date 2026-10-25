import Solcore.Frontend.RustHull.MemoryBuiltinCorrespondence
import Solcore.Frontend.RustHull.ExternalCallCorrespondence
import Solcore.Frontend.RustHull.RuntimeAssemblyCorrespondence

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
