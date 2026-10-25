import Solcore.Frontend.RustHull.RuntimeEnvironmentEffectsSemantics
import Solcore.Frontend.RustHull.RuntimeEffectsCorrespondence
import Solcore.Frontend.RustHull.EnvironmentBuiltinCorrespondence
import Solcore.Frontend.RustHull.RuntimeEffectsProjectionPreservation

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
