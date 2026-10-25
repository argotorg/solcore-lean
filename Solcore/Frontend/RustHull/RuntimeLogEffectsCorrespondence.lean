import Solcore.Frontend.RustHull.RuntimeLogEffectsSemantics
import Solcore.Frontend.RustHull.RuntimeEnvironmentEffectsCorrespondence
import Solcore.Frontend.RustHull.LogBuiltinCorrespondence

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
