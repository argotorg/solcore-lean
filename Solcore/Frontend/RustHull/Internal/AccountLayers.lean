import Solcore.Frontend.RustHull.Semantics.Layers
import Solcore.Frontend.RustHull.Internal.TerminationLayers
import Solcore.Frontend.RustHull.Internal.EffectBuiltins
import Solcore.Frontend.RustHull.Internal.EffectLayers

/-!
# Effect layers: accounts, code, return data

The frame and message proofs of the account, code and return data layers.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeAccountStateCorrespondence
/-! The concrete balance cell extends the established runtime model. Its
contents are derived from initialization and retained by current operations. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeAccountEffectsCorrespondence
open Correspondence

structure Layout extends toLogLayout : RuntimeLogEffectsCorrespondence.Layout where
  balances : Nat
  balancesBelow : balances < boundary
  balancesOutside : balances ∉ RuntimeLogEffectsCorrespondence.mutable toLogLayout

def Resources (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot)
    (state : RuntimeAccountEffectsSemantics.State) (read : Nat → Option Core.Value) : Prop :=
  RuntimeLogEffectsCorrespondence.Resources layout.toLogLayout baseline slots state.runtime read ∧
  read layout.balances = some (Core.WordMapping.encode state.balances)

def model (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot) :
    StateModel RuntimeAccountEffectsSemantics.State :=
  StateModel.cutoff layout.boundary (Resources layout baseline slots)

def sourceRuntime (state : Semantics.State RuntimeAccountEffectsSemantics.State) :
    Semantics.State RuntimeHashEffectsSemantics.State := ⟨state.heap, state.external.runtime⟩

theorem runtime_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {world : World} {state : Semantics.State RuntimeAccountEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots) world state store) :
    StateRel (RuntimeLogEffectsCorrespondence.model layout.toLogLayout baseline slots) world (sourceRuntime state) store :=
  ⟨related.toHeapRel, related.external.1, related.external.2.1, related.external.2.2.1⟩

theorem balances_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {world : World} {state : Semantics.State RuntimeAccountEffectsSemantics.State} {store : Core.Store}
    (related : StateRel (model layout baseline slots) world state store) :
    store.read? layout.balances = some (Core.WordMapping.encode state.external.balances) := by
  simpa only [prefixRead, layout.balancesBelow, ↓reduceIte] using related.external.2.2.2

theorem runtime_updated {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {world : World} {state : Semantics.State RuntimeAccountEffectsSemantics.State}
    {initial final : Core.Store} {runtime : RuntimeHashEffectsSemantics.State}
    (before : StateRel (model layout baseline slots) world state initial)
    (after : StateRel (RuntimeLogEffectsCorrespondence.model layout.toLogLayout baseline slots) world
      {sourceRuntime state with external := runtime} final) :
    StateRel (model layout baseline slots) world {state with external := {state.external with runtime := runtime}} final := by
  refine ⟨after.toHeapRel, after.external.1, after.external.2.1, after.external.2.2, ?_⟩
  rw [RuntimeLogEffectsCorrespondence.other_related after layout.balancesOutside,
    ← RuntimeLogEffectsCorrespondence.other_related (runtime_related before) layout.balancesOutside]
  exact before.external.2.2.2

theorem memory_updated {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {world : World} {state : Semantics.State RuntimeAccountEffectsSemantics.State}
    {initial final : Core.Store} {memory : MemorySemantics.State}
    (before : StateRel (model layout baseline slots) world state initial)
    (memoryAfter : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize memory final)
    (frame : MemoryCorrespondence.Frame layout.memory layout.storage.memorySize initial final) :
    StateRel (model layout baseline slots) world
      {state with external := RuntimeAccountEffectsSemantics.withMemory state.external memory} final :=
  runtime_updated before (RuntimeCopyEffectsCorrespondence.memory_updated passive (runtime_related before) memoryAfter frame)

theorem initial_state {layout : Layout} {slots : List EffectSlot} {state : RuntimeAccountEffectsSemantics.State}
    {store : Core.Store}
    (runtime : StateRel (RuntimeLogEffectsCorrespondence.model layout.toLogLayout
      (prefixRead layout.boundary store) slots) [] ⟨[], state.runtime⟩ store)
    (balances : store.read? layout.balances = some (Core.WordMapping.encode state.balances)) :
    StateRel (model layout (prefixRead layout.boundary store) slots) [] ⟨[], state⟩ store :=
  ⟨runtime.toHeapRel, runtime.external.1, runtime.external.2.1, runtime.external.2.2,
    by simpa only [prefixRead, layout.balancesBelow, ↓reduceIte] using balances⟩

end Solcore.Frontend.RustHull.RuntimeAccountEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeAccountEffectsCorrespondence
/-! Concrete account inspection composes with the initialized runtime model
before the common recursive proof reaches actual function assembly. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeAccountEffectsCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence

def supported (slots : List EffectSlot) (name : String) : Prop :=
  RuntimeHashEffectsCorrespondence.supported slots name ∨
    ∃ operation : AccountObservationSemantics.Operation, operation.name = name

private theorem primitive_none {slots : List EffectSlot} {name : String}
    (enabled : supported slots name) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = none := by
  rcases enabled with ((((((memory | storage) | environment) | logs) | termination) | copy) | hash) | ⟨operation, rfl⟩
  · obtain ⟨operation, rfl⟩ := memory
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := storage
    cases operation with | load transient | store transient => cases transient <;> rfl
  · obtain ⟨operation, rfl, _⟩ := environment
    cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals rfl
  · obtain ⟨operation, rfl⟩ := logs
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := termination
    cases operation <;> rfl
  · obtain ⟨operation, rfl, _⟩ := copy
    cases operation <;> rfl
  · subst name
    rfl
  · cases operation <;> rfl

private theorem copy_named {calldata : MemorySemantics.Entries} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : MemoryCopySemantics.Builtin calldata name type arguments initial result final) :
    ∃ operation : MemoryCopySemantics.Operation, operation.name = name := by
  cases computed with
  | move _ => exact ⟨.move, rfl⟩
  | calldata _ => exact ⟨.calldata, rfl⟩

private theorem log_named {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : LogsSemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : LogsSemantics.Builtin name type arguments initial result final) :
    ∃ operation : LogsSemantics.Operation, operation.name = name := by
  cases computed with | log operation _ _ _ _ _ _ => exact ⟨operation, rfl⟩

private theorem hash_named {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : KeccakSemantics.Builtin name type arguments initial result final) : name = "keccak256" := by
  cases computed
  rfl

private theorem runtime_unsupported (operation : AccountObservationSemantics.Operation)
    {type : Ty} {arguments : List Semantics.Value} {initial final : RuntimeHashEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (computed : RuntimeHashEffectsSemantics.Builtin operation.name type arguments initial result final) : False := by
  cases computed with
  | runtime computed =>
      cases computed with
      | runtime computed =>
          cases computed with
          | runtime computed =>
              cases computed with
              | runtime computed =>
                  have missing : RuntimeEnvironmentEffectsSemantics.builtin operation.name type arguments initial.runtime = none := by
                    cases operation <;> rfl
                  rw [missing] at computed
                  contradiction
              | logs computed =>
                  obtain ⟨log, named⟩ := log_named computed
                  cases operation <;> cases log <;> simp [AccountObservationSemantics.Operation.name, LogsSemantics.Operation.name] at named
          | termination computed =>
              have missing : TerminationSemantics.builtin operation.name type arguments initial.runtime.runtime = none := by
                cases operation <;> rfl
              rw [missing] at computed
              contradiction
      | copy computed =>
          obtain ⟨copy, named⟩ := copy_named computed
          cases operation <;> cases copy <;> simp [AccountObservationSemantics.Operation.name, MemoryCopySemantics.Operation.name] at named
  | hash computed =>
      have named := hash_named computed
      cases operation <;> simp [AccountObservationSemantics.Operation.name] at named

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
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
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots) :
    ExternalCallPreservation (supported slots) (model layout baseline slots) slots RuntimeAccountEffectsSemantics.effects := by
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | runtime computed =>
          have runtimeEnabled : RuntimeHashEffectsCorrespondence.supported slots name := by
            rcases enabled with runtime | ⟨operation, rfl⟩
            · exact runtime
            · exact False.elim (runtime_unsupported operation computed)
          have call : Semantics.EvalCall functions RuntimeHashEffectsSemantics.effects name type sources
              (sourceRuntime initial) result _ := .external absent notPrimitive computed
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          obtain ⟨target, finalStore, resultRelated, evaluated, finalState, installedFinal, retained⟩ :=
            RuntimeHashEffectsCorrespondence.external_preserves layout.toLogLayout baseline slots passive
              memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
              logsMember logSizeMember runtimeEnabled notFunction call typeCompiled compiled related packed runtime (runtime_related state) installed
          exact ⟨target, finalStore, resultRelated, evaluated, runtime_updated state finalState, installedFinal, retained⟩
      | observation computed =>
          obtain ⟨operation, named⟩ := computed.named
          subst name
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          have beforeLog := runtime_related state
          have beforeEnvironment := RuntimeLogEffectsCorrespondence.runtime_related beforeLog
          have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related beforeEnvironment
          have memoryRelated := RuntimeEffectsCorrespondence.memory_related beforeRuntime
          have storageRelated := RuntimeEffectsCorrespondence.storage_related beforeRuntime
          obtain ⟨target, finalStore, resultRelated, evaluated, memoryFinal, frame⟩ :=
            AccountObservationBuiltinCorrespondence.preserves operation compiled computed related runtime
              memoryMember memorySizeMember worldMember addressMember completeMember balancesMember
              memoryRelated storageRelated (balances_related state) packed
          have retained : ClosuresPreserved argumentStore finalStore := MemoryEffectCorrespondence.closures_preserved memoryRelated frame
          exact ⟨target, finalStore, resultRelated, evaluated, memory_updated passive state memoryFinal frame,
            installed.preserved retained, retained⟩

theorem assemble_program (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
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
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    {functions : List Function} {function : Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (eligible : ExecutableProgram (supported slots) functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State RuntimeAccountEffectsSemantics.State}
    {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions RuntimeAccountEffectsSemantics.effects
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
      memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember balancesMember) eligible values evaluated
    runtimeLength covered runtimeRelated separated state

end Solcore.Frontend.RustHull.RuntimeAccountEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeAccountEffectsFrameCorrespondence
/-! Source account observations reach actual frame calls and final snapshots.
The balance mapping is read from the source state and its initialized cell. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeAccountEffectsFrameCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeAccountEffectsCorrespondence (Layout model runtime_related balances_related)
open RuntimeAccountEffectsCorrespondence (supported assemble_program)

abbrev slotTypes := RuntimeLogEffectsFrameCorrespondence.slotTypes
abbrev cell_observed := @RuntimeLogEffectsFrameCorrespondence.cell_observed
def snapshotValues (state : RuntimeAccountEffectsSemantics.State) (accounts : StorageCorrespondence.Accounts) :
    String → Core.Value :=
  RuntimeLogEffectsFrameCorrespondence.snapshotValues
    (fun name => if name = "balances" then Core.WordMapping.encode state.balances
      else if name = "logs" then Core.WordMapping.encode [] else .word (Core.Word.ofNatModulo 0))
    state.runtime accounts

/-- A frame installed earlier retains its captured environment. The body and
completion wrapper observe the final source world and balances through the
compiler's actual frame references. -/
theorem compileFrame_call_preserves_observed {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout}
    {initial : RuntimeAccountEffectsSemantics.State}
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
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {final : Semantics.State RuntimeAccountEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeAccountEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.storage.complete)) finalStore ∧
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
      logsMember logSizeMember balancesMember assembled selected eligible argumentValues evaluated
      (runtimeValues := values.reverse) (caller := bundleValues values :: captured)
      (by simpa [AccountRuntime.frameScope, slotTypes, MemoryFrameCorrespondence.slotTypes] using length)
      (MemoryFrameCorrespondence.frame_coverage _) runtime separated
      initialRelated
  have finalStorage := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related (RuntimeLogEffectsCorrespondence.runtime_related (runtime_related state)))
  have finalLogs := RuntimeLogEffectsCorrespondence.logs_related (runtime_related state)
  obtain ⟨accounts, sourceWorld, worldRead⟩ := finalStorage.world
  have finalWorld := cell_observed references runtime worldMember worldRead
  have finalAddress := cell_observed references runtime addressMember finalStorage.address
  have finalComplete := cell_observed references runtime completeMember finalStorage.complete
  have finalSnapshot : ∀ name ∈ frameSnapshotNames,
      FrameCellObserved cells (values.reverse ++ .unit :: bundleValues values :: captured)
        bodyStore name (snapshotValues final.external accounts name) := by
    intro name member
    simp [frameSnapshotNames] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cell_observed references runtime exitMember finalStorage.exit
    · exact cell_observed references runtime offsetMember finalStorage.returnOffset
    · exact cell_observed references runtime sizeMember finalStorage.returnSize
    · exact cell_observed references runtime memoryMember finalLogs.logs.memory
    · exact cell_observed references runtime logsMember finalLogs.logs.logs
    · exact cell_observed references runtime logSizeMember finalLogs.logs.logSize
    · exact cell_observed references runtime balancesMember (balances_related state)
    · exact finalWorld
  have completed := frameCompletion_evaluates executed accounts final.external.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.storage.complete
    finalWorld finalAddress finalComplete finalSnapshot
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.getStore_extension accounts
    final.external.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.storage.complete
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
    {initial : RuntimeAccountEffectsSemantics.State}
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
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {final : Semantics.State RuntimeAccountEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeAccountEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots)
        extension final finalStore := by
  obtain ⟨extension, status, accounts, finalStore, represented, related, executed, state, _⟩ :=
    compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length runtime separated
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember initialRelated passive evaluated
  exact ⟨extension, status, accounts, finalStore, represented, related, executed, state⟩

/-- Direct evaluation of freshly compiled frame code is a special case of the
same theorem for captured calls. -/
theorem compileFrame_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout}
    {initial : RuntimeAccountEffectsSemantics.State}
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
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {final : Semantics.State RuntimeAccountEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeAccountEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment initialStore (.apply compiled argument)
        (frameCompletionValue status (snapshotValues final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots)
        extension final finalStore := by
  obtain ⟨own, body, cells, _, _, rfl⟩ := compileFrame_components accepted
  exact compileFrame_call_preserves accepted eligible (CapturedClosure.lambda _ _ _ environment)
    Core.Evaluates.lambda supplied length runtime separated memoryMember worldMember addressMember completeMember
    staticMember memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember balancesMember initialRelated passive
    evaluated

end Solcore.Frontend.RustHull.RuntimeAccountEffectsFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractAccountCorrespondence
/-! Account observations and the explicit source balance ledger pass through
actual message finalization and transaction completion. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractAccountCorrespondence
open Correspondence ScalarExecution CodeBuilder

def supported (name : String) : Prop := ContractHashCorrespondence.supported name ∨
  ∃ operation : AccountObservationSemantics.Operation, operation.name = name

theorem supported_actual {slots : List EffectSlot}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots) :
    RuntimeAccountEffectsCorrespondence.supported slots = supported := by
  funext name
  simp only [RuntimeAccountEffectsCorrespondence.supported, supported, ContractHashCorrespondence.supported_actual signature]

def messageValue (result : Semantics.Result Semantics.Value) (state : RuntimeAccountEffectsSemantics.State)
    (accounts : StorageCorrespondence.Accounts) (target : Core.Word) : Core.Value :=
  ContractLogCorrespondence.messageValue result state.runtime accounts target state.balances

def MessageRel (result : Semantics.Result Semantics.Value) (state : RuntimeAccountEffectsSemantics.State)
    (target : Core.Word) (value : Core.Value) : Prop :=
  ContractLogCorrespondence.MessageRel result state.runtime target state.balances value

theorem frameCall_message_evaluates {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (RuntimeLogEffectsFrameCorrespondence.slotTypes slots) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram (RuntimeAccountEffectsCorrespondence.supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : RuntimeAccountEffectsCorrespondence.Layout}
    {initial : RuntimeAccountEffectsSemantics.State}
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
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (initialRelated : StateRel (RuntimeAccountEffectsCorrespondence.model layout (prefixRead layout.boundary store) slots) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {final : Semantics.State RuntimeAccountEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) RuntimeAccountEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (address : Core.Word)
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type layout.storage.world))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type layout.balances))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false)) :
    ∃ value finalStore, Core.Evaluates environment before
      (bind (apply function argument) (fun framed => AccountRuntime.completeMessage shared images target deploying framed) depth)
      value finalStore ∧ MessageRel result final.external address value := by
  obtain ⟨extension, status, accounts, bodyStore, represented, statusRelated, executed, related, worldFinal⟩ :=
    RuntimeAccountEffectsFrameCorrespondence.compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length
      runtime separated memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember initialRelated passive evaluated
  have balancesFinal := RuntimeAccountEffectsCorrespondence.balances_related related
  let frameResult := frameCompletionValue status (ContractLogCorrespondence.snapshotValues final.external.runtime accounts final.external.balances)
    (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.storage.complete)
  obtain ⟨finalStore, completed⟩ := ContractLogCorrespondence.message_evaluates result final.external.runtime accounts address final.external.balances
    statusRelated (worldReference.prepend [frameResult]) (balancesReference.prepend [frameResult])
    (targetValue.prepend [frameResult]) (deployingValue.prepend [frameResult])
    (CodeValue.bound depth environment frameResult) worldFinal balancesFinal
  exact ⟨_, finalStore, .letE executed completed, accounts, represented, rfl⟩

end Solcore.Frontend.RustHull.ContractAccountCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCodeStateCorrespondence
/-! The immutable code bytes and availability flag extend the existing
runtime representation without adding another source state wrapper. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCodeEffectsCorrespondence
open Correspondence

structure Layout extends toAccountLayout : RuntimeAccountEffectsCorrespondence.Layout where
  code : Nat
  known : Nat
  codeBelow : code < boundary
  knownBelow : known < boundary
  codeOutside : code ∉ RuntimeLogEffectsCorrespondence.mutable toLogLayout
  knownOutside : known ∉ RuntimeLogEffectsCorrespondence.mutable toLogLayout

def Resources (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot)
    (image : Option (List UInt8)) (state : RuntimeAccountEffectsSemantics.State)
    (read : Nat → Option Core.Value) : Prop :=
  RuntimeAccountEffectsCorrespondence.Resources layout.toAccountLayout baseline slots state read ∧
  read layout.code = some (Core.WordMapping.encode (Memory.packBytes (image.getD []))) ∧
  read layout.known = some (.bool image.isSome)

def model (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot)
    (image : Option (List UInt8)) : StateModel RuntimeAccountEffectsSemantics.State :=
  StateModel.cutoff layout.boundary (Resources layout baseline slots image)

theorem account_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeAccountEffectsSemantics.State}
    {store : Core.Store} (related : StateRel (model layout baseline slots image) world state store) :
    StateRel (RuntimeAccountEffectsCorrespondence.model layout.toAccountLayout baseline slots) world state store :=
  ⟨related.toHeapRel, related.external.1, related.external.2.1, related.external.2.2.1⟩

theorem code_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeAccountEffectsSemantics.State}
    {store : Core.Store} (related : StateRel (model layout baseline slots image) world state store) :
    store.read? layout.code = some (Core.WordMapping.encode (Memory.packBytes (image.getD []))) := by
  simpa only [prefixRead, layout.codeBelow, ↓reduceIte] using related.external.2.2.2.1

theorem known_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeAccountEffectsSemantics.State}
    {store : Core.Store} (related : StateRel (model layout baseline slots image) world state store) :
    store.read? layout.known = some (.bool image.isSome) := by
  simpa only [prefixRead, layout.knownBelow, ↓reduceIte] using related.external.2.2.2.2

theorem account_updated {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {world : World} {beforeState afterState : Semantics.State RuntimeAccountEffectsSemantics.State}
    {initial final : Core.Store}
    (before : StateRel (model layout baseline slots image) world beforeState initial)
    (after : StateRel (RuntimeAccountEffectsCorrespondence.model layout.toAccountLayout baseline slots) world afterState final) :
    StateRel (model layout baseline slots image) world afterState final := by
  refine ⟨after.toHeapRel, after.external.1, after.external.2.1, after.external.2.2, ?_, ?_⟩
  · rw [RuntimeLogEffectsCorrespondence.other_related
      (RuntimeAccountEffectsCorrespondence.runtime_related after) layout.codeOutside,
      ← RuntimeLogEffectsCorrespondence.other_related
        (RuntimeAccountEffectsCorrespondence.runtime_related (account_related before)) layout.codeOutside]
    exact before.external.2.2.2.1
  · rw [RuntimeLogEffectsCorrespondence.other_related
      (RuntimeAccountEffectsCorrespondence.runtime_related after) layout.knownOutside,
      ← RuntimeLogEffectsCorrespondence.other_related
        (RuntimeAccountEffectsCorrespondence.runtime_related (account_related before)) layout.knownOutside]
    exact before.external.2.2.2.2

theorem memory_updated {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeAccountEffectsSemantics.State}
    {initial final : Core.Store} {memory : MemorySemantics.State}
    (before : StateRel (model layout baseline slots image) world state initial)
    (memoryAfter : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize memory final)
    (frame : MemoryCorrespondence.Frame layout.memory layout.storage.memorySize initial final) :
    StateRel (model layout baseline slots image) world
      {state with external := RuntimeAccountEffectsSemantics.withMemory state.external memory} final :=
  account_updated before (RuntimeAccountEffectsCorrespondence.memory_updated passive (account_related before) memoryAfter frame)

theorem initial_state {layout : Layout} {slots : List EffectSlot} {state : RuntimeAccountEffectsSemantics.State}
    {store : Core.Store} {image : Option (List UInt8)}
    (runtime : StateRel (RuntimeAccountEffectsCorrespondence.model layout.toAccountLayout
      (prefixRead layout.boundary store) slots) [] ⟨[], state⟩ store)
    (code : store.read? layout.code = some (Core.WordMapping.encode (Memory.packBytes (image.getD []))))
    (known : store.read? layout.known = some (.bool image.isSome)) :
    StateRel (model layout (prefixRead layout.boundary store) slots image) [] ⟨[], state⟩ store :=
  ⟨runtime.toHeapRel, runtime.external.1, runtime.external.2.1, runtime.external.2.2,
    by simpa only [prefixRead, layout.codeBelow, ↓reduceIte] using code,
    by simpa only [prefixRead, layout.knownBelow, ↓reduceIte] using known⟩

end Solcore.Frontend.RustHull.RuntimeCodeEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCodeEffectsCorrespondence
/-! Linked image copying composes with the existing runtime semantics before
actual function assembly and public execution. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCodeEffectsCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence

def supported (slots : List EffectSlot) (name : String) : Prop :=
  RuntimeAccountEffectsCorrespondence.supported slots name ∨
    ∃ operation : CodeImageSemantics.Operation, operation.name = name

private theorem primitive_none {slots : List EffectSlot} {name : String}
    (enabled : supported slots name) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = none := by
  rcases enabled with (((((((memory | storage) | environment) | logs) | termination) | copy) | hash) | account) | ⟨operation, rfl⟩
  · obtain ⟨operation, rfl⟩ := memory
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := storage
    cases operation with | load transient | store transient => cases transient <;> rfl
  · obtain ⟨operation, rfl, _⟩ := environment
    cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals rfl
  · obtain ⟨operation, rfl⟩ := logs
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := termination
    cases operation <;> rfl
  · obtain ⟨operation, rfl, _⟩ := copy
    cases operation <;> rfl
  · subst name
    rfl
  · obtain ⟨operation, rfl⟩ := account
    cases operation <;> rfl
  · cases operation <;> rfl

private theorem copy_named {calldata : MemorySemantics.Entries} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : MemoryCopySemantics.Builtin calldata name type arguments initial result final) :
    ∃ operation : MemoryCopySemantics.Operation, operation.name = name := by
  cases computed with
  | move _ => exact ⟨.move, rfl⟩
  | calldata _ => exact ⟨.calldata, rfl⟩

private theorem log_named {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : LogsSemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : LogsSemantics.Builtin name type arguments initial result final) :
    ∃ operation : LogsSemantics.Operation, operation.name = name := by
  cases computed with | log operation _ _ _ _ _ _ => exact ⟨operation, rfl⟩

private theorem hash_named {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : KeccakSemantics.Builtin name type arguments initial result final) : name = "keccak256" := by
  cases computed
  rfl

private theorem hash_runtime_unsupported (operation : CodeImageSemantics.Operation)
    {type : Ty} {arguments : List Semantics.Value} {initial final : RuntimeHashEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (computed : RuntimeHashEffectsSemantics.Builtin operation.name type arguments initial result final) : False := by
  cases computed with
  | runtime computed =>
      cases computed with
      | runtime computed =>
          cases computed with
          | runtime computed =>
              cases computed with
              | runtime computed =>
                  have missing : RuntimeEnvironmentEffectsSemantics.builtin operation.name type arguments initial.runtime = none := by
                    cases operation <;> rfl
                  rw [missing] at computed
                  contradiction
              | logs computed =>
                  obtain ⟨log, named⟩ := log_named computed
                  cases operation <;> cases log <;> simp [CodeImageSemantics.Operation.name, LogsSemantics.Operation.name] at named
          | termination computed =>
              have missing : TerminationSemantics.builtin operation.name type arguments initial.runtime.runtime = none := by
                cases operation <;> rfl
              rw [missing] at computed
              contradiction
      | copy computed =>
          obtain ⟨copy, named⟩ := copy_named computed
          cases operation <;> cases copy <;> simp [CodeImageSemantics.Operation.name, MemoryCopySemantics.Operation.name] at named
  | hash computed =>
      have named := hash_named computed
      cases operation <;> simp [CodeImageSemantics.Operation.name] at named

private theorem runtime_unsupported (operation : CodeImageSemantics.Operation)
    {type : Ty} {arguments : List Semantics.Value} {initial final : RuntimeAccountEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (computed : RuntimeAccountEffectsSemantics.Builtin operation.name type arguments initial result final) : False := by
  cases computed with
  | runtime computed => exact hash_runtime_unsupported operation computed
  | observation computed =>
      obtain ⟨observation, named⟩ := computed.named
      cases operation <;> cases observation <;>
        simp [CodeImageSemantics.Operation.name, AccountObservationSemantics.Operation.name] at named

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (image : Option (List UInt8)) (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
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
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (codeMember : ⟨"code", Core.WordMapping.type, layout.code⟩ ∈ slots)
    (knownMember : ⟨"codeKnown", .bool, layout.known⟩ ∈ slots) :
    ExternalCallPreservation (supported slots) (model layout baseline slots image) slots (RuntimeCodeEffectsSemantics.effects image) := by
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | runtime computed =>
          have runtimeEnabled : RuntimeAccountEffectsCorrespondence.supported slots name := by
            rcases enabled with runtime | ⟨operation, rfl⟩
            · exact runtime
            · exact False.elim (runtime_unsupported operation computed)
          have call : Semantics.EvalCall functions RuntimeAccountEffectsSemantics.effects name type sources
              initial result _ := .external absent notPrimitive computed
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          obtain ⟨target, finalStore, resultRelated, evaluated, finalState, installedFinal, retained⟩ :=
            RuntimeAccountEffectsCorrespondence.external_preserves layout.toAccountLayout baseline slots passive
              memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
              logsMember logSizeMember balancesMember runtimeEnabled notFunction call typeCompiled compiled related packed runtime (account_related state) installed
          exact ⟨target, finalStore, resultRelated, evaluated, account_updated state finalState, installedFinal, retained⟩
      | copy computed =>
          obtain ⟨operation, named⟩ := computed.named
          subst name
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          have beforeAccount := account_related state
          have beforeLog := RuntimeAccountEffectsCorrespondence.runtime_related beforeAccount
          have beforeEnvironment := RuntimeLogEffectsCorrespondence.runtime_related beforeLog
          have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related beforeEnvironment
          have memoryRelated := RuntimeEffectsCorrespondence.memory_related beforeRuntime
          obtain ⟨target, finalStore, resultRelated, evaluated, memoryFinal, frame⟩ :=
            CodeImageBuiltinCorrespondence.preserves operation compiled computed related runtime
              memoryMember memorySizeMember codeMember knownMember
              (code_related state) (known_related state) memoryRelated packed
          have retained : ClosuresPreserved argumentStore finalStore := MemoryEffectCorrespondence.closures_preserved memoryRelated frame
          exact ⟨target, finalStore, resultRelated, evaluated, memory_updated passive state memoryFinal frame,
            installed.preserved retained, retained⟩

theorem assemble_program (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (image : Option (List UInt8)) (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
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
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (codeMember : ⟨"code", Core.WordMapping.type, layout.code⟩ ∈ slots)
    (knownMember : ⟨"codeKnown", .bool, layout.known⟩ ∈ slots)
    {functions : List Function} {function : Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (eligible : ExecutableProgram (supported slots) functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State RuntimeAccountEffectsSemantics.State}
    {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions (RuntimeCodeEffectsSemantics.effects image)
      function sources initial sourceResult final)
    {world : World} {runtimeValues caller : Core.Environment} {store : Core.Store}
    (runtimeLength : runtimeValues.length = runtime.length)
    (covered : ScopeCoverage [] runtime)
    (runtimeRelated : EffectEnvironmentRel slots runtime Core.Renaming.id
      (runtimeValues ++ bundleValues targets :: caller))
    (separated : EffectSlotsSeparate slots)
    (state : StateRel (model layout baseline slots image) world initial store) :
    ∃ extension target finalStore,
      ResultRel own.result sourceResult target ∧
      Core.Evaluates (runtimeValues ++ bundleValues targets :: caller) store allocated target finalStore ∧
      StateRel (model layout baseline slots image) (world ++ extension) final finalStore ∧
      ClosuresPreserved store finalStore :=
  assemble_recursive_program_effects accepted selected
    (external_preserves layout baseline slots image passive memoryMember worldMember addressMember completeMember staticMember
      memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember balancesMember codeMember knownMember) eligible values evaluated
    runtimeLength covered runtimeRelated separated state

end Solcore.Frontend.RustHull.RuntimeCodeEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCodeEffectsFrameCorrespondence
/-! Source code-image operations reach actual frame calls and final snapshots.
The immutable image cells share the existing account representation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCodeEffectsFrameCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeCodeEffectsCorrespondence (Layout model account_related)
open RuntimeAccountEffectsCorrespondence (runtime_related balances_related)
open RuntimeCodeEffectsCorrespondence (supported assemble_program)

abbrev slotTypes := RuntimeLogEffectsFrameCorrespondence.slotTypes
abbrev cell_observed := @RuntimeLogEffectsFrameCorrespondence.cell_observed
abbrev snapshotValues := RuntimeAccountEffectsFrameCorrespondence.snapshotValues

/-- A frame installed earlier retains its captured environment. The body and
completion wrapper observe the final source world and balances through the
compiler's actual frame references. -/
theorem compileFrame_call_preserves_observed {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout} {image : Option (List UInt8)}
    {initial : RuntimeCodeEffectsSemantics.State}
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
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (codeMember : ⟨"code", Core.WordMapping.type, layout.code⟩ ∈ slots)
    (knownMember : ⟨"codeKnown", .bool, layout.known⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots image) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {final : Semantics.State RuntimeCodeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCodeEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots image)
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
    assemble_program layout (prefixRead layout.boundary store) slots image passive
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember codeMember knownMember assembled selected eligible argumentValues evaluated
      (runtimeValues := values.reverse) (caller := bundleValues values :: captured)
      (by simpa [AccountRuntime.frameScope, slotTypes, MemoryFrameCorrespondence.slotTypes] using length)
      (MemoryFrameCorrespondence.frame_coverage _) runtime separated
      initialRelated
  have finalStorage := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related (RuntimeLogEffectsCorrespondence.runtime_related (runtime_related (account_related state))))
  have finalLogs := RuntimeLogEffectsCorrespondence.logs_related (runtime_related (account_related state))
  obtain ⟨accounts, sourceWorld, worldRead⟩ := finalStorage.world
  have finalWorld := cell_observed references runtime worldMember worldRead
  have finalAddress := cell_observed references runtime addressMember finalStorage.address
  have finalComplete := cell_observed references runtime completeMember finalStorage.complete
  have finalSnapshot : ∀ name ∈ frameSnapshotNames,
      FrameCellObserved cells (values.reverse ++ .unit :: bundleValues values :: captured)
        bodyStore name (snapshotValues final.external accounts name) := by
    intro name member
    simp [frameSnapshotNames] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cell_observed references runtime exitMember finalStorage.exit
    · exact cell_observed references runtime offsetMember finalStorage.returnOffset
    · exact cell_observed references runtime sizeMember finalStorage.returnSize
    · exact cell_observed references runtime memoryMember finalLogs.logs.memory
    · exact cell_observed references runtime logsMember finalLogs.logs.logs
    · exact cell_observed references runtime logSizeMember finalLogs.logs.logSize
    · exact cell_observed references runtime balancesMember (balances_related (account_related state))
    · exact finalWorld
  have completed := frameCompletion_evaluates executed accounts final.external.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.storage.complete
    finalWorld finalAddress finalComplete finalSnapshot
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.getStore_extension accounts
    final.external.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.storage.complete
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
    {layout : Layout} {image : Option (List UInt8)}
    {initial : RuntimeCodeEffectsSemantics.State}
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
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (codeMember : ⟨"code", Core.WordMapping.type, layout.code⟩ ∈ slots)
    (knownMember : ⟨"codeKnown", .bool, layout.known⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots image) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {final : Semantics.State RuntimeCodeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCodeEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots image)
        extension final finalStore := by
  obtain ⟨extension, status, accounts, finalStore, represented, related, executed, state, _⟩ :=
    compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length runtime separated
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember codeMember knownMember initialRelated passive evaluated
  exact ⟨extension, status, accounts, finalStore, represented, related, executed, state⟩

/-- Direct evaluation of freshly compiled frame code is a special case of the
same theorem for captured calls. -/
theorem compileFrame_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout} {image : Option (List UInt8)}
    {initial : RuntimeCodeEffectsSemantics.State}
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
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (codeMember : ⟨"code", Core.WordMapping.type, layout.code⟩ ∈ slots)
    (knownMember : ⟨"codeKnown", .bool, layout.known⟩ ∈ slots)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots image) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {final : Semantics.State RuntimeCodeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCodeEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment initialStore (.apply compiled argument)
        (frameCompletionValue status (snapshotValues final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots image)
        extension final finalStore := by
  obtain ⟨own, body, cells, _, _, rfl⟩ := compileFrame_components accepted
  exact compileFrame_call_preserves accepted eligible (CapturedClosure.lambda _ _ _ environment)
    Core.Evaluates.lambda supplied length runtime separated memoryMember worldMember addressMember completeMember
    staticMember memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember balancesMember codeMember knownMember initialRelated passive
    evaluated

end Solcore.Frontend.RustHull.RuntimeCodeEffectsFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractCodeCorrespondence
/-! Code-image operations pass through the actual message finalizer with the
existing account, memory, environment and event observations. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractCodeCorrespondence
open Correspondence ScalarExecution CodeBuilder

def supported (name : String) : Prop := ContractAccountCorrespondence.supported name ∨
  name = "codesize" ∨ ∃ operation : CodeImageSemantics.Operation, operation.name = name

abbrev messageValue := ContractAccountCorrespondence.messageValue
abbrev MessageRel := ContractAccountCorrespondence.MessageRel

private theorem slot_available {slots : List EffectSlot}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots ++ Effects.codeSlots)
    {name : String} {type : Core.Ty} (present : (name, type) ∈ Effects.slots ++ Effects.codeSlots) :
    ∃ location, ⟨name, type, location⟩ ∈ slots := by
  rw [← signature] at present
  obtain ⟨slot, member, same⟩ := List.mem_map.mp present
  rcases slot with ⟨actualName, actualType, location⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact ⟨location, member⟩

private theorem base_inputs (operation : EnvironmentSemantics.Operation) :
    (∀ input ∈ EnvironmentBuiltinCorrespondence.inputs operation, input ∈ Effects.slots) ↔
      operation ≠ .codeSize := by
  cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
  all_goals simp [EnvironmentBuiltinCorrespondence.inputs, EnvironmentSemantics.Direct.slot,
    EnvironmentSemantics.Direct.name, EnvironmentSemantics.AmbientWord.name, Effects.slots, Ambient.slots,
    EnvironmentBuiltinCorrespondence.optionalWord, EnvironmentBuiltinCorrespondence.optionalHashes,
    Ambient.optionalWord, Ambient.optionalHashes]

theorem environment_available {slots : List EffectSlot}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots ++ Effects.codeSlots)
    (operation : EnvironmentSemantics.Operation) : EnvironmentBuiltinCorrespondence.Available slots operation := by
  have included : ∀ input ∈ EnvironmentBuiltinCorrespondence.inputs operation,
      input ∈ Effects.slots ++ Effects.codeSlots := by
    cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals simp [EnvironmentBuiltinCorrespondence.inputs, EnvironmentSemantics.Direct.slot,
      EnvironmentSemantics.Direct.name, EnvironmentSemantics.AmbientWord.name, Effects.slots, Effects.codeSlots,
      Ambient.slots, EnvironmentBuiltinCorrespondence.optionalWord, EnvironmentBuiltinCorrespondence.optionalHashes,
      Ambient.optionalWord, Ambient.optionalHashes]
  intro name type member
  exact slot_available signature (included (name, type) member)

private theorem environment_supported {slots : List EffectSlot}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots ++ Effects.codeSlots)
    (name : String) : RuntimeEnvironmentEffectsCorrespondence.supported slots name ↔
      ContractEnvironmentCorrespondence.supported name ∨ name = "codesize" := by
  constructor
  · rintro (runtime | ⟨operation, named, _⟩)
    · exact .inl (.inl runtime)
    · by_cases codeSize : operation = .codeSize
      · subst operation
        exact .inr named.symm
      · exact .inl (.inr ⟨operation, named, (base_inputs operation).mpr codeSize⟩)
  · rintro ((runtime | ⟨operation, named, _⟩) | rfl)
    · exact .inl runtime
    · exact .inr ⟨operation, named, environment_available signature operation⟩
    · exact .inr ⟨.codeSize, rfl, environment_available signature .codeSize⟩

private theorem copy_available {slots : List EffectSlot}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots ++ Effects.codeSlots)
    (operation : MemoryCopySemantics.Operation) : RuntimeCopyEffectsCorrespondence.Available slots operation := by
  intro _
  exact slot_available signature (by simp [Effects.slots])

theorem supported_actual {slots : List EffectSlot}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = Effects.slots ++ Effects.codeSlots) :
    RuntimeCodeEffectsCorrespondence.supported slots = supported := by
  funext name
  apply propext
  simp only [RuntimeCodeEffectsCorrespondence.supported, RuntimeAccountEffectsCorrespondence.supported,
    RuntimeHashEffectsCorrespondence.supported, RuntimeCopyEffectsCorrespondence.supported,
    RuntimeFullEffectsCorrespondence.supported, RuntimeLogEffectsCorrespondence.supported,
    environment_supported signature name, copy_available signature, and_true, supported,
    ContractAccountCorrespondence.supported, ContractHashCorrespondence.supported,
    ContractCopyCorrespondence.supported, ContractFullCorrespondence.supported, ContractLogCorrespondence.supported]
  simp only [or_assoc, or_left_comm, or_comm]

theorem frameCall_message_evaluates {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (RuntimeLogEffectsFrameCorrespondence.slotTypes slots) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram (RuntimeCodeEffectsCorrespondence.supported slots)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : RuntimeCodeEffectsCorrespondence.Layout} {image : Option (List UInt8)}
    {initial : RuntimeCodeEffectsSemantics.State}
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
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (codeMember : ⟨"code", Core.WordMapping.type, layout.code⟩ ∈ slots)
    (knownMember : ⟨"codeKnown", .bool, layout.known⟩ ∈ slots)
    (initialRelated : StateRel (RuntimeCodeEffectsCorrespondence.model layout (prefixRead layout.boundary store) slots image) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {final : Semantics.State RuntimeCodeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCodeEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (address : Core.Word)
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type layout.storage.world))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type layout.balances))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false)) :
    ∃ value finalStore, Core.Evaluates environment before
      (bind (apply function argument) (fun framed => AccountRuntime.completeMessage shared images target deploying framed) depth)
      value finalStore ∧ MessageRel result final.external address value := by
  obtain ⟨extension, status, accounts, bodyStore, represented, statusRelated, executed, related, worldFinal⟩ :=
    RuntimeCodeEffectsFrameCorrespondence.compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length
      runtime separated memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember codeMember knownMember initialRelated passive evaluated
  have balancesFinal := RuntimeAccountEffectsCorrespondence.balances_related (RuntimeCodeEffectsCorrespondence.account_related related)
  let frameResult := frameCompletionValue status (ContractLogCorrespondence.snapshotValues final.external.runtime accounts final.external.balances)
    (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.storage.complete)
  obtain ⟨finalStore, completed⟩ := ContractLogCorrespondence.message_evaluates result final.external.runtime accounts address final.external.balances
    statusRelated (worldReference.prepend [frameResult]) (balancesReference.prepend [frameResult])
    (targetValue.prepend [frameResult]) (deployingValue.prepend [frameResult])
    (CodeValue.bound depth environment frameResult) worldFinal balancesFinal
  exact ⟨_, finalStore, .letE executed completed, accounts, represented, rfl⟩

end Solcore.Frontend.RustHull.ContractCodeCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeAccountInitializedEffects
/-! The public allocator supplies the balance ledger and separates it from
the mutable memory, storage and event cells used by execution. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeAccountInitializedEffects
open Correspondence ScalarExecution RuntimeInitializedEffects

structure Ready {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : StateReady cells store state}
    {words : LogsSemantics.Words} {cursor : Core.Word}
    (logs : RuntimeLogInitializedEffects.Ready runtime words cursor)
    (balances : StorageSemantics.Words) where
  layout : RuntimeAccountEffectsCorrespondence.Layout
  base : layout.toLogLayout = logs.layout
  balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ cells.map InitializedCell.effectSlot
  balancesRead : store.read? layout.balances = some (Core.WordMapping.encode balances)

theorem ready {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : StateReady cells store state}
    {words : LogsSemantics.Words} {cursor : Core.Word} {balances : StorageSemantics.Words}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots)
    (initialized : InitializedCells cells store) (separate : CellLocations cells)
    (logs : RuntimeLogInitializedEffects.Ready runtime words cursor)
    (observed : ∀ cell ∈ cells, cell.name = "balances" → cell.value = Core.WordMapping.encode balances) :
    Nonempty (Ready logs balances) := by
  obtain ⟨balance⟩ := RuntimeLogInitializedEffects.observe signature initialized
    (type := Core.WordMapping.type) (by simp [Effects.slots]) observed
  have outside : balance.cell.location ∉ RuntimeLogEffectsCorrespondence.mutable logs.layout := by
    intro inside
    rcases List.mem_cons.mp inside with same | inside
    · exact cell_location_ne separate balance.member logs.logsMember (by simp [balance.named]) same
    rcases List.mem_cons.mp inside with same | inside
    · exact cell_location_ne separate balance.member logs.logSizeMember (by simp [balance.named]) same
    rw [logs.base] at inside
    change balance.cell.location ∈ [runtime.memory, runtime.locations.memorySize] ++ runtime.locations.mutable at inside
    simp only [StorageBuiltinCorrespondence.Locations.mutable, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at inside
    rcases inside with (same | same) | same | same | same | same
    all_goals
      first
      | exact cell_location_ne separate balance.member runtime.memoryMember (by simp [balance.named]) same
      | exact cell_location_ne separate balance.member runtime.sizeMember (by simp [balance.named]) same
      | exact cell_location_ne separate balance.member runtime.worldMember (by simp [balance.named]) same
      | exact cell_location_ne separate balance.member runtime.exitMember (by simp [balance.named]) same
      | exact cell_location_ne separate balance.member runtime.offsetMember (by simp [balance.named]) same
      | exact cell_location_ne separate balance.member runtime.returnSizeMember (by simp [balance.named]) same
  let layout : RuntimeAccountEffectsCorrespondence.Layout := {
    toLogLayout := logs.layout
    balances := balance.cell.location
    balancesBelow := by
      change balance.cell.location < logs.layout.toLayout.boundary
      rw [logs.base]
      exact initialized.location_bound balance.member
    balancesOutside := outside }
  exact ⟨layout, rfl, balance.slot, balance.stored⟩

end Solcore.Frontend.RustHull.RuntimeAccountInitializedEffects
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeExtendedInitializedEffects
/-! Extra code-image cells preserve the existing initialized runtime resources.
The ordinary slot prefix supplies those resources; their members then lift to
the complete slot list without rebuilding the separation proofs. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeExtendedInitializedEffects
open Correspondence ScalarExecution RuntimeInitializedEffects

abbrev baseCells (cells : List InitializedCell) : List InitializedCell :=
  cells.take Effects.slots.length

theorem base_signature {cells : List InitializedCell} {extra : List (String × Core.Ty)}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots ++ extra) :
    (baseCells cells).map (fun cell => (cell.name, cell.type)) = Effects.slots := by
  rw [baseCells, List.map_take, signature, List.take_left]

theorem slot_inclusion {smaller larger : List InitializedCell}
    (included : ∀ cell ∈ smaller, cell ∈ larger) {slot : EffectSlot}
    (member : slot ∈ smaller.map InitializedCell.effectSlot) :
    slot ∈ larger.map InitializedCell.effectSlot := by
  obtain ⟨cell, present, rfl⟩ := List.mem_map.mp member
  exact List.mem_map_of_mem (included cell present)

/-- Enlarging the cell inventory does not change its represented resources. -/
def extendRuntime {smaller larger : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State}
    (included : ∀ cell ∈ smaller, cell ∈ larger) (ready : StateReady smaller store state) :
    StateReady larger store state where
  memory := ready.memory
  locations := ready.locations
  memoryMember := slot_inclusion included ready.memoryMember
  worldMember := slot_inclusion included ready.worldMember
  addressMember := slot_inclusion included ready.addressMember
  completeMember := slot_inclusion included ready.completeMember
  staticMember := slot_inclusion included ready.staticMember
  sizeMember := slot_inclusion included ready.sizeMember
  exitMember := slot_inclusion included ready.exitMember
  offsetMember := slot_inclusion included ready.offsetMember
  returnSizeMember := slot_inclusion included ready.returnSizeMember
  memoryRelated := ready.memoryRelated
  storageRelated := ready.storageRelated
  distinct := ready.distinct

def extendLogs {smaller larger : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : StateReady smaller store state}
    {words : LogsSemantics.Words} {cursor : Core.Word}
    (included : ∀ cell ∈ smaller, cell ∈ larger) (ready : RuntimeLogInitializedEffects.Ready runtime words cursor) :
    RuntimeLogInitializedEffects.Ready (extendRuntime included runtime) words cursor where
  layout := ready.layout
  base := ready.base
  logsMember := slot_inclusion included ready.logsMember
  logSizeMember := slot_inclusion included ready.logSizeMember
  logsRead := ready.logsRead
  logSizeRead := ready.logSizeRead

def extendAccounts {smaller larger : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : StateReady smaller store state}
    {words : LogsSemantics.Words} {cursor : Core.Word} {logs : RuntimeLogInitializedEffects.Ready runtime words cursor}
    {balances : StorageSemantics.Words}
    (included : ∀ cell ∈ smaller, cell ∈ larger) (ready : RuntimeAccountInitializedEffects.Ready logs balances) :
    RuntimeAccountInitializedEffects.Ready (extendLogs included logs) balances where
  layout := ready.layout
  base := ready.base
  balancesMember := slot_inclusion included ready.balancesMember
  balancesRead := ready.balancesRead

/-- The allocator's actual ordinary prefix provides memory, storage, events
and balances, even when code cells follow it. -/
theorem ready {cells : List InitializedCell} {store : Core.Store} {extra : List (String × Core.Ty)}
    {accounts : StorageCorrespondence.Accounts} {state : RuntimeEffectsSemantics.State}
    {words : LogsSemantics.Words} {cursor : Core.Word} {balances : StorageSemantics.Words}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots ++ extra)
    (initialized : InitializedCells cells store) (separate : CellLocations cells)
    (observed : ∀ cell ∈ cells, RuntimeInitializedEffects.Observed accounts state cell)
    (world : accounts.map Prod.fst = state.storage.world)
    (logsObserved : ∀ cell ∈ cells, cell.name = "logs" → cell.value = Core.WordMapping.encode words)
    (cursorObserved : ∀ cell ∈ cells, cell.name = "logSize" → cell.value = .word cursor)
    (balancesObserved : ∀ cell ∈ cells, cell.name = "balances" → cell.value = Core.WordMapping.encode balances) :
    ∃ runtime : StateReady cells store state,
      ∃ logs : RuntimeLogInitializedEffects.Ready runtime words cursor,
        Nonempty (RuntimeAccountInitializedEffects.Ready logs balances) := by
  have included : ∀ cell ∈ baseCells cells, cell ∈ cells := fun _ member => List.mem_of_mem_take member
  have baseInitialized : InitializedCells (baseCells cells) store := fun cell member => initialized cell (included cell member)
  have baseSeparate := separate.subset included
  obtain ⟨runtime⟩ := RuntimeInitializedEffects.state_ready (base_signature signature) baseInitialized baseSeparate
    (fun cell member => observed cell (included cell member)) world
  obtain ⟨logs⟩ := RuntimeLogInitializedEffects.ready (base_signature signature) baseInitialized baseSeparate runtime
    (fun cell member => logsObserved cell (included cell member))
    (fun cell member => cursorObserved cell (included cell member))
  obtain ⟨accounts⟩ := RuntimeAccountInitializedEffects.ready (base_signature signature) baseInitialized baseSeparate logs
    (fun cell member => balancesObserved cell (included cell member))
  exact ⟨extendRuntime included runtime, extendLogs included logs, ⟨extendAccounts included accounts⟩⟩

/-- These are exactly the two slot lists selected by the public compiler. -/
def slots (withCode : Bool) : List (String × Core.Ty) :=
  Effects.slots ++ if withCode then Effects.codeSlots else []

theorem slots_include (withCode : Bool) {slot : String × Core.Ty} (member : slot ∈ Effects.slots) :
    slot ∈ slots withCode := List.mem_append_left _ member

theorem code_member {slot : String × Core.Ty} (member : slot ∈ Effects.codeSlots) :
    slot ∈ slots true := List.mem_append_right _ member

theorem slots_allowed (withCode : Bool) {slot : String × Core.Ty} (member : slot ∈ slots withCode) :
    slot ∈ Effects.slots ++ Effects.codeSlots := by
  cases withCode with
  | false => exact List.mem_append_left _ (by simpa only [slots, Bool.false_eq_true, ↓reduceIte, List.append_nil] using member)
  | true => exact member

theorem slots_unique (withCode : Bool) : ((slots withCode).map Prod.fst).Nodup := by
  cases withCode <;> decide

theorem slots_separate (withCode : Bool) :
    ∀ slot ∈ slots withCode, slot.1.startsWith "function$" = false := by
  intro slot member
  apply String.startsWith_string_eq_false_iff.mpr
  have absent : ∀ slot ∈ slots withCode, ¬ ("function$".toList <+: slot.1.toList) := by
    cases withCode <;> decide
  exact absent slot member

theorem initialized_unique {cells : List InitializedCell} {withCode : Bool}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = slots withCode) :
    (cells.map InitializedCell.name).Nodup := by
  have names := congrArg (List.map Prod.fst) signature
  simp only [List.map_map, Function.comp_def] at names
  rw [names]
  exact slots_unique withCode

theorem initialized_separate {cells : List InitializedCell} {withCode : Bool}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = slots withCode) :
    EffectSlotsSeparate (cells.map InitializedCell.effectSlot) := by
  intro slot member
  obtain ⟨cell, cellMember, rfl⟩ := List.mem_map.mp member
  apply slots_separate withCode (cell.name, cell.type)
  rw [← signature]
  exact List.mem_map_of_mem cellMember

end Solcore.Frontend.RustHull.RuntimeExtendedInitializedEffects
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeReturnDataStateCorrespondence
/-! Return-data cells are caller resources. The baseline supplied to the older
runtime models observes their current source contents, and optional code cells
allow the same relation to cover frames without a linked code image. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeReturnDataEffectsCorrespondence
open Correspondence

structure CodeCells (base : RuntimeAccountEffectsCorrespondence.Layout) where
  code : Nat
  known : Nat
  codeBelow : code < base.boundary
  knownBelow : known < base.boundary
  codeOutside : code ∉ RuntimeLogEffectsCorrespondence.mutable base.toLogLayout
  knownOutside : known ∉ RuntimeLogEffectsCorrespondence.mutable base.toLogLayout

structure Layout extends toAccountLayout : RuntimeAccountEffectsCorrespondence.Layout where
  codeCells : Option (CodeCells toAccountLayout)
  returnData : Nat
  returnDataSize : Nat
  dataBelow : returnData < boundary
  sizeBelow : returnDataSize < boundary
  dataOutside : returnData ∉ RuntimeLogEffectsCorrespondence.mutable toLogLayout
  sizeOutside : returnDataSize ∉ RuntimeLogEffectsCorrespondence.mutable toLogLayout
  dataDistinct : returnData ≠ returnDataSize

def patched (layout : Layout) (baseline : Nat → Option Core.Value)
    (state : RuntimeReturnDataEffectsSemantics.State) (location : Nat) : Option Core.Value :=
  if location = layout.returnData then some (Core.WordMapping.encode state.returnData)
  else if location = layout.returnDataSize then some (.word (RuntimeReturnDataEffectsSemantics.size state))
  else baseline location

def CodeResources (layout : Layout) (image : Option (List UInt8)) (read : Nat → Option Core.Value) : Prop :=
  ∀ cells, layout.codeCells = some cells →
    read cells.code = some (Core.WordMapping.encode (Memory.packBytes (image.getD []))) ∧
    read cells.known = some (.bool image.isSome)

def Resources (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot)
    (image : Option (List UInt8)) (state : RuntimeReturnDataEffectsSemantics.State)
    (read : Nat → Option Core.Value) : Prop :=
  RuntimeAccountEffectsCorrespondence.Resources layout.toAccountLayout (patched layout baseline state) slots state.runtime read ∧
  read layout.returnData = some (Core.WordMapping.encode state.returnData) ∧
  read layout.returnDataSize = some (.word (RuntimeReturnDataEffectsSemantics.size state)) ∧
  CodeResources layout image read

def model (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot)
    (image : Option (List UInt8)) : StateModel RuntimeReturnDataEffectsSemantics.State :=
  StateModel.cutoff layout.boundary (Resources layout baseline slots image)

def sourceRuntime (state : Semantics.State RuntimeReturnDataEffectsSemantics.State) :
    Semantics.State RuntimeAccountEffectsSemantics.State := ⟨state.heap, state.external.runtime⟩

theorem account_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    {store : Core.Store} (related : StateRel (model layout baseline slots image) world state store) :
    StateRel (RuntimeAccountEffectsCorrespondence.model layout.toAccountLayout (patched layout baseline state.external) slots)
      world (sourceRuntime state) store :=
  ⟨related.toHeapRel, related.external.1, related.external.2.1, related.external.2.2.1⟩

theorem data_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    {store : Core.Store} (related : StateRel (model layout baseline slots image) world state store) :
    store.read? layout.returnData = some (Core.WordMapping.encode state.external.returnData) := by
  simpa only [prefixRead, layout.dataBelow, ↓reduceIte] using related.external.2.2.2.1

theorem size_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    {store : Core.Store} (related : StateRel (model layout baseline slots image) world state store) :
    store.read? layout.returnDataSize = some (.word (RuntimeReturnDataEffectsSemantics.size state.external)) := by
  simpa only [prefixRead, layout.sizeBelow, ↓reduceIte] using related.external.2.2.2.2.1

theorem code_related {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    {store : Core.Store} (related : StateRel (model layout baseline slots image) world state store)
    {cells : CodeCells layout.toAccountLayout} (present : layout.codeCells = some cells) :
    store.read? cells.code = some (Core.WordMapping.encode (Memory.packBytes (image.getD []))) ∧
    store.read? cells.known = some (.bool image.isSome) := by
  simpa only [prefixRead, cells.codeBelow, cells.knownBelow, ↓reduceIte]
    using related.external.2.2.2.2.2 cells present

theorem account_updated {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    {initial final : Core.Store} {runtime : RuntimeAccountEffectsSemantics.State}
    (before : StateRel (model layout baseline slots image) world state initial)
    (after : StateRel (RuntimeAccountEffectsCorrespondence.model layout.toAccountLayout
      (patched layout baseline state.external) slots) world {sourceRuntime state with external := runtime} final)
    (sizeEqual : runtime.runtime.runtime.environment.direct .returnDataSize =
      state.external.runtime.runtime.runtime.environment.direct .returnDataSize) :
    StateRel (model layout baseline slots image) world {state with external := {state.external with runtime := runtime}} final := by
  have patchEqual : patched layout baseline {state.external with runtime := runtime} = patched layout baseline state.external := by
    funext location
    simp only [patched, RuntimeReturnDataEffectsSemantics.size, sizeEqual]
  refine ⟨after.toHeapRel, after.external.1, after.external.2.1, ?_, ?_, ?_, ?_⟩
  · rw [patchEqual]
    exact after.external.2.2
  · rw [RuntimeLogEffectsCorrespondence.other_related
      (RuntimeAccountEffectsCorrespondence.runtime_related after) layout.dataOutside]
    simp [patched]
  · rw [RuntimeLogEffectsCorrespondence.other_related
      (RuntimeAccountEffectsCorrespondence.runtime_related after) layout.sizeOutside]
    simp [patched, Ne.symm layout.dataDistinct, RuntimeReturnDataEffectsSemantics.size, sizeEqual]
  · intro cells present
    rw [RuntimeLogEffectsCorrespondence.other_related
      (RuntimeAccountEffectsCorrespondence.runtime_related after) cells.codeOutside,
      RuntimeLogEffectsCorrespondence.other_related
      (RuntimeAccountEffectsCorrespondence.runtime_related after) cells.knownOutside,
      ← RuntimeLogEffectsCorrespondence.other_related
      (RuntimeAccountEffectsCorrespondence.runtime_related (account_related before)) cells.codeOutside,
      ← RuntimeLogEffectsCorrespondence.other_related
      (RuntimeAccountEffectsCorrespondence.runtime_related (account_related before)) cells.knownOutside]
    exact before.external.2.2.2.2.2 cells present

theorem memory_updated {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    {initial final : Core.Store} {memory : MemorySemantics.State}
    (before : StateRel (model layout baseline slots image) world state initial)
    (memoryAfter : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize memory final)
    (frame : MemoryCorrespondence.Frame layout.memory layout.storage.memorySize initial final) :
    StateRel (model layout baseline slots image) world
      {state with external := {state.external with runtime := RuntimeAccountEffectsSemantics.withMemory state.external.runtime memory}} final :=
  account_updated before (RuntimeAccountEffectsCorrespondence.memory_updated passive (account_related before) memoryAfter frame) rfl

theorem runtime_updated {layout : Layout} {baseline : Nat → Option Core.Value} {slots : List EffectSlot}
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {image : Option (List UInt8)} {world : World} {state : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    {initial final : Core.Store} {runtime : RuntimeEffectsSemantics.State}
    (before : StateRel (model layout baseline slots image) world state initial)
    (memoryAfter : MemoryCorrespondence.StateRel layout.memory layout.storage.memorySize runtime.memory final)
    (storageAfter : StorageBuiltinCorrespondence.StateRel layout.storage runtime.storage final)
    (frame : RuntimeEffectsCorrespondence.Frame layout.toLayout initial final) :
    StateRel (model layout baseline slots image) world
      {state with external := RuntimeReturnDataEffectsSemantics.withRuntime state.external runtime} final := by
  have accountBefore := account_related before
  have logBefore := RuntimeAccountEffectsCorrespondence.runtime_related accountBefore
  have environmentBefore := RuntimeLogEffectsCorrespondence.runtime_related logBefore
  have runtimeBefore := RuntimeEnvironmentEffectsCorrespondence.runtime_related environmentBefore
  have runtimeAfter := runtimeBefore.cutoff_effect (RuntimeEffectsCorrespondence.frame_above frame)
    (RuntimeEffectsCorrespondence.resources_preserved runtimeBefore.external.1 runtimeBefore.external.2.2 memoryAfter storageAfter frame)
  have environmentAfter := RuntimeEnvironmentEffectsCorrespondence.runtime_updated
    (RuntimeLogEffectsCorrespondence.passive_runtime passive) environmentBefore runtimeAfter
  have logAfter := RuntimeLogEffectsCorrespondence.runtime_updated environmentAfter
  exact account_updated before (RuntimeAccountEffectsCorrespondence.runtime_updated accountBefore logAfter) rfl

theorem initial_state {layout : Layout} {slots : List EffectSlot} {state : RuntimeReturnDataEffectsSemantics.State}
    {store : Core.Store} {image : Option (List UInt8)}
    (runtime : StateRel (RuntimeAccountEffectsCorrespondence.model layout.toAccountLayout
      (prefixRead layout.boundary store) slots) [] ⟨[], state.runtime⟩ store)
    (data : store.read? layout.returnData = some (Core.WordMapping.encode state.returnData))
    (size : store.read? layout.returnDataSize = some (.word (RuntimeReturnDataEffectsSemantics.size state)))
    (code : ∀ cells, layout.codeCells = some cells →
      store.read? cells.code = some (Core.WordMapping.encode (Memory.packBytes (image.getD []))) ∧
      store.read? cells.known = some (.bool image.isSome)) :
    StateRel (model layout (prefixRead layout.boundary store) slots image) [] ⟨[], state⟩ store := by
  have patchEqual : patched layout (prefixRead layout.boundary store) state = prefixRead layout.boundary store := by
    funext location
    unfold patched
    split
    · subst location
      simpa only [prefixRead, layout.dataBelow, ↓reduceIte] using data.symm
    · split
      · subst location
        simpa only [prefixRead, layout.sizeBelow, ↓reduceIte] using size.symm
      · rfl
  refine ⟨runtime.toHeapRel, runtime.external.1, runtime.external.2.1, ?_, ?_, ?_, ?_⟩
  · rw [patchEqual]
    exact runtime.external.2.2
  · simpa only [prefixRead, layout.dataBelow, ↓reduceIte] using data
  · simpa only [prefixRead, layout.sizeBelow, ↓reduceIte] using size
  · intro cells present
    simpa only [prefixRead, cells.codeBelow, cells.knownBelow, ↓reduceIte] using code cells present

end Solcore.Frontend.RustHull.RuntimeReturnDataEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeReturnDataSupported
/-! The return-data extension selects the existing runtime only for names that
it implements. Linked code copying additionally requires installed code slots. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeReturnDataEffectsCorrespondence
open Correspondence

def supported (slots : List EffectSlot) (withCode : Bool) (name : String) : Prop :=
  RuntimeAccountEffectsCorrespondence.supported slots name ∨
  (withCode = true ∧ ∃ operation : CodeImageSemantics.Operation, operation.name = name) ∨
  name = "returndatacopy" ∨ name = "memoryguard"

theorem primitive_none {slots : List EffectSlot} {withCode : Bool} {name : String}
    (enabled : supported slots withCode name) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = none := by
  rcases enabled with (((((((memory | storage) | environment) | logs) | termination) | copy) | hash) | account) | ⟨_, code⟩ | rfl | rfl
  · obtain ⟨operation, rfl⟩ := memory
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := storage
    cases operation with | load transient | store transient => cases transient <;> rfl
  · obtain ⟨operation, rfl, _⟩ := environment
    cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals rfl
  · obtain ⟨operation, rfl⟩ := logs
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := termination
    cases operation <;> rfl
  · obtain ⟨operation, rfl, _⟩ := copy
    cases operation <;> rfl
  · subst name
    rfl
  · obtain ⟨operation, rfl⟩ := account
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := code
    cases operation <;> rfl
  · rfl
  · rfl

private theorem runtime_new_unsupported {image : Option (List UInt8)} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : RuntimeCodeEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (newName : name = "returndatacopy" ∨ name = "memoryguard")
    (computed : RuntimeCodeEffectsSemantics.Builtin image name type arguments initial result final) : False := by
  cases computed with
  | copy computed =>
      obtain ⟨operation, named⟩ := computed.named
      rcases newName with rfl | rfl <;> cases operation <;>
        simp [CodeImageSemantics.Operation.name] at named
  | runtime computed =>
      cases computed with
      | observation computed =>
          obtain ⟨operation, named⟩ := computed.named
          rcases newName with rfl | rfl <;> cases operation <;>
            simp [AccountObservationSemantics.Operation.name] at named
      | runtime computed =>
          cases computed with
          | hash computed =>
              cases computed
              simp at newName
          | runtime computed =>
              cases computed with
              | copy computed =>
                  cases computed <;> simp at newName
              | runtime computed =>
                  cases computed with
                  | termination computed =>
                      have missing : TerminationSemantics.builtin name type arguments initial.runtime.runtime.runtime = none := by
                        rcases newName with rfl | rfl <;> rfl
                      rw [missing] at computed
                      contradiction
                  | runtime computed =>
                      cases computed with
                      | logs computed =>
                          cases computed with
                          | log operation _ _ _ _ _ _ =>
                              rcases newName with named | named <;> cases operation <;>
                                simp [LogsSemantics.Operation.name] at named
                      | runtime computed =>
                          have missing : RuntimeEnvironmentEffectsSemantics.builtin name type arguments initial.runtime.runtime = none := by
                            rcases newName with rfl | rfl <;> rfl
                          rw [missing] at computed
                          contradiction

theorem runtime_enabled {slots : List EffectSlot} {withCode : Bool} {image : Option (List UInt8)}
    {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : RuntimeCodeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (enabled : supported slots withCode name)
    (computed : RuntimeCodeEffectsSemantics.Builtin image name type arguments initial result final) :
    RuntimeCodeEffectsCorrespondence.supported slots name := by
  rcases enabled with account | ⟨_, code⟩ | copying | guard
  · exact .inl account
  · exact .inr code
  · exact False.elim (runtime_new_unsupported (.inl copying) computed)
  · exact False.elim (runtime_new_unsupported (.inr guard) computed)

theorem account_enabled {slots : List EffectSlot} {image : Option (List UInt8)}
    {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : RuntimeCodeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (enabled : supported slots false name)
    (computed : RuntimeCodeEffectsSemantics.Builtin image name type arguments initial result final) :
    RuntimeAccountEffectsCorrespondence.supported slots name := by
  rcases enabled with account | ⟨impossible, _⟩ | copying | guard
  · exact account
  · cases impossible
  · exact False.elim (runtime_new_unsupported (.inl copying) computed)
  · exact False.elim (runtime_new_unsupported (.inr guard) computed)

theorem code_unsupported {slots : List EffectSlot} (operation : CodeImageSemantics.Operation)
    (enabled : RuntimeAccountEffectsCorrespondence.supported slots operation.name) : False := by
  rcases enabled with ((((((memory | storage) | environment) | logs) | termination) | copy) | hash) | account
  · obtain ⟨other, named⟩ := memory
    cases operation <;> cases other <;> simp [CodeImageSemantics.Operation.name, MemoryBuiltinCorrespondence.Operation.name] at named
  · obtain ⟨other, named⟩ := storage
    cases other with
    | load transient | store transient =>
      cases operation <;> cases transient <;> simp [CodeImageSemantics.Operation.name, StorageBuiltinCorrespondence.Operation.name] at named
  · obtain ⟨other, named, _⟩ := environment
    cases other <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals cases operation <;> simp [CodeImageSemantics.Operation.name, EnvironmentSemantics.Operation.name,
      EnvironmentSemantics.Direct.name, EnvironmentSemantics.AmbientWord.name] at named
  · obtain ⟨other, named⟩ := logs
    cases operation <;> cases other <;> simp [CodeImageSemantics.Operation.name, LogsSemantics.Operation.name] at named
  · obtain ⟨other, named⟩ := termination
    cases operation <;> cases other <;> simp [CodeImageSemantics.Operation.name, TerminationSemantics.Operation.name] at named
  · obtain ⟨other, named, _⟩ := copy
    cases operation <;> cases other <;> simp [CodeImageSemantics.Operation.name, MemoryCopySemantics.Operation.name] at named
  · cases operation <;> simp [CodeImageSemantics.Operation.name] at hash
  · obtain ⟨other, named⟩ := account
    cases operation <;> cases other <;> simp [CodeImageSemantics.Operation.name, AccountObservationSemantics.Operation.name] at named

end Solcore.Frontend.RustHull.RuntimeReturnDataEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeReturnDataEffectsCorrespondence
/-! Caller return data, optional code images, and existing runtime effects are
connected to the actual compiler and recursive Hull execution in one model. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeReturnDataEffectsCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (image : Option (List UInt8)) (withCode : Bool) (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
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
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (codeMembers : ∀ cells, layout.codeCells = some cells →
      (⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots))
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode) :
    ExternalCallPreservation (supported slots withCode) (model layout baseline slots image) slots
      (RuntimeReturnDataEffectsSemantics.effects image) := by
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | runtime computed =>
          have sizeEqual := congrArg (fun environment => environment.direct .returnDataSize)
            (RuntimeReturnDataEffectsSemantics.runtime_environment computed)
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          cases present : layout.codeCells with
          | some cells =>
              let codeLayout : RuntimeCodeEffectsCorrespondence.Layout :=
                { toAccountLayout := layout.toAccountLayout
                  code := cells.code, known := cells.known
                  codeBelow := cells.codeBelow, knownBelow := cells.knownBelow
                  codeOutside := cells.codeOutside, knownOutside := cells.knownOutside }
              have beforeAccount := account_related state
              have codeState : StateRel (RuntimeCodeEffectsCorrespondence.model codeLayout
                  (patched layout baseline initial.external) slots image) world (sourceRuntime initial) argumentStore :=
                ⟨beforeAccount.toHeapRel, beforeAccount.external.1, beforeAccount.external.2.1,
                  beforeAccount.external.2.2, state.external.2.2.2.2.2 cells present⟩
              have call : Semantics.EvalCall functions (RuntimeCodeEffectsSemantics.effects image) name type sources
                  (sourceRuntime initial) result _ := .external absent notPrimitive computed
              obtain ⟨target, finalStore, resultRelated, evaluated, finalState, installedFinal, retained⟩ :=
                RuntimeCodeEffectsCorrespondence.external_preserves codeLayout
                  (patched layout baseline initial.external) slots image passive
                  memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
                  logsMember logSizeMember balancesMember (codeMembers cells present).1 (codeMembers cells present).2
                  (runtime_enabled enabled computed) notFunction call typeCompiled compiled related packed runtime codeState installed
              exact ⟨target, finalStore, resultRelated, evaluated,
                account_updated state (RuntimeCodeEffectsCorrespondence.account_related finalState) sizeEqual,
                installedFinal, retained⟩
          | none =>
              have disabled : withCode = false := by simpa only [present, Option.isSome_none] using mode.symm
              have accountEnabled := account_enabled (disabled ▸ enabled) computed
              cases computed with
              | runtime computed =>
                  have call : Semantics.EvalCall functions RuntimeAccountEffectsSemantics.effects name type sources
                      (sourceRuntime initial) result _ := .external absent notPrimitive computed
                  obtain ⟨target, finalStore, resultRelated, evaluated, finalState, installedFinal, retained⟩ :=
                    RuntimeAccountEffectsCorrespondence.external_preserves layout.toAccountLayout
                      (patched layout baseline initial.external) slots passive
                      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
                      logsMember logSizeMember balancesMember accountEnabled notFunction call typeCompiled compiled related packed runtime
                      (account_related state) installed
                  exact ⟨target, finalStore, resultRelated, evaluated, account_updated state finalState sizeEqual,
                    installedFinal, retained⟩
              | copy computed =>
                  obtain ⟨operation, named⟩ := computed.named
                  subst name
                  exact False.elim (code_unsupported operation accountEnabled)
      | copy computed =>
          have named := computed.named
          subst name
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          have beforeAccount := account_related state
          have beforeLog := RuntimeAccountEffectsCorrespondence.runtime_related beforeAccount
          have beforeEnvironment := RuntimeLogEffectsCorrespondence.runtime_related beforeLog
          have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related beforeEnvironment
          obtain ⟨target, finalStore, resultRelated, evaluated, memoryFinal, storageFinal, frame, retained⟩ :=
            ReturnDataBuiltinCorrespondence.preserves compiled computed related runtime
              memoryMember memorySizeMember exitMember offsetMember sizeMember dataMember dataSizeMember
              (data_related state) (size_related state)
              (RuntimeEffectsCorrespondence.memory_related beforeRuntime)
              (RuntimeEffectsCorrespondence.storage_related beforeRuntime) packed
          exact ⟨target, finalStore, resultRelated, evaluated,
            runtime_updated passive state memoryFinal storageFinal frame, installed.preserved retained, retained⟩
      | guard computed =>
          have named := computed.named
          subst name
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          obtain ⟨target, resultRelated, evaluated⟩ := MemoryGuardBuiltinCorrespondence.preserves compiled computed related packed
          exact ⟨target, argumentStore, resultRelated, evaluated, state, installed, ClosuresPreserved.refl _⟩

theorem assemble_program (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (image : Option (List UInt8)) (withCode : Bool) (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
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
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (codeMembers : ∀ cells, layout.codeCells = some cells →
      (⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots))
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode)
    {functions : List Function} {function : Function} {entry : String} {runtime : Scope}
    {fuel : Nat} {own : Signature} {allocated : Core.Expr}
    (accepted : assemble functions entry runtime fuel = .ok (own, allocated))
    (selected : functions.find? (·.name == entry) = some function)
    (eligible : ExecutableProgram (supported slots withCode) functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State RuntimeReturnDataEffectsSemantics.State}
    {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions (RuntimeReturnDataEffectsSemantics.effects image)
      function sources initial sourceResult final)
    {world : World} {runtimeValues caller : Core.Environment} {store : Core.Store}
    (runtimeLength : runtimeValues.length = runtime.length)
    (covered : ScopeCoverage [] runtime)
    (runtimeRelated : EffectEnvironmentRel slots runtime Core.Renaming.id
      (runtimeValues ++ bundleValues targets :: caller))
    (separated : EffectSlotsSeparate slots)
    (state : StateRel (model layout baseline slots image) world initial store) :
    ∃ extension target finalStore,
      ResultRel own.result sourceResult target ∧
      Core.Evaluates (runtimeValues ++ bundleValues targets :: caller) store allocated target finalStore ∧
      StateRel (model layout baseline slots image) (world ++ extension) final finalStore ∧
      ClosuresPreserved store finalStore :=
  assemble_recursive_program_effects accepted selected
    (external_preserves layout baseline slots image withCode passive memoryMember worldMember addressMember completeMember staticMember
      memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode) eligible values evaluated
    runtimeLength covered runtimeRelated separated state


end Solcore.Frontend.RustHull.RuntimeReturnDataEffectsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeReturnDataEffectsFrameCorrespondence
/-! Source return-data operations reach actual frame calls and final snapshots.
The same proof covers ordinary frames and frames with linked code slots. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeReturnDataEffectsFrameCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeReturnDataEffectsCorrespondence (Layout model account_related)
open RuntimeAccountEffectsCorrespondence (runtime_related balances_related)
open RuntimeReturnDataEffectsCorrespondence (supported assemble_program)

abbrev slotTypes := RuntimeLogEffectsFrameCorrespondence.slotTypes
abbrev cell_observed := @RuntimeLogEffectsFrameCorrespondence.cell_observed
def snapshotValues (state : RuntimeReturnDataEffectsSemantics.State) :=
  RuntimeAccountEffectsFrameCorrespondence.snapshotValues state.runtime

/-- A frame installed earlier retains its captured environment. The body and
completion wrapper observe the final source world and balances through the
compiler's actual frame references. -/
theorem compileFrame_call_preserves_observed {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout} {image : Option (List UInt8)}
    {initial : RuntimeReturnDataEffectsSemantics.State}
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
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (codeMembers : ∀ cells, layout.codeCells = some cells →
      ⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots)
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots image) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {final : Semantics.State RuntimeReturnDataEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeReturnDataEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots image)
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
    assemble_program layout (prefixRead layout.boundary store) slots image withCode passive
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode assembled selected eligible argumentValues evaluated
      (runtimeValues := values.reverse) (caller := bundleValues values :: captured)
      (by simpa [AccountRuntime.frameScope, slotTypes, MemoryFrameCorrespondence.slotTypes] using length)
      (MemoryFrameCorrespondence.frame_coverage _) runtime separated
      initialRelated
  have finalStorage := RuntimeEffectsCorrespondence.storage_related
    (RuntimeEnvironmentEffectsCorrespondence.runtime_related (RuntimeLogEffectsCorrespondence.runtime_related (runtime_related (account_related state))))
  have finalLogs := RuntimeLogEffectsCorrespondence.logs_related (runtime_related (account_related state))
  obtain ⟨accounts, sourceWorld, worldRead⟩ := finalStorage.world
  have finalWorld := cell_observed references runtime worldMember worldRead
  have finalAddress := cell_observed references runtime addressMember finalStorage.address
  have finalComplete := cell_observed references runtime completeMember finalStorage.complete
  have finalSnapshot : ∀ name ∈ frameSnapshotNames,
      FrameCellObserved cells (values.reverse ++ .unit :: bundleValues values :: captured)
        bodyStore name (snapshotValues final.external accounts name) := by
    intro name member
    simp [frameSnapshotNames] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cell_observed references runtime exitMember finalStorage.exit
    · exact cell_observed references runtime offsetMember finalStorage.returnOffset
    · exact cell_observed references runtime sizeMember finalStorage.returnSize
    · exact cell_observed references runtime memoryMember finalLogs.logs.memory
    · exact cell_observed references runtime logsMember finalLogs.logs.logs
    · exact cell_observed references runtime logSizeMember finalLogs.logs.logSize
    · exact cell_observed references runtime balancesMember (balances_related (account_related state))
    · exact finalWorld
  have completed := frameCompletion_evaluates executed accounts final.external.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.storage.complete
    finalWorld finalAddress finalComplete finalSnapshot
  obtain ⟨suffix, _, extended⟩ := StorageCorrespondence.getStore_extension accounts
    final.external.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.storage.complete
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
    {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout} {image : Option (List UInt8)}
    {initial : RuntimeReturnDataEffectsSemantics.State}
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
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (codeMembers : ∀ cells, layout.codeCells = some cells →
      ⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots)
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots image) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {final : Semantics.State RuntimeReturnDataEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeReturnDataEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment before (.apply function argument)
        (frameCompletionValue status (snapshotValues final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots image)
        extension final finalStore := by
  obtain ⟨extension, status, accounts, finalStore, represented, related, executed, state, _⟩ :=
    compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length runtime separated
      memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode initialRelated passive evaluated
  exact ⟨extension, status, accounts, finalStore, represented, related, executed, state⟩

/-- Direct evaluation of freshly compiled frame code is a special case of the
same theorem for captured calls. -/
theorem compileFrame_preserves {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (slotTypes slots) fuel = .ok compiled)
    (eligible : ExecutableProgram (supported slots withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : Layout} {image : Option (List UInt8)}
    {initial : RuntimeReturnDataEffectsSemantics.State}
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
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (codeMembers : ∀ cells, layout.codeCells = some cells →
      ⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots)
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode)
    (initialRelated : StateRel (model layout (prefixRead layout.boundary store) slots image) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {final : Semantics.State RuntimeReturnDataEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeReturnDataEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final) :
    ∃ extension status accounts finalStore,
      accounts.map Prod.fst = final.external.runtime.runtime.runtime.runtime.storage.world ∧
      ResultRel .unit result status ∧
      Core.Evaluates environment initialStore (.apply compiled argument)
        (frameCompletionValue status (snapshotValues final.external accounts)
          (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.storage.complete)) finalStore ∧
      StateRel (model layout (prefixRead layout.boundary store) slots image)
        extension final finalStore := by
  obtain ⟨own, body, cells, _, _, rfl⟩ := compileFrame_components accepted
  exact compileFrame_call_preserves accepted eligible (CapturedClosure.lambda _ _ _ environment)
    Core.Evaluates.lambda supplied length runtime separated memoryMember worldMember addressMember completeMember
    staticMember memorySizeMember exitMember offsetMember sizeMember logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode initialRelated passive
    evaluated

end Solcore.Frontend.RustHull.RuntimeReturnDataEffectsFrameCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContractReturnDataCorrespondence
/-! Return-data bounds and identity observations reach actual message
completion with or without linked code cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractReturnDataCorrespondence
open Correspondence ScalarExecution CodeBuilder

def supported (withCode : Bool) (name : String) : Prop :=
  (if withCode then ContractCodeCorrespondence.supported name else ContractAccountCorrespondence.supported name) ∨
    name = "returndatacopy" ∨ name = "memoryguard"

theorem supported_actual {slots : List EffectSlot} {withCode : Bool}
    (signature : RuntimeEffectsFrameCorrespondence.slotTypes slots = RuntimeExtendedInitializedEffects.slots withCode) :
    RuntimeReturnDataEffectsCorrespondence.supported slots withCode = supported withCode := by
  funext name
  apply propext
  cases withCode with
  | false =>
      have base := congrFun (ContractAccountCorrespondence.supported_actual (by simpa [RuntimeExtendedInitializedEffects.slots] using signature)) name
      simp only [RuntimeReturnDataEffectsCorrespondence.supported, supported, Bool.false_eq_true, ↓reduceIte, false_and, false_or, base]
  | true =>
      have base := congrFun (ContractCodeCorrespondence.supported_actual (by simpa [RuntimeExtendedInitializedEffects.slots] using signature)) name
      simp only [RuntimeCodeEffectsCorrespondence.supported] at base
      simp only [RuntimeReturnDataEffectsCorrespondence.supported, supported, ↓reduceIte, true_and]
      rw [← base]
      simp only [or_assoc]

def messageValue (result : Semantics.Result Semantics.Value) (state : RuntimeReturnDataEffectsSemantics.State)
    (accounts : StorageCorrespondence.Accounts) (target : Core.Word) : Core.Value :=
  ContractAccountCorrespondence.messageValue result state.runtime accounts target

def MessageRel (result : Semantics.Result Semantics.Value) (state : RuntimeReturnDataEffectsSemantics.State)
    (target : Core.Word) (value : Core.Value) : Prop :=
  ContractAccountCorrespondence.MessageRel result state.runtime target value

theorem frameCall_message_evaluates {program : Program} {code : CodeBlock} {slots : List EffectSlot}
    {fuel : Nat} {compiled : Core.Expr} {withCode : Bool}
    (accepted : AccountRuntime.compileFrame program code (RuntimeLogEffectsFrameCorrespondence.slotTypes slots) fuel = .ok compiled)
    (eligible : DerivationCorrespondence.ExecutableProgram (RuntimeReturnDataEffectsCorrespondence.supported slots withCode)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {layout : RuntimeReturnDataEffectsCorrespondence.Layout} {image : Option (List UInt8)}
    {initial : RuntimeReturnDataEffectsSemantics.State}
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
    (balancesMember : ⟨"balances", Core.WordMapping.type, layout.balances⟩ ∈ slots)
    (codeMembers : ∀ cells, layout.codeCells = some cells →
      ⟨"code", Core.WordMapping.type, cells.code⟩ ∈ slots ∧ ⟨"codeKnown", .bool, cells.known⟩ ∈ slots)
    (dataMember : ⟨"returnData", Core.WordMapping.type, layout.returnData⟩ ∈ slots)
    (dataSizeMember : ⟨"returnDataSize", .word, layout.returnDataSize⟩ ∈ slots)
    (mode : layout.codeCells.isSome = withCode)
    (initialRelated : StateRel (RuntimeReturnDataEffectsCorrespondence.model layout (prefixRead layout.boundary store) slots image) [] ⟨[], initial⟩ store)
    (passive : RuntimeLogEffectsCorrespondence.Passive layout.toLogLayout slots)
    {final : Semantics.State RuntimeReturnDataEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeReturnDataEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], initial⟩ result final)
    (address : Core.Word)
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type layout.storage.world))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type layout.balances))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false)) :
    ∃ value finalStore, Core.Evaluates environment before
      (bind (apply function argument) (fun framed => AccountRuntime.completeMessage shared images target deploying framed) depth)
      value finalStore ∧ MessageRel result final.external address value := by
  obtain ⟨extension, status, accounts, bodyStore, represented, statusRelated, executed, related, worldFinal⟩ :=
    RuntimeReturnDataEffectsFrameCorrespondence.compileFrame_call_preserves_observed accepted eligible closureRelated resolved supplied length
      runtime separated memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      logsMember logSizeMember balancesMember codeMembers dataMember dataSizeMember mode initialRelated passive evaluated
  have balancesFinal := RuntimeAccountEffectsCorrespondence.balances_related (RuntimeReturnDataEffectsCorrespondence.account_related related)
  let frameResult := frameCompletionValue status (ContractLogCorrespondence.snapshotValues final.external.runtime.runtime accounts final.external.runtime.balances)
    (StorageCorrespondence.get accounts final.external.runtime.runtime.runtime.runtime.storage.address final.external.runtime.runtime.runtime.runtime.storage.complete)
  obtain ⟨finalStore, completed⟩ := ContractLogCorrespondence.message_evaluates result final.external.runtime.runtime accounts address final.external.runtime.balances
    statusRelated (worldReference.prepend [frameResult]) (balancesReference.prepend [frameResult])
    (targetValue.prepend [frameResult]) (deployingValue.prepend [frameResult])
    (CodeValue.bound depth environment frameResult) worldFinal balancesFinal
  exact ⟨_, finalStore, .letE executed completed, accounts, represented, rfl⟩

end Solcore.Frontend.RustHull.ContractReturnDataCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCodeInitializedEffects
/-! Actual code-image allocations extend the account layout. Their bounds and
separation follow from the same named cells as the existing runtime resources. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCodeInitializedEffects
open Correspondence ScalarExecution RuntimeInitializedEffects

structure Ready {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : StateReady cells store state}
    {words : LogsSemantics.Words} {cursor : Core.Word} {logs : RuntimeLogInitializedEffects.Ready runtime words cursor}
    {balances : StorageSemantics.Words} (accounts : RuntimeAccountInitializedEffects.Ready logs balances)
    (image : Option (List UInt8)) where
  layout : RuntimeCodeEffectsCorrespondence.Layout
  base : layout.toAccountLayout = accounts.layout
  codeMember : ⟨"code", Core.WordMapping.type, layout.code⟩ ∈ cells.map InitializedCell.effectSlot
  knownMember : ⟨"codeKnown", .bool, layout.known⟩ ∈ cells.map InitializedCell.effectSlot
  readCode : store.read? layout.code = some (Core.WordMapping.encode (Memory.packBytes (image.getD [])))
  readKnown : store.read? layout.known = some (.bool image.isSome)

theorem observe {cells : List InitializedCell} {store : Core.Store}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots ++ Effects.codeSlots)
    (initialized : InitializedCells cells store)
    {name : String} {type : Core.Ty} {value : Core.Value}
    (member : (name, type) ∈ Effects.codeSlots)
    (observed : ∀ cell ∈ cells, cell.name = name → cell.value = value) :
    Nonempty (Cell cells store name type value) := by
  have present := List.mem_append_right Effects.slots member
  rw [← signature] at present
  obtain ⟨cell, cellMember, same⟩ := List.mem_map.mp present
  obtain ⟨named, typed⟩ := Prod.mk.inj same
  exact ⟨cell, cellMember, named, typed,
    by simpa only [observed cell cellMember named] using initialized cell cellMember⟩

theorem slot_typed {cells : List InitializedCell} {slot : EffectSlot}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots ++ Effects.codeSlots)
    (member : slot ∈ cells.map InitializedCell.effectSlot) :
    (slot.name, slot.type) ∈ Effects.slots ++ Effects.codeSlots := by
  obtain ⟨cell, cellMember, rfl⟩ := List.mem_map.mp member
  rw [← signature]
  exact List.mem_map_of_mem cellMember

/-- The code and availability cells are passive resources of the actual
frame, including when only the catalog supplies a linked image. -/
theorem ready {cells : List InitializedCell} {store : Core.Store}
    {state : RuntimeEffectsSemantics.State} {runtime : StateReady cells store state}
    {words : LogsSemantics.Words} {cursor : Core.Word} {logs : RuntimeLogInitializedEffects.Ready runtime words cursor}
    {balances : StorageSemantics.Words} {image : Option (List UInt8)}
    (signature : cells.map (fun cell => (cell.name, cell.type)) = Effects.slots ++ Effects.codeSlots)
    (initialized : InitializedCells cells store) (separate : CellLocations cells)
    (accounts : RuntimeAccountInitializedEffects.Ready logs balances)
    (codeObserved : ∀ cell ∈ cells, cell.name = "code" →
      cell.value = Core.WordMapping.encode (Memory.packBytes (image.getD [])))
    (knownObserved : ∀ cell ∈ cells, cell.name = "codeKnown" → cell.value = .bool image.isSome) :
    Nonempty (Ready accounts image) := by
  obtain ⟨code⟩ := observe signature initialized (type := Core.WordMapping.type) (by simp [Effects.codeSlots]) codeObserved
  obtain ⟨known⟩ := observe signature initialized (type := .bool) (by simp [Effects.codeSlots]) knownObserved
  obtain ⟨codeSlot, codeMember, codeName, codeOutside, codeBelow, codeRead⟩ :=
    logs.passive_cell separate initialized code.member (by rw [code.named]; decide)
  obtain ⟨knownSlot, knownMember, knownName, knownOutside, knownBelow, knownRead⟩ :=
    logs.passive_cell separate initialized known.member (by rw [known.named]; decide)
  have codeName : codeSlot.name = "code" := codeName.trans code.named
  have knownName : knownSlot.name = "codeKnown" := knownName.trans known.named
  have codeTyped : codeSlot.type = Core.WordMapping.type := by
    have types : ∀ slot ∈ Effects.slots ++ Effects.codeSlots, slot.1 = "code" → slot.2 = Core.WordMapping.type := by decide
    exact types _ (slot_typed signature codeMember) codeName
  have knownTyped : knownSlot.type = .bool := by
    have types : ∀ slot ∈ Effects.slots ++ Effects.codeSlots, slot.1 = "codeKnown" → slot.2 = .bool := by decide
    exact types _ (slot_typed signature knownMember) knownName
  let layout : RuntimeCodeEffectsCorrespondence.Layout := {
    toAccountLayout := accounts.layout
    code := codeSlot.location
    known := knownSlot.location
    codeBelow := by change codeSlot.location < accounts.layout.toLogLayout.boundary; rw [accounts.base]; exact codeBelow
    knownBelow := by change knownSlot.location < accounts.layout.toLogLayout.boundary; rw [accounts.base]; exact knownBelow
    codeOutside := by change codeSlot.location ∉ RuntimeLogEffectsCorrespondence.mutable accounts.layout.toLogLayout; rw [accounts.base]; exact codeOutside
    knownOutside := by change knownSlot.location ∉ RuntimeLogEffectsCorrespondence.mutable accounts.layout.toLogLayout; rw [accounts.base]; exact knownOutside }
  refine ⟨layout, rfl, ?_, ?_, ?_, ?_⟩
  · simpa only [layout, ← codeName, ← codeTyped] using codeMember
  · simpa only [layout, ← knownName, ← knownTyped] using knownMember
  · simpa only [codeObserved code.cell code.member code.named] using codeRead
  · simpa only [knownObserved known.cell known.member known.named] using knownRead

end Solcore.Frontend.RustHull.RuntimeCodeInitializedEffects
end
