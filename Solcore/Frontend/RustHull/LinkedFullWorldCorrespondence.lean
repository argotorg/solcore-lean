import Solcore.Frontend.RustHull.LinkedLogWorldCorrespondence
import Solcore.Frontend.RustHull.RuntimeFullEffectsCorrespondence
import Solcore.Frontend.RustHull.ReadOnlyWorldBuiltinCorrespondence

set_option autoImplicit false
set_option linter.unusedVariables false
namespace Solcore.Frontend.RustHull.LinkedFullWorldCorrespondence
open Correspondence DerivationCorrespondence ScalarExecution RuntimeFullEffectsCorrespondence LinkedBuiltinWorldCorrespondence
open RuntimeLogEffectsCorrespondence (Layout model Passive)

private theorem primitive_none {slots : List EffectSlot} {name : String}
    (enabled : supported slots name) (type : Ty) (arguments : List Semantics.Value) :
    Semantics.primitive? name type arguments = none := by
  rcases enabled with (((memory | storage) | environment) | logs) | ⟨operation, rfl⟩
  · obtain ⟨operation, rfl⟩ := memory
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := storage
    cases operation with | load transient | store transient => cases transient <;> rfl
  · obtain ⟨operation, rfl, _⟩ := environment
    cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals rfl
  · obtain ⟨operation, rfl⟩ := logs
    cases operation <;> rfl
  · cases operation <;> rfl

private theorem termination_unsupported {slots : List EffectSlot} {name : String}
    (enabled : RuntimeLogEffectsCorrespondence.supported slots name)
    (type : Ty) (arguments : List Semantics.Value) (state : RuntimeEffectsSemantics.State) :
    TerminationSemantics.builtin name type arguments state = none := by
  rcases enabled with ((memory | storage) | environment) | ⟨operation, rfl⟩
  · obtain ⟨operation, rfl⟩ := memory
    cases operation <;> rfl
  · obtain ⟨operation, rfl⟩ := storage
    cases operation with | load transient | store transient => cases transient <;> rfl
  · obtain ⟨operation, rfl, _⟩ := environment
    cases operation <;> (try first | cases ‹EnvironmentSemantics.Direct› | cases ‹EnvironmentSemantics.AmbientWord›)
    all_goals rfl
  · cases operation <;> rfl

private theorem log_named {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : LogsSemantics.State} {result : Semantics.Result Semantics.Value}
    (computed : LogsSemantics.Builtin name type arguments initial result final) :
    ∃ operation : LogsSemantics.Operation, operation.name = name := by
  cases computed with | log operation _ _ _ _ _ _ => exact ⟨operation, rfl⟩

private theorem runtime_unsupported (operation : TerminationSemantics.Operation)
    {type : Ty} {arguments : List Semantics.Value} {initial final : RuntimeLogEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (computed : RuntimeLogEffectsSemantics.Builtin operation.name type arguments initial result final) : False := by
  cases computed with
  | runtime computed =>
      have missing : RuntimeEnvironmentEffectsSemantics.builtin operation.name type arguments initial.runtime = none := by
        cases operation <;> rfl
      rw [missing] at computed
      contradiction
  | logs computed =>
      obtain ⟨log, named⟩ := log_named computed
      cases log <;> cases operation <;> simp [LogsSemantics.Operation.name, TerminationSemantics.Operation.name] at named

theorem external_preserves (layout : RuntimeLogEffectsCorrespondence.Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot) (passive : RuntimeLogEffectsCorrespondence.Passive layout slots)
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
    ∀ anchors, ExternalWorldPreservation (supported slots) (model layout baseline slots) slots RuntimeFullEffectsSemantics.effects
      anchors layout.storage.world (fun state => state.runtime.runtime.storage.world) := by
  intro anchors
  intro functions name type sources initial final result enabled notFunction called
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed => rw [primitive_none enabled] at computed; contradiction
  | external absent notPrimitive computed =>
      cases computed with
      | runtime computed =>
          have runtimeEnabled : RuntimeLogEffectsCorrespondence.supported slots name := by
            rcases enabled with runtime | ⟨operation, rfl⟩
            · exact runtime
            · exact False.elim (runtime_unsupported operation computed)
          have call : Semantics.EvalCall functions RuntimeLogEffectsSemantics.effects name type sources initial result _ :=
            .external absent notPrimitive computed
          intro typeFuel expected typeCompiled
          exact LinkedLogWorldCorrespondence.external_preserves layout baseline slots passive
            memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
            logsMember logSizeMember anchors runtimeEnabled notFunction call typeCompiled
      | @termination finalRuntime computed =>
          have terminationEnabled : TerminationEffectCorrespondence.supported name := by
            rcases enabled with runtime | termination
            · rw [termination_unsupported runtime] at computed
              contradiction
            · exact termination
          obtain ⟨operation, rfl⟩ := terminationEnabled
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed linked
          have beforeRuntime := RuntimeEnvironmentEffectsCorrespondence.runtime_related (RuntimeLogEffectsCorrespondence.runtime_related state)
          obtain ⟨computedResult, computedState, target, finalStore, meaning, resultRelated, evaluated, memoryFinal, storageFinal, frame, retained, preserved⟩ :=
            ReadOnlyWorldBuiltinCorrespondence.Termination.preserves operation compiled related runtime
              memorySizeMember exitMember offsetMember sizeMember
              (RuntimeEffectsCorrespondence.memory_related beforeRuntime)
              (RuntimeEffectsCorrespondence.storage_related beforeRuntime) packed type
          have unchanged : ∀ (state : RuntimeEffectsSemantics.State) kind offset length,
              (TerminationSemantics.terminate state kind offset length).2.storage.world = state.storage.world := by
            intro state kind offset length
            unfold TerminationSemantics.terminate
            split <;> rfl
          have worldSame : computedState.storage.world = initial.external.runtime.runtime.storage.world := by
            cases operation <;> simp [TerminationSemantics.builtin, TerminationSemantics.Operation.name] at meaning
            all_goals split at meaning
            all_goals try contradiction
            all_goals have changed := congrArg (fun output => output.2.storage.world) (Option.some.inj meaning)
            all_goals simpa only [unchanged, RuntimeEnvironmentEffectsCorrespondence.sourceRuntime, RuntimeLogEffectsCorrespondence.sourceRuntime] using changed.symm
          have same := Option.some.inj (computed.symm.trans meaning)
          cases same
          refine ⟨target, finalStore, evaluated, ?_⟩
          change RuntimeLinkedWorldCorrespondence.StateRel anchors finalRuntime.storage.world layout.storage.world finalStore
          rw [worldSame]
          exact linked.read_preserved preserved


end Solcore.Frontend.RustHull.LinkedFullWorldCorrespondence
