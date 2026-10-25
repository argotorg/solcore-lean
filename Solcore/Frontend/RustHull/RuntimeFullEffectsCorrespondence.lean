import Solcore.Frontend.RustHull.RuntimeFullEffectsSemantics
import Solcore.Frontend.RustHull.RuntimeLogEffectsCorrespondence
import Solcore.Frontend.RustHull.TerminationEffectCorrespondence

/-! Message termination uses the established concrete memory/storage model;
its surrounding environment and event cells retain their source observations. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeFullEffectsCorrespondence
open Correspondence ScalarExecution DerivationCorrespondence
open RuntimeLogEffectsCorrespondence (Layout model Passive)

def supported (slots : List EffectSlot) (name : String) : Prop :=
  RuntimeLogEffectsCorrespondence.supported slots name ∨ TerminationEffectCorrespondence.supported name

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
    ExternalCallPreservation (supported slots) (model layout baseline slots) slots RuntimeFullEffectsSemantics.effects := by
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
          exact RuntimeLogEffectsCorrespondence.external_preserves layout baseline slots passive
            memoryMember worldMember addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
            logsMember logSizeMember runtimeEnabled notFunction call typeCompiled
      | @termination finalRuntime computed =>
          have terminationEnabled : TerminationEffectCorrespondence.supported name := by
            rcases enabled with runtime | termination
            · rw [termination_unsupported runtime] at computed
              contradiction
            · exact termination
          intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
          let projected : Semantics.State RuntimeEffectsSemantics.State := ⟨initial.heap, initial.external.runtime.runtime⟩
          have call : Semantics.EvalCall functions TerminationSemantics.effects name type sources projected result
              {projected with external := finalRuntime} := .external absent notPrimitive computed
          have beforeEnvironment := RuntimeLogEffectsCorrespondence.runtime_related state
          obtain ⟨target, finalStore, resultRelated, evaluated, finalState, installedFinal, retained⟩ :=
            TerminationEffectCorrespondence.external_preserves layout.toLayout
              (RuntimeLogEffectsCorrespondence.patched layout baseline initial.external) slots
              memorySizeMember exitMember offsetMember sizeMember terminationEnabled notFunction call typeCompiled
              compiled related packed runtime (RuntimeEnvironmentEffectsCorrespondence.runtime_related beforeEnvironment) installed
          have afterEnvironment := RuntimeEnvironmentEffectsCorrespondence.runtime_updated
            (RuntimeLogEffectsCorrespondence.passive_runtime passive) beforeEnvironment finalState
          exact ⟨target, finalStore, resultRelated, evaluated, RuntimeLogEffectsCorrespondence.runtime_updated afterEnvironment,
            installedFinal, retained⟩

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
    (evaluated : Semantics.EvalFunction functions RuntimeFullEffectsSemantics.effects
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

end Solcore.Frontend.RustHull.RuntimeFullEffectsCorrespondence
