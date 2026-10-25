import Solcore.Frontend.RustHull.TerminationBuiltinCorrespondence
import Solcore.Frontend.RustHull.RuntimeEffectsProjectionPreservation

/-! Concrete termination discharges the external-call obligation and reaches
actual recursive assembly using the existing memory/storage resource model. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.TerminationEffectCorrespondence
open Correspondence DerivationCorrespondence ScalarExecution
open RuntimeEffectsCorrespondence (Layout model memory_related storage_related frame_above resources_preserved)

def supported (name : String) : Prop := ∃ operation : TerminationSemantics.Operation, operation.name = name

theorem external_preserves (layout : Layout) (baseline : Nat → Option Core.Value) (slots : List EffectSlot)
    (memorySizeMember : ⟨"memorySize", .word, layout.storage.memorySize⟩ ∈ slots)
    (exitMember : ⟨"exit", .word, layout.storage.exit⟩ ∈ slots)
    (offsetMember : ⟨"returnOffset", .word, layout.storage.returnOffset⟩ ∈ slots)
    (sizeMember : ⟨"returnSize", .word, layout.storage.returnSize⟩ ∈ slots) :
    ExternalCallPreservation supported (model layout baseline) slots TerminationSemantics.effects := by
  intro functions name type sources initial final result available notFunction called
  obtain ⟨operation, rfl⟩ := available
  cases called with
  | function selected called => rw [notFunction] at selected; contradiction
  | primitive absent computed =>
      cases operation <;> simp [TerminationSemantics.Operation.name, Semantics.primitive?] at computed
  | external absent notPrimitive computed =>
      intro typeFuel expected typeCompiled scope arguments lowered compiled world mapping environment initialStore argumentStore targets codes locations captured related packed runtime state installed
      obtain ⟨computedResult, computedState, target, finalStore, meaning, resultRelated, evaluated, memoryFinal, storageFinal, frame, retained⟩ :=
        TerminationBuiltinCorrespondence.preserves operation compiled related runtime
          memorySizeMember exitMember offsetMember sizeMember (memory_related state) (storage_related state) packed type
      have same := Option.some.inj (computed.symm.trans meaning)
      cases same
      exact ⟨target, finalStore, resultRelated, evaluated,
        state.cutoff_effect (frame_above frame)
          (resources_preserved state.external.1 state.external.2.2 memoryFinal storageFinal frame),
        installed.preserved retained, retained⟩

theorem assemble_program (layout : Layout) (baseline : Nat → Option Core.Value)
    (slots : List EffectSlot)
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
    (evaluated : Semantics.EvalFunction functions TerminationSemantics.effects function sources initial sourceResult final)
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
    (external_preserves layout baseline slots memorySizeMember exitMember offsetMember sizeMember) eligible values evaluated
    runtimeLength covered runtimeRelated separated state


theorem terminate_context (state : RuntimeEffectsSemantics.State) (kind : Nat) (offset length : Core.Word) :
    RuntimeEffectsProjectionPreservation.context (TerminationSemantics.terminate state kind offset length).2 =
      RuntimeEffectsProjectionPreservation.context state := by
  unfold TerminationSemantics.terminate
  split <;> rfl

private theorem terminated_context {state final : RuntimeEffectsSemantics.State}
    {kind : Nat} {offset length : Core.Word} {result : Semantics.Result Semantics.Value}
    (called : some (TerminationSemantics.terminate state kind offset length) = some (result, final)) :
    RuntimeEffectsProjectionPreservation.context final = RuntimeEffectsProjectionPreservation.context state := by
  have changed : (TerminationSemantics.terminate state kind offset length).2 = final :=
    congrArg Prod.snd (Option.some.inj called)
  exact (congrArg RuntimeEffectsProjectionPreservation.context changed).symm.trans
    (terminate_context state kind offset length)

theorem builtin_context {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : RuntimeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (called : TerminationSemantics.builtin name type arguments initial = some (result, final)) :
    RuntimeEffectsProjectionPreservation.context final = RuntimeEffectsProjectionPreservation.context initial := by
  by_cases returned : name = "return"
  · subst name
    rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
    all_goals try cases first
    all_goals try cases second
    all_goals try contradiction
    rename_i offset length
    exact terminated_context (kind := 1) (offset := offset) (length := length) called
  by_cases reverted : name = "revert"
  · subst name
    rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
    all_goals try cases first
    all_goals try cases second
    all_goals try contradiction
    rename_i offset length
    exact terminated_context (kind := 2) (offset := offset) (length := length) called
  by_cases stopped : name = "stop"
  · subst name
    cases arguments with
    | nil => exact terminated_context (kind := 1) (offset := Core.Word.zero) (length := Core.Word.zero) called
    | cons first rest => cases first <;> contradiction
  by_cases invalid : name = "invalid"
  · subst name
    cases arguments with
    | nil => exact terminated_context (kind := 3) (offset := Core.Word.zero) (length := Core.Word.zero) called
    | cons first rest => cases first <;> contradiction
  simp [TerminationSemantics.builtin, returned, reverted, stopped, invalid] at called

theorem context_preserves : EffectProjectionPreservation.Preserves TerminationSemantics.effects
    RuntimeEffectsProjectionPreservation.context where
  builtin := builtin_context
  assembly := False.elim
  revert := False.elim

theorem function_context {functions : List Function} {function : Function}
    {arguments : List Semantics.Value} {initial final : Semantics.State RuntimeEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions TerminationSemantics.effects function arguments initial result final) :
    RuntimeEffectsProjectionPreservation.context final.external = RuntimeEffectsProjectionPreservation.context initial.external :=
  EffectProjectionPreservation.function_preserves context_preserves evaluated

end Solcore.Frontend.RustHull.TerminationEffectCorrespondence
