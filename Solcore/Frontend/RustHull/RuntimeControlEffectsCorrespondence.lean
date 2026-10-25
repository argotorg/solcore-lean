import Solcore.Frontend.RustHull.RuntimeControlEffectsSemantics
import Solcore.Frontend.RustHull.TerminationEffectCorrespondence

/-! Termination reuses the concrete memory/storage layout and its resource
model. No external implementation assumption remains at recursive assembly. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeControlEffectsCorrespondence
open Correspondence DerivationCorrespondence ScalarExecution
open RuntimeEffectsCorrespondence (Layout model)

def supported (name : String) : Prop :=
  RuntimeEffectsCorrespondence.supported name ∨ TerminationEffectCorrespondence.supported name

private theorem termination_unsupported {name : String}
    (available : RuntimeEffectsCorrespondence.supported name)
    (type : Ty) (arguments : List Semantics.Value) (state : RuntimeEffectsSemantics.State) :
    TerminationSemantics.builtin name type arguments state = none := by
  rcases available with ⟨operation, rfl⟩ | ⟨operation, rfl⟩
  · cases operation <;> rfl
  · cases operation with | load transient | store transient => cases transient <;> rfl

private theorem runtime_unsupported (operation : TerminationSemantics.Operation)
    (type : Ty) (arguments : List Semantics.Value) (state : RuntimeEffectsSemantics.State) :
    RuntimeEffectsSemantics.builtin operation.name type arguments state = none := by
  cases operation <;> rfl

theorem runtime_builtin {name : String} (available : RuntimeEffectsCorrespondence.supported name)
    (type : Ty) (arguments : List Semantics.Value) (state : RuntimeEffectsSemantics.State) :
    RuntimeControlEffectsSemantics.builtin name type arguments state =
      RuntimeEffectsSemantics.builtin name type arguments state := by
  unfold RuntimeControlEffectsSemantics.builtin
  cases computed : RuntimeEffectsSemantics.builtin name type arguments state with
  | some output => rfl
  | none => exact termination_unsupported available type arguments state

theorem termination_builtin (operation : TerminationSemantics.Operation)
    (type : Ty) (arguments : List Semantics.Value) (state : RuntimeEffectsSemantics.State) :
    RuntimeControlEffectsSemantics.builtin operation.name type arguments state =
      TerminationSemantics.builtin operation.name type arguments state := by
  simp only [RuntimeControlEffectsSemantics.builtin, runtime_unsupported]

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
    ExternalCallPreservation supported (model layout baseline) slots RuntimeControlEffectsSemantics.effects := by
  intro functions name type sources initial final result enabled notFunction called
  rcases enabled with runtimeEnabled | ⟨operation, rfl⟩
  · have call : Semantics.EvalCall functions RuntimeEffectsSemantics.effects name type sources initial result final := by
      cases called with
      | function selected called => rw [notFunction] at selected; contradiction
      | primitive absent computed => exact .primitive absent computed
      | external absent notPrimitive computed =>
          exact .external absent notPrimitive ((runtime_builtin runtimeEnabled type sources initial.external).symm.trans computed)
    intro typeFuel expected typeCompiled
    exact RuntimeEffectsCorrespondence.external_preserves layout baseline slots memoryMember worldMember
      addressMember completeMember staticMember memorySizeMember exitMember offsetMember sizeMember
      runtimeEnabled notFunction call typeCompiled
  · have call : Semantics.EvalCall functions TerminationSemantics.effects operation.name type sources initial result final := by
      cases called with
      | function selected called => rw [notFunction] at selected; contradiction
      | primitive absent computed => exact .primitive absent computed
      | external absent notPrimitive computed =>
          exact .external absent notPrimitive ((termination_builtin operation type sources initial.external).symm.trans computed)
    intro typeFuel expected typeCompiled
    exact TerminationEffectCorrespondence.external_preserves layout baseline slots
      memorySizeMember exitMember offsetMember sizeMember ⟨operation, rfl⟩ notFunction call typeCompiled

/-- Memory, storage, and explicit termination preserve their independent
meaning through actual recursive assembly. -/
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
    (evaluated : Semantics.EvalFunction functions RuntimeControlEffectsSemantics.effects function sources initial sourceResult final)
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

theorem builtin_context {name : String} {type : Ty} {arguments : List Semantics.Value}
    {initial final : RuntimeEffectsSemantics.State} {result : Semantics.Result Semantics.Value}
    (called : RuntimeControlEffectsSemantics.builtin name type arguments initial = some (result, final)) :
    RuntimeEffectsProjectionPreservation.context final = RuntimeEffectsProjectionPreservation.context initial := by
  unfold RuntimeControlEffectsSemantics.builtin at called
  split at called
  · rename_i output runtime
    exact RuntimeEffectsProjectionPreservation.builtin_context (runtime.trans called)
  · exact TerminationEffectCorrespondence.builtin_context called

theorem context_preserves : EffectProjectionPreservation.Preserves RuntimeControlEffectsSemantics.effects
    RuntimeEffectsProjectionPreservation.context where
  builtin := builtin_context
  assembly := False.elim
  revert := False.elim

theorem function_context {functions : List Function} {function : Function}
    {arguments : List Semantics.Value} {initial final : Semantics.State RuntimeEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions RuntimeControlEffectsSemantics.effects function arguments initial result final) :
    RuntimeEffectsProjectionPreservation.context final.external = RuntimeEffectsProjectionPreservation.context initial.external :=
  EffectProjectionPreservation.function_preserves context_preserves evaluated

theorem function_observations {functions : List Function} {function : Function}
    {arguments : List Semantics.Value} {initial final : Semantics.State RuntimeEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions RuntimeControlEffectsSemantics.effects function arguments initial result final) :
    final.external.storage.address = initial.external.storage.address ∧
    final.external.storage.complete = initial.external.storage.complete ∧
    final.external.storage.isStatic = initial.external.storage.isStatic :=
  ⟨congrArg RuntimeEffectsProjectionPreservation.Context.address (function_context evaluated),
   congrArg RuntimeEffectsProjectionPreservation.Context.complete (function_context evaluated),
   congrArg RuntimeEffectsProjectionPreservation.Context.isStatic (function_context evaluated)⟩

end Solcore.Frontend.RustHull.RuntimeControlEffectsCorrespondence
