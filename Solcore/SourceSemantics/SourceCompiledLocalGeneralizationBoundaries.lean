import Solcore.SourceSemantics.SourceCompiledLocalGeneralizationBindings
import Solcore.Frontend.SourceInference.LocalGeneralizationBoundedInference

/-! The actual empty function entry closes the bounded event traversal.
Selected local instances retain their original generalization boundary and its
read containment at the final inferred body state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalGeneralizationEvents
open Frontend SourceInference SourceSpecializationWorklist TypeSystem
open LocalGeneralizationBoundaries

/-- This is the parameter state used by the original checker equation. -/
def InferredSelectedBody.initialState {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (receipt : InferredSelectedBody compiled row fuel) : State :=
  State.initial receipt.declaration.id
    ((receipt.signature.parameterNames.zip receipt.signature.parameterTypes).map fun parameter =>
      (parameter.1, Scheme.mono parameter.2)) receipt.signature.parameterComptime

/-- Every event is created by actual body inference. The initial node table is
empty and parameter binders lie below its real allocator cutoff. -/
theorem InferredSelectedBody.bounded_origins {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (receipt : InferredSelectedBody compiled row fuel) :
    OriginsSince receipt.initialState.nextLocal receipt.body.state := by
  have ready : LocalGeneralizationEvents.Ready receipt.initialState := by
    refine ⟨State.initial_requirementsWellFormed _ _ _, ?_, ?_⟩
    · intro id impossible
      exact False.elim (List.not_mem_nil impossible)
    · intro node impossible
      exact False.elim (List.not_mem_nil impossible)
  have below : receipt.initialState.LocalBindersBelowNextLocal :=
    State.initial_localBindersBelowNextLocal _ _ _
  exact (inferStatementsFuel_boundaries_progress receipt.inferred).empty_entry ready below rfl

structure BoundedBindingEvent {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (receipt : InferredSelectedBody compiled row fuel) (binding : LocalLambdaBinding)
    extends BindingEvent receipt binding where
  boundary : OriginSince receipt.initialState.nextLocal receipt.body.state originalBinder binding.initializer

/-- The selected statement and both substitutions identify the very same
original event whose retired reads remain contained after all continuations. -/
theorem InferredSelectedBody.binding_boundary {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (receipt : InferredSelectedBody compiled row fuel) {binding : LocalLambdaBinding}
    (member : binding ∈ localLambdaBindings row.function.typedBody) :
    Nonempty (BoundedBindingEvent receipt binding) := by
  obtain ⟨event⟩ := receipt.binding_event member
  refine ⟨{ toBindingEvent := event, boundary := ?_ }⟩
  have boundary := receipt.bounded_origins event.original event.originalPresent
  simpa only [StatementSince, event.originalForm] using boundary

/-- The final compiler connection needs only actual accepted selected
compilation. Discovery supplies membership and read ancestry; original
inference supplies generalization and final-state containment. -/
theorem compile_binding_boundaries {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ receipt : InferredSelectedBody compiled row options.checkingFuel,
      ∃ instances, localLambdaInstances row.function.typedBody = .ok instances ∧
        ∀ value ∈ instances,
          value.binding ∈ localLambdaBindings row.function.typedBody ∧
          LocalLambdaInstance.ReadOrigin row.function.typedBody value ∧
          Nonempty (BoundedBindingEvent receipt value.binding) := by
  obtain ⟨receipt⟩ := compile_selected_body accepted member
  obtain ⟨instances, discovered, bindings⟩ := SourceCompiledLocalBindings.compile_binding_origins accepted member
  refine ⟨receipt, instances, discovered, ?_⟩
  intro value present
  have binding := bindings value present
  exact ⟨binding.1, binding.2.1, receipt.binding_boundary binding.1⟩

end Solcore.SourceSemantics.SourceCompiledLocalGeneralizationEvents
