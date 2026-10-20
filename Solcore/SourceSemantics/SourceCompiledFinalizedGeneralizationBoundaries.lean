import Solcore.SourceSemantics.SourceCompiledLocalGeneralizationBoundaries
import Solcore.SourceSemantics.SourceCompiledSelectedFinalization

/-! Original inference, generalization, finalization and parameter
specialization share one actual checking witness. The finalizer's capture
validation applies to the same original binder identified by the worklist. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceSpecializationWorklist
open SourceCompiledLocalGeneralizationEvents LocalGeneralizationBoundaries

namespace Selected
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

/-- Build the inference receipt from this finalizer's own body and substitution. -/
def inferenceReceipt (selected : Selected compiled row fuel) : InferredSelectedBody compiled row fuel := by
  have ready : LocalGeneralizationEvents.Ready (initial selected.signature selected.body.declaration) := by
    refine ⟨State.initial_requirementsWellFormed _ _ _, ?_, ?_⟩
    · intro id impossible
      exact False.elim (List.not_mem_nil impossible)
    · intro node impossible
      exact False.elim (List.not_mem_nil impossible)
  refine {
    original := selected.original
    originalMember := selected.originalMember
    signature := selected.signature
    signatureMember := selected.signatureMember
    declaration := selected.body.declaration
    declared := selected.body.declared
    body := selected.body.body
    substitution := selected.body.finalized.substitution
    inferred := selected.body.inferred
    solved := selected.body.source_nodes
    specialized := ?_
    events := LocalGeneralizationEvents.inferStatementsFuel_origins selected.body.inferred ready
      LocalGeneralizationEvents.Origins.empty
  }
  rw [selected.specialized]
  rfl

theorem inference_body (selected : Selected compiled row fuel) :
    selected.inferenceReceipt.body = selected.body.body := rfl

theorem inference_substitution (selected : Selected compiled row fuel) :
    selected.inferenceReceipt.substitution = selected.body.finalized.substitution := rfl

/-- Return-type unification is an actual continuation of the body and keeps
its retired-local boundary. -/
theorem returned_boundary (selected : Selected compiled row fuel) {binding : LocalLambdaBinding}
    (event : BoundedBindingEvent selected.inferenceReceipt binding) :
    OriginSince selected.inferenceReceipt.initialState.nextLocal selected.body.returned
      event.originalBinder binding.initializer :=
  event.boundary.progress (LocalReadScopeProgress.Progress.unify selected.body.unified)

/-- The finalizer validates capture avoidance for this exact original binder.
Its membership follows from the retained initialized statement occurrence. -/
theorem binding_no_capture (selected : Selected compiled row fuel) {binding : LocalLambdaBinding}
    (event : BoundedBindingEvent selected.inferenceReceipt binding) :
    Detail.LocalBinderInstantiationNoCapture selected.body.finalized.substitution event.originalBinder := by
  apply selected.body.resources.local_no_capture
  unfold TypedSource.initializedLetBinders
  apply List.mem_flatMap.mpr
  refine ⟨.statement event.original, ?_, ?_⟩
  · change .statement event.original ∈ selected.body.returned.nodes
    rw [selected.body.returned_nodes]
    exact event.originalPresent
  · simp only [Node.initializedLetBinders, event.originalForm, StatementForm.initializedLetBinders]
    exact List.mem_singleton_self _

end Selected

structure FinalizedBindingEvent {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (receipt : Selected compiled row fuel) (binding : LocalLambdaBinding)
    extends BoundedBindingEvent receipt.inferenceReceipt binding where
  noCapture : Detail.LocalBinderInstantiationNoCapture receipt.body.finalized.substitution originalBinder

/-- Accepted compilation supplies actual local discovery and one shared
checker/finalizer witness for all returned generalization boundaries. -/
theorem compile_finalized_binding_boundaries {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ selected : Selected compiled row options.checkingFuel,
      ∃ instances, localLambdaInstances row.function.typedBody = .ok instances ∧
        ∀ value ∈ instances,
          value.binding ∈ localLambdaBindings row.function.typedBody ∧
          LocalLambdaInstance.ReadOrigin row.function.typedBody value ∧
          Nonempty (FinalizedBindingEvent selected value.binding) := by
  obtain ⟨selected⟩ := of_compile accepted member
  obtain ⟨instances, discovered, bindings⟩ := SourceCompiledLocalBindings.compile_binding_origins accepted member
  refine ⟨selected, instances, discovered, ?_⟩
  intro value present
  have binding := bindings value present
  obtain ⟨event⟩ := selected.inferenceReceipt.binding_boundary binding.1
  exact ⟨binding.1, binding.2.1, ⟨{
    toBoundedBindingEvent := event
    noCapture := selected.binding_no_capture event
  }⟩⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
