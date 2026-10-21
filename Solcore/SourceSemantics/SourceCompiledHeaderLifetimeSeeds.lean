import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimes
import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceInferenceHeaderReturnPrivacy
import Solcore.SourceSemantics.SourceInferenceGeneralizedHeaderInitializerState

/-! Header events retain the same allocated binder and initializer as their
containing for node. Their initial lifetime follows from that actual receipt
and the finalizer which retained it. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness ProtectedVariables

theorem initializedHeaderReceipt_accepted
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (receipt : SourceInference.LocalHeaderRequirementTiming.Receipt fuel context source initial result) :
    Detail.inferForItemFuel (fuel + 1) context source initial = .ok result := by
  rcases receipt with ⟨name, initializer, annotation, expected, annotationAccepted,
    form, value, ready, child, completed⟩
  cases annotationAccepted with
  | none =>
    simp [Detail.inferForItemFuel, form, child, completed,
      SourceInference.LocalHeaderRequirementTiming.finish, bind, Except.bind, pure, Pure.pure, Except.pure]
    exact ⟨rfl, rfl⟩
  | some annotationAccepted =>
    simp [Detail.inferForItemFuel, form, annotationAccepted, child, completed,
      SourceInference.LocalHeaderRequirementTiming.finish, bind, Except.bind, pure, Pure.pure, Except.pure]
    exact ⟨rfl, rfl⟩

namespace HeaderLifetime
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.ForItem}
    {inferenceContext : SourceInference.Context} {entry : State} {result : ForItemForm × State}

def event
    (receipt : SourceInference.LocalHeaderRequirementTiming.Receipt childFuel inferenceContext source entry result)
    (ready : receipt.ready.InferenceReady)
    (extension : selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution)
    (retained : ({binder := receipt.binding.1, initializer := .expression receipt.value.id} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource selected))
    (binderRetained : receipt.binding.1 ∈ (evidenceSource selected).initializedLetBinders) :
    RetainedGeneralization (evidenceSource selected) selected.body.finalized.substitution
      receipt.binding.1 receipt.value.id where
  context := inferenceContext
  entry
  readyState := receipt.ready
  value := receipt.value
  valueId := rfl
  computation := .header receipt
  ready
  extension
  retained
  binderRetained

theorem lifetime
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (scope : CheckingScope selected inferenceContext)
    (receipt : SourceInference.LocalHeaderRequirementTiming.Receipt childFuel inferenceContext source entry result)
    (ready : entry.InferenceReady)
    (operational : GeneralizedActualStateInvariant entry (evidenceSource selected))
    (retained : ({binder := receipt.binding.1, initializer := .expression receipt.value.id} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource selected))
    (binderRetained : receipt.binding.1 ∈ (evidenceSource selected).initializedLetBinders)
    (extension : selected.body.finalized.substitution.SemanticallyExtends result.2.inference.substitution) :
    ∃ readyAtEvent readyExtension,
      GeneralizationLifetime (event receipt readyAtEvent readyExtension retained binderRetained)
        entry.inference.next result.2 [] := by
  have formation := scope.formation checked
  have canonical := scope.functionsCanonical checked
  have readyAtEvent := (receipt.initializer_inference ready formation canonical).2.1
  have readyExtension : selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [receipt.inference_eq] at extension
  have itemRetained : result.1.initializedLetBinders ⊆ (evidenceSource selected).initializedLetBinders := by
    rw [receipt.recorded]
    intro binder present
    obtain rfl := List.mem_singleton.mp present
    exact binderRetained
  have after := operational.ofRetainedHeader selected.body.resources ready (scope.catalog checked)
    formation canonical itemRetained extension (initializedHeaderReceipt_accepted receipt)
  have member : receipt.binding.1 ∈ result.2.localBinders := by
    rw [receipt.result_binders]
    exact List.mem_cons_self
  have sameRequirements : result.2.requirements = receipt.ready.requirements :=
    congrArg (fun result : ForItemForm × State => result.2.requirements) receipt.completed
  refine ⟨readyAtEvent, readyExtension, {
    createdAfter := Nat.le_refl _
    allocated := ProtectedVariables.LocalHeaderRequirementTiming.Receipt.quantified_at_or_after_entry
      selected.body.resources receipt ready operational.requirements (scope.catalog checked)
      formation canonical operational.backed operational.origins binderRetained extension
    bound := after.quantifiersBelow _ member
    transport := SafeTransport.of_substitution_eq (congrArg InferState.substitution receipt.inference_eq)
    live := after.privacy _ member
    values := by simp
    older := ?_
    newRows := ?_ }⟩
  · intro type below
    exact ProtectedVariables.LocalHeaderRequirementTiming.Receipt.generalized_type_safe
      selected.body.resources receipt ready operational.requirements (scope.catalog checked)
      formation canonical operational.backed operational.origins binderRetained extension below
  · intro requirement present fresh
    exact False.elim (fresh (sameRequirements ▸ present))

end HeaderLifetime
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
