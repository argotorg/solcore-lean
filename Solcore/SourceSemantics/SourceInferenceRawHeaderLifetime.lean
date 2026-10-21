import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimes
import Solcore.SourceSemantics.SourceInferenceHeaderReturnPrivacy

/-! The real receipt starts its lifetime using only actual requirements,
old template backing and retained binder origins. No whole node-prefix or
entry privacy invariant is required. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace RawHeaderLifetime
variable {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}

def event
    (receipt : SourceInference.LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (ready : receipt.ready.InferenceReady)
    (extension : finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution)
    (retained : ({binder := receipt.binding.1, initializer := .expression receipt.value.id} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceState.toTypedSource roots))
    (binderRetained : receipt.binding.1 ∈ (evidenceState.toTypedSource roots).initializedLetBinders) :
    RetainedGeneralization (evidenceState.toTypedSource roots) finalized.substitution
      receipt.binding.1 receipt.value.id where
  context
  entry := initial
  readyState := receipt.ready
  value := receipt.value
  valueId := rfl
  computation := .header receipt
  ready
  extension
  retained
  binderRetained

theorem lifetime
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (receipt : SourceInference.LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : ({binder := receipt.binding.1, initializer := .expression receipt.value.id} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceState.toTypedSource roots))
    (binderRetained : receipt.binding.1 ∈ (evidenceState.toTypedSource roots).initializedLetBinders)
    (extension : finalized.substitution.SemanticallyExtends result.2.inference.substitution) :
    ∃ readyAtEvent readyExtension,
      GeneralizationLifetime (event (finalized := finalized) receipt readyAtEvent readyExtension retained binderRetained)
        initial.inference.next result.2 [] := by
  have inferred := receipt.initializer_inference ready formation canonical
  have readyExtension : finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [receipt.inference_eq] at extension
  have templates := LocalHeaderRequirementTiming.Receipt.templates_before receipt backed ready wellFormed formation canonical
  have readyLive : LiveBindersSafe receipt.binding.1.scheme.quantified receipt.ready :=
    generalized_live_from_finalizer resources (origins.congr_localBinders receipt.ready_binders)
      readyExtension binderRetained rfl templates
  have unchanged : SafeTransport receipt.binding.1.scheme.quantified receipt.ready result.2 :=
    .of_substitution_eq (congrArg InferState.substitution receipt.inference_eq)
  have afterLive : LiveBindersSafe receipt.binding.1.scheme.quantified result.2 := by
    intro binder member
    rw [receipt.result_binders] at member
    rcases List.mem_cons.mp member with rfl | old
    · exact (binder_private_own_quantifiers readyExtension (resources.local_no_capture _ binderRetained)).transport unchanged
    · apply (readyLive binder ?_).transport unchanged
      rw [receipt.ready_binders]
      exact old
  have sameRequirements : result.2.requirements = receipt.ready.requirements :=
    congrArg (fun output : ForItemForm × State => output.2.requirements) receipt.completed
  refine ⟨inferred.2.1, readyExtension, {
    createdAfter := Nat.le_refl _
    allocated := LocalHeaderRequirementTiming.Receipt.quantified_at_or_after_entry resources receipt ready wellFormed catalog formation canonical backed origins binderRetained extension
    bound := ?_
    transport := unchanged
    live := afterLive
    values := ?_
    older := ?_
    newRows := ?_ }⟩
  · intro q quantified
    have bound := inferred.2.1.solved.variablesBelow_apply inferred.2.2 q (List.mem_filter.mp quantified).1
    simpa only [event, receipt.inference_eq] using bound
  · simp
  · intro type below
    exact LocalHeaderRequirementTiming.Receipt.generalized_type_safe resources receipt ready wellFormed catalog formation canonical backed origins binderRetained extension below
  · intro requirement member fresh
    exact False.elim (fresh (sameRequirements ▸ member))

end RawHeaderLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
