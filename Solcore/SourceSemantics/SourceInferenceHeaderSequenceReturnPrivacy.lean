import Solcore.SourceSemantics.SourceInferenceHeaderReturnPrivacy
import Solcore.SourceSemantics.SourceInferenceGeneralizedHeaderInitializerState

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

/-- Return-type privacy follows the actual ordered header calls and their retained binders. -/
theorem GeneralizedActualStateInvariant.forItems_return_safe
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.ForItem}
    {initial : State} {result : Detail.InferredForItems} {expectedReturn : Ty}
    (invariant : GeneralizedActualStateInvariant initial (evidenceState.toTypedSource roots))
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (retained : result.items.flatMap ForItemForm.initializedLetBinders ⊆
      (evidenceState.toTypedSource roots).initializedLetBinders)
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (returnSafe : ∀ binder ∈ initial.localBinders, Safe binder.scheme.quantified initial expectedReturn)
    (accepted : Detail.inferForItemsFuel fuel context sources initial = .ok result) :
    ∀ binder ∈ result.state.localBinders, Safe binder.scheme.quantified result.state expectedReturn := by
  induction sources generalizing initial result with
  | nil =>
    simp only [Detail.inferForItemsFuel, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    subst result
    exact returnSafe
  | cons head tail induction =>
    cases headRun : Detail.inferForItemFuel fuel context head initial with
    | error error => simp [Detail.inferForItemsFuel, headRun, bind, Except.bind] at accepted
    | ok pair =>
      rcases pair with ⟨item, state⟩
      cases tailRun : Detail.inferForItemsFuel fuel context tail state with
      | error error => simp [Detail.inferForItemsFuel, headRun, tailRun, bind, Except.bind] at accepted
      | ok rest =>
        simp only [Detail.inferForItemsFuel, headRun, tailRun, bind, Except.bind,
          pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
        subst result
        have headProperties := Detail.inferForItemFuel_inferenceProperties ready formation canonical headRun
        have tailProperties := Detail.inferForItemsFuel_inferenceProperties headProperties.2 formation canonical tailRun
        have headRetained : item.initializedLetBinders ⊆ (evidenceState.toTypedSource roots).initializedLetBinders := by
          intro binder member
          apply retained
          exact List.mem_append_left _ member
        have tailRetained : rest.items.flatMap ForItemForm.initializedLetBinders ⊆
            (evidenceState.toTypedSource roots).initializedLetBinders := by
          intro binder member
          apply retained
          exact List.mem_append_right _ member
        have middle := invariant.ofRetainedHeader resources ready catalog formation canonical headRetained
          (extension.trans tailProperties.1.substitution_extends) headRun
        have safe := inferForItemFuel_return_safe resources ready invariant.requirements invariant.quantifiersBelow
          invariant.privacy catalog formation canonical invariant.backed invariant.origins headRetained
          (extension.trans tailProperties.1.substitution_extends)
          returnBelow returnSafe headRun
        exact induction (result := rest) middle headProperties.2 tailRetained extension
          (returnBelow.weaken headProperties.1.next_le) safe tailRun

end Solcore.SourceSemantics.SourceInferenceSoundness
