import Solcore.SourceSemantics.SourceCompiledGeneralizedForContracts
import Solcore.SourceSemantics.SourceInferenceActiveHeaderPrivacy

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

theorem GeneralizedActualStateInvariant.ofRetainedHeader
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {item : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (invariant : GeneralizedActualStateInvariant initial (evidenceState.toTypedSource roots))
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (retained : result.1.initializedLetBinders ⊆ (evidenceState.toTypedSource roots).initializedLetBinders)
    (extension : finalized.substitution.SemanticallyExtends result.2.inference.substitution)
    (accepted : Detail.inferForItemFuel fuel context item initial = .ok result) :
    GeneralizedActualStateInvariant result.2 (evidenceState.toTypedSource roots) := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending ++ result.1.localSchemeTemplateIds, (actualLedgerFamily fuel).statements.forItem accepted ledger⟩,
    activeBinderCaptureOrigins_inferForItemFuel invariant.origins retained accepted,
    activeQuantifiersBelowNext_inferForItemFuel invariant.quantifiersBelow ready formation canonical accepted,
    invariant.privacy.inferForItemFuel resources ready ledger.requirements invariant.quantifiersBelow
      catalog formation canonical invariant.backed invariant.origins retained extension accepted,
    invariant.backed.inferForItemFuel ready formation canonical accepted⟩

theorem LocalHeaderRequirementTiming.Receipt.schemeIsolation
    {fuel : Nat} {context : SourceInference.Context} {item : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (receipt : SourceInference.LocalHeaderRequirementTiming.Receipt fuel context item initial result)
    (ready : receipt.ready.InferenceReady)
    (priorAvoided : Avoids (activeSchemeQuantifiers initial) (receipt.ready.resolve receipt.value.type))
    (isolated : ActiveSchemeQuantifierIsolation initial)
    (resultPrivate : ActiveQuantifiersPrivate result.2) : ActiveSchemeQuantifierIsolation result.2 := by
  have body : receipt.binding.1.scheme.body = receipt.ready.resolve receipt.value.type := by
    change receipt.generalized.scheme.body = _
    exact Detail.generalizeValue_scheme_body _ _ _ _
  intro binder member q quantified free
  have casesQuantified : q ∈ receipt.binding.1.scheme.quantified ∨ q ∈ activeSchemeQuantifiers initial := by
    simpa only [activeSchemeQuantifiers, receipt.result_binders, List.flatMap_cons, List.mem_append] using quantified
  rcases casesQuantified with fresh | prior
  · have selectedMember : receipt.binding.1 ∈ result.2.localBinders := by
      rw [receipt.result_binders]
      exact List.mem_cons_self
    have safe := (resultPrivate receipt.binding.1 selectedMember binder member).1 q free
    have occurs : q ∈ (receipt.ready.resolve receipt.value.type).freeVariables := (List.mem_filter.mp fresh).1
    have outside := ready.solved.apply_variables_outside_domain receipt.value.type q occurs
    have fixed : result.2.resolve (.variable q) = .variable q := by
      simp only [State.resolve, InferState.resolve, receipt.inference_eq, Substitution.apply,
        (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr outside, Option.getD_none]
    exact safe q (by simp only [fixed, Ty.freeVariables, List.mem_singleton]) fresh
  · rw [receipt.result_binders] at member
    rcases List.mem_cons.mp member with rfl | member
    · have occurs := (List.mem_filter.mp free).1
      rw [body] at occurs
      exact priorAvoided q occurs prior
    · exact isolated binder member q prior free

end Solcore.SourceSemantics.SourceInferenceSoundness
