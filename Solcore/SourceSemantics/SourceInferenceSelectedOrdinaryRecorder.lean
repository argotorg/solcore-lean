import Solcore.SourceSemantics.SourceInferenceSelectedLeafSoundness

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem recordExpressionWithExpected_success_expressionTypingBase_actual
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      wholeContext.signatures finalized.solvedRequirements finalized.typedSource)
    {expression : Syntax.Expr} {expected : Option Ty}
    {initial recordedState resultState : State} {id : ExpressionId}
    {rawType : Ty} {form : ExpressionForm} {owned : List RequirementId}
    {instantiationStart : Option Nat} {inferred : InferredExpression}
    {semanticSource : TypedSource} {active : SourceSemantics.Context}
    (recorded : Detail.recordExpressionWithExpected inferenceContext expression id
      rawType form owned expected recordedState instantiationStart = .ok (inferred, resultState))
    (extension : finalized.substitution.SemanticallyExtends resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆ evidenceState.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id)
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial active)
    (formType : ExpressionFormHasRawType semanticSource active
      (form.applySubstitution finalized.substitution) (finalized.substitution.apply rawType)
      (.ordinary owned))
    (rawAdmissible : TypeAdmissible active (finalized.substitution.apply rawType))
    (covered : TemplateScopeCovered finalized.typedSource active (.expression inferred.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource active
      finalized.substitution inferred := by
  have finalSubstitutionEq := resources.substitution_eq.symm
  have finalExtension : resources.finalState.inference.substitution.SemanticallyExtends
      resultState.inference.substitution := by simpa only [finalSubstitutionEq] using extension
  have finalRequirements : resultState.requirements ⊆ resources.finalState.requirements := by
    rw [resources.requirements_eq]
    exact requirementsSubset
  have activeSignaturesEq : active.signatures = inferenceContext.signatures :=
    invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeCatalog : SignatureCatalogWellFormed active.signatures := by
    rw [activeSignaturesEq]
    exact catalog
  simpa only [finalSubstitutionEq] using
    (recordExpressionWithExpected_success_ordinaryExpressionTypingBase_from_interfaces
      (base := finalizedRequirementContext wholeContext finalized)
      recorded finalExtension finalRequirements retained
      (by simpa only [finalSubstitutionEq] using formType)
      (by simpa only [finalSubstitutionEq] using rawAdmissible)
      (by simpa only [signaturesEq] using interfaces) coercionsRetained
      activeCatalog activeSignaturesEq resources.solve_success resources.solved_context_eq
      resources.ledger resources.ownership invariant.signaturesEq invariant.solvedRequirementsEq
      invariant.assumptionsMono covered)

theorem recordExpressionWithExpected_success_nodesPrefix
    {inferenceContext : Frontend.SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId}
    {type : TypeSystem.Ty} {form : ExpressionForm}
    {requirements : List RequirementId}
    {expected : Option TypeSystem.Ty}
    {initial : Frontend.SourceInference.State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × Frontend.SourceInference.State}
    (success : Detail.recordExpressionWithExpected inferenceContext source id
      type form requirements expected initial localSchemeInstantiationStart =
        .ok result) :
    initial.nodes <+: result.2.nodes := by
  obtain ⟨fitted, fittedSuccess, _, resultStateEq⟩ :=
    Detail.recordExpressionWithExpected_success_record success
  have fittedPrefix : initial.nodes <+: fitted.state.nodes := by
    rw [(Detail.withExpected_occurrenceState_eq fittedSuccess).1]
    exact List.prefix_rfl
  rw [resultStateEq]
  exact fittedPrefix.trans
    (Frontend.SourceInference.State.recordNode_nodesPrefix fitted.state _)


end Solcore.SourceSemantics.SourceInferenceSoundness
