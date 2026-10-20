import Solcore.SourceSemantics.SourceInferenceGeneralizedPatternState
import Solcore.SourceSemantics.SourceInferenceGeneralizedExpressionListState

/-! The real single or multiple match-scrutinee call provides the operational
arm-entry state and privacy for the returned scrutinee type. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

private theorem record_expression {state : State} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant state source) (node : ExpressionNode) :
    GeneralizedActualStateInvariant (state.recordNode (.expression node)) source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending, ledger.recordExpression node⟩, invariant.origins.congr_localBinders rfl,
    invariant.quantifiersBelow, invariant.privacy.congr rfl rfl, invariant.backed.congr rfl rfl rfl⟩

theorem GeneralizedActualStateInvariant.ofMatchScrutinees
    {fuel : Nat} {context : SourceInference.Context} {span : Syntax.SourceSpan}
    {sources : List Syntax.Expr} {initial final : State}
    {inferred : InferredExpression} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (accepted : inferMatchScrutineesFuel fuel context span sources initial = .ok (inferred, final)) :
    GeneralizedActualStateInvariant final source ∧
      Safe (activeSchemeQuantifiers final) final inferred.type := by
  have finish (elements : List InferredExpression) (after : State)
      (acceptedElements : Detail.inferExprsFuel fuel context sources initial = .ok (elements, after))
      (recorded : (pure ({
          id := after.allocateExpressionId.1
          type := Ty.productMany (elements.map (·.type))
        },
        after.allocateExpressionId.2.recordNode (.expression {
          id := after.allocateExpressionId.1, span,
          type := Ty.productMany (elements.map (·.type)), form := .tuple (elements.map (·.id))})) :
          Except Error (InferredExpression × State)) = .ok (inferred, final)) :
      GeneralizedActualStateInvariant final source ∧
        Safe (activeSchemeQuantifiers final) final inferred.type := by
    have pairEq := Except.ok.inj recorded
    cases pairEq
    have afterInvariant := invariant.ofExpressions ready catalog formation canonical acceptedElements
    have privacy := inferExprsFuel_private (activeSchemeQuantifiers initial) fuel context sources initial
      ready invariant.requirements (activeSchemeQuantifiers_below_next invariant.quantifiersBelow)
      invariant.privacy.all_live catalog formation canonical _ acceptedElements
    have binders : after.localBinders = initial.localBinders :=
      congrArg LexicalScope.binders (Detail.inferExprsFuel_success_lexicalScope_eq acceptedElements)
    refine ⟨record_expression afterInvariant.allocateExpressionId _, ?_⟩
    change Safe (activeSchemeQuantifiers after) after (Ty.productMany (elements.map (·.type)))
    apply safe_productMany
    intro type member
    obtain ⟨element, present, rfl⟩ := List.mem_map.mp member
    simpa only [activeSchemeQuantifiers, binders] using privacy.2.1 element present
  cases sources with
  | nil =>
    unfold inferMatchScrutineesFuel at accepted
    cases elementsAccepted : Detail.inferExprsFuel fuel context [] initial with
    | error error => simp [elementsAccepted, bind, Except.bind] at accepted
    | ok result =>
      obtain ⟨elements, after⟩ := result
      simp only [elementsAccepted, bind, Except.bind] at accepted
      exact finish elements after elementsAccepted accepted
  | cons first rest =>
    cases rest with
    | nil =>
      have expressionAccepted : Detail.inferExprFuel fuel context first none initial = .ok (inferred, final) :=
        accepted
      exact ⟨invariant.ofExpression ready catalog formation canonical (by simp) (by simp) expressionAccepted,
        invariant.expression_result_private ready catalog formation canonical expressionAccepted⟩
    | cons second tail =>
      unfold inferMatchScrutineesFuel at accepted
      cases elementsAccepted : Detail.inferExprsFuel fuel context (first :: second :: tail) initial with
      | error error => simp [elementsAccepted, bind, Except.bind] at accepted
      | ok result =>
        obtain ⟨elements, after⟩ := result
        simp only [elementsAccepted, bind, Except.bind] at accepted
        exact finish elements after elementsAccepted accepted

end Solcore.SourceSemantics.SourceInferenceSoundness
