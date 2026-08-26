import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRulePassThrough
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

private abbrev postfixPartSourceBranches : List EbnfExpr := [
  .sequence [
    .atom (.terminal (.symbol .leftParen)),
    .list0 (.atom (.nonterminal .expression)),
    .atom (.terminal (.symbol .rightParen))],
  .sequence [
    .atom (.terminal (.symbol .dot)),
    .atom (.terminal (.category .identifier))],
  .sequence [
    .atom (.terminal (.symbol .leftBracket)),
    .atom (.nonterminal .expression),
    .atom (.terminal (.symbol .rightBracket))]
]

private theorem matchedIdentifier_physicalTokenPlan
    {file : WorkspaceFile} {tokens : List Token}
    (matched : MatchedTerminal file tokens (.category .identifier))
    (spelling : String) (parsed : Identifier)
    (projects : IdentifierProjects matched spelling parsed) :
    matched.physicalTokenPlan = identifierPlan
      (RuleReduction.terminalLoc matched parsed) := by
  rcases projects with ⟨token, valueEq, payloadEq, parseEq⟩
  have spellingEq : spelling = parsed.render := by
    unfold Identifier.parse at parseEq
    split at parseEq
    · have parsedEq := Option.some.inj parseEq
      rw [← parsedEq]
      rfl
    · contradiction
  simp [MatchedTerminal.physicalTokenPlan, identifierPlan,
    RuleReduction.terminalLoc, valueEq, payloadEq, spellingEq]

private theorem expressionPlans_eq_mapM (values : List Expression) :
    expressionTokenPlans? values =
      values.mapM (ruleTokenPlan? .expression) := by
  change expressionTokenPlans? values = values.mapM expressionTokenPlan?
  induction values with
  | nil => simp [expressionTokenPlans?]
  | cons head tail induction =>
      simp [expressionTokenPlans?, expressionTokenPlan?, induction]

/-- Call, field-selection, and indexing suffixes retain their complete source
token plans before postfix folding attaches a receiver. -/
theorem postfixPart_tokenPlanSound :
    GrammarRuleTokenPlanSound .postfixPart := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | postfixPartCall origin finish openParen arguments closeParen =>
      change EbnfValue file tokens (.choice postfixPartSourceBranches) at input
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_list0,
        EbnfValues.tokenPlan?_nil] at sequenceEvidence
      simp [sourceRuleTokenPlanLayout] at sequenceEvidence
      change TokenPlanEvidence
        (postfixPartTokenPlan?
          (.call openParen.span arguments closeParen.span)) _
      apply sequenceEvidence.candidate_eq
      simp [postfixPartTokenPlan?, expressionPlans_eq_mapM,
        Function.comp_def]
      cases argumentPlansEq : List.mapM
          (ruleTokenPlan? .expression)
          arguments with
      | none =>
          rfl
      | some argumentPlans =>
          rfl
  | postfixPartSelect origin finish dot field spelling parsed projects =>
      change EbnfValue file tokens (.choice postfixPartSourceBranches) at input
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      simp [sourceRuleTokenPlanLayout] at sequenceEvidence
      change TokenPlanEvidence
        (postfixPartTokenPlan?
          (.select dot.span
            (RuleReduction.terminalLoc field parsed))) _
      apply sequenceEvidence.candidate_eq
      simp [postfixPartTokenPlan?,
        matchedIdentifier_physicalTokenPlan field spelling parsed projects]
  | postfixPartIndex origin finish openBracket index closeBracket =>
      change EbnfValue file tokens (.choice postfixPartSourceBranches) at input
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      simp [sourceRuleTokenPlanLayout, ruleTokenPlan?] at sequenceEvidence
      change TokenPlanEvidence
        (postfixPartTokenPlan?
          (.index openBracket.span index closeBracket.span)) _
      apply sequenceEvidence.candidate_eq
      cases indexEq : expressionTokenPlan? index <;>
        simp [postfixPartTokenPlan?, indexEq,
          TokenPlan.concat_cons]

end Solcore.Surface.Multi
