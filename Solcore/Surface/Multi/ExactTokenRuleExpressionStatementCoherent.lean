import Solcore.Surface.Multi.ExactTokenCoherentRuleSoundness
import Solcore.Surface.Multi.ExactTokenExpressionAnchoring
import Solcore.Surface.Multi.ExactTokenRuleLeaf

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

private abbrev expressionStatementSourceChildren : List EbnfExpr := [
  .atom (.nonterminal .expression),
  .optional (.atom (.terminal (.symbol .semicolon)))]

/-- A terminal expression statement has no plan in a context that requires a
semicolon. This records why the rule-level dispatcher must accept both source
terminator values before an enclosing statement list applies its positional
policy. -/
theorem expressionStatementTerminal_mandatoryPlan_none
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (expression : Expression)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    statementTokenPlan? false
      (sourceLoc witness (.expression expression none) : Statement) = none := by
  simp [statementTokenPlan?, sourceLoc]

/-- Consequently, no retained-token sequence can witness that terminal value
under the mandatory-semicolon visitor. -/
theorem expressionStatementTerminal_mandatoryEvidence_absent
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (expression : Expression)
    (witness : ConsumedSpanWitness file tokens origin finish)
    (actual : List Token) :
    ¬ TokenPlanEvidence
      (statementTokenPlan? false
        (sourceLoc witness (.expression expression none) : Statement))
      actual := by
  rw [expressionStatementTerminal_mandatoryPlan_none]
  rintro ⟨plan, success, _relation⟩
  cases success

/-- Expression-statement reduction preserves exact tokens both with and
without the optional semicolon. -/
theorem expressionStatement_tokenPlanSound :
    GrammarRuleTokenPlanSound .expressionStatement := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | expressionStatementTerminated origin finish expression semicolon witness =>
      change EbnfValue file tokens
        (.sequence expressionStatementSourceChildren) at input
      rw [← inputEq] at inputEvidence
      change TokenPlanEvidence
        (statementTokenPlan? true
          (sourceLoc witness
            (.expression expression (some semicolon.span)) : Statement))
        (PhysicalTokens tokens origin finish)
      have candidateEq :
          input.tokenPlan? sourceRuleTokenPlanLayout = (do
            let expressionPlan ← expressionTokenPlan? expression
            pure (expressionPlan.append
              (TokenPlan.exact (.symbol .semicolon) semicolon.span))) := by
        rw [inputEq]
        simp [EbnfExpr.children, sourceRuleTokenPlanLayout, ruleTokenPlan?]
      have coreEvidence := inputEvidence.candidate_eq candidateEq
      cases expressionEq : expressionTokenPlan? expression with
      | none =>
          simp [expressionEq, TokenPlanEvidence] at coreEvidence
      | some expressionPlan =>
          simp only [expressionEq] at coreEvidence
          change expressionTokenPlanAt? .annotation expression =
            some expressionPlan at expressionEq
          have innerAnchored :
              (expressionPlan.append
                (TokenPlan.exact (.symbol .semicolon)
                  semicolon.span)).WellAnchored :=
            TokenPlan.WellAnchored.append
              (expressionTokenPlan?_wellAnchored expression expressionPlan
                expressionEq)
              (TokenPlan.WellAnchored.exact _ _)
          have enclosed := TokenPlanEvidence.enclose coreEvidence
            (fun plan success => by
              cases success
              exact innerAnchored)
            witness.consumed
          simpa [ruleTokenPlan?, statementTokenPlan?, sourceLoc,
            expressionEq] using enclosed
  | expressionStatementTerminal origin finish expression witness =>
      change EbnfValue file tokens
        (.sequence expressionStatementSourceChildren) at input
      rw [← inputEq] at inputEvidence
      change TokenPlanEvidence
        (statementTokenPlan? true
          (sourceLoc witness (.expression expression none) : Statement))
        (PhysicalTokens tokens origin finish)
      have candidateEq :
          input.tokenPlan? sourceRuleTokenPlanLayout =
            expressionTokenPlan? expression := by
        rw [inputEq]
        simp [EbnfExpr.children, sourceRuleTokenPlanLayout, ruleTokenPlan?]
      have coreEvidence := inputEvidence.candidate_eq candidateEq
      cases expressionEq : expressionTokenPlan? expression with
      | none =>
          simp [expressionEq, TokenPlanEvidence] at coreEvidence
      | some expressionPlan =>
          simp only [expressionEq] at coreEvidence
          change expressionTokenPlanAt? .annotation expression =
            some expressionPlan at expressionEq
          have enclosed := TokenPlanEvidence.enclose coreEvidence
            (fun plan success => by
              cases success
              exact expressionTokenPlan?_wellAnchored expression
                expressionPlan expressionEq)
            witness.consumed
          simpa [ruleTokenPlan?, statementTokenPlan?, sourceLoc,
            expressionEq] using enclosed

/-- Coherent complete roots inherit the unrestricted expression-statement
proof; reachability remains available to the enclosing statement policy. -/
theorem expressionStatement_coherentTokenPlanSound :
    CoherentGrammarRuleTokenPlanSound sourceRuleTokenPlanLayout
      .expressionStatement :=
  CoherentGrammarRuleTokenPlanSound.ofGrammarRule
    expressionStatement_tokenPlanSound

end Solcore.Surface.Multi
