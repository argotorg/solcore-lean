import Solcore.Surface.Multi.ExactTokenExpressionAnchoring
import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

private theorem TokenPlanEvidence.weakenHeadAndEnclose
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {kind : TokenKind} {headSpan outputSpan : SourceSpan}
    {tail : TokenPlan}
    (evidence : TokenPlanEvidence
      (Option.some ((TokenPlan.exact kind headSpan).append tail))
      (PhysicalTokens tokens origin finish))
    (tailAnchored : tail.WellAnchored)
    (consumed : ConsumedSpan file tokens origin finish outputSpan) :
    TokenPlanEvidence
      (Option.some (TokenPlan.enclose outputSpan
        ((TokenPlan.plain kind).append tail)))
      (PhysicalTokens tokens origin finish) := by
  rcases evidence with ⟨plan, candidateEq, relation⟩
  simp only [Option.some.injEq] at candidateEq
  subst plan
  have innerRelation : TokenSlot.ListMatches
      ((TokenPlan.plain kind).append tail).slots
      (PhysicalTokens tokens origin finish) := by
    apply TokenSlot.ListMatches.exactBetweenToPlain
      (left := TokenPlan.empty) (right := tail)
    simpa using relation
  have innerAnchored :
      ((TokenPlan.plain kind).append tail).WellAnchored :=
    TokenPlan.WellAnchored.append
      (TokenPlan.WellAnchored.plain kind) tailAnchored
  have enclosed := TokenPlanEvidence.enclose
    (TokenPlanEvidence.some innerRelation)
    (fun enclosedPlan success => by
      simp only [Option.some.injEq] at success
      subst enclosedPlan
      exact innerAnchored)
    consumed
  simpa using enclosed

/-- Reducing a `break` statement preserves every retained source token. -/
theorem breakStatement_tokenPlanSound :
    GrammarRuleTokenPlanSound .breakStatement := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | breakStatement origin finish breakKeyword semicolon witness =>
      change EbnfValue file tokens (.sequence [
        .atom (.terminal (.hardKeyword .breakKw)),
        .atom (.terminal (.symbol .semicolon))]) at input
      simp only [m2cV1, m2cV1Rhs, Grammar.sequence,
        Grammar.hardKeyword, Grammar.symbol, Grammar.terminal,
        EbnfExpr.children] at inputEvidence
      rw [EbnfValue.tokenPlan?_sequence] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_terminalAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_terminalAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_nil] at inputEvidence
      rw [MatchedTerminal.physicalTokenPlan_hardKeyword,
        MatchedTerminal.physicalTokenPlan_symbol] at inputEvidence
      have enclosed := inputEvidence.weakenHeadAndEnclose
        (tailAnchored := TokenPlan.WellAnchored.exact _ _)
        witness.consumed
      simpa [ruleTokenPlan?, statementTokenPlan?, sourceLoc,
        TokenPlan.concat_cons] using enclosed

/-- Reducing a `continue` statement preserves every retained source token. -/
theorem continueStatement_tokenPlanSound :
    GrammarRuleTokenPlanSound .continueStatement := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | continueStatement origin finish continueKeyword semicolon witness =>
      change EbnfValue file tokens (.sequence [
        .atom (.terminal (.hardKeyword .continueKw)),
        .atom (.terminal (.symbol .semicolon))]) at input
      simp only [m2cV1, m2cV1Rhs, Grammar.sequence,
        Grammar.hardKeyword, Grammar.symbol, Grammar.terminal,
        EbnfExpr.children] at inputEvidence
      rw [EbnfValue.tokenPlan?_sequence] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_terminalAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_terminalAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_nil] at inputEvidence
      rw [MatchedTerminal.physicalTokenPlan_hardKeyword,
        MatchedTerminal.physicalTokenPlan_symbol] at inputEvidence
      have enclosed := inputEvidence.weakenHeadAndEnclose
        (tailAnchored := TokenPlan.WellAnchored.exact _ _)
        witness.consumed
      simpa [ruleTokenPlan?, statementTokenPlan?, sourceLoc,
        TokenPlan.concat_cons] using enclosed

/-- Reducing a `return` statement, with or without a value, preserves every
retained source token. -/
theorem returnStatement_tokenPlanSound :
    GrammarRuleTokenPlanSound .returnStatement := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | returnStatement origin finish returnKeyword value semicolon witness =>
      change EbnfValue file tokens (.sequence [
        .atom (.terminal (.hardKeyword .returnKw)),
        .optional (.atom (.nonterminal .expression)),
        .atom (.terminal (.symbol .semicolon))]) at input
      simp only [m2cV1, m2cV1Rhs, Grammar.sequence,
        Grammar.hardKeyword, Grammar.symbol, Grammar.terminal,
        Grammar.optional, Grammar.nonterminal,
        EbnfExpr.children, RuleValue] at inputEvidence
      rw [EbnfValue.tokenPlan?_sequence] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_terminalAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      cases value with
      | none =>
          simp only [Option.map] at inputEvidence
          rw [EbnfValue.tokenPlan?_optional_none] at inputEvidence
          rw [EbnfValues.tokenPlan?_cons] at inputEvidence
          rw [EbnfValue.tokenPlan?_terminalAtom] at inputEvidence
          rw [EbnfValues.tokenPlan?_nil] at inputEvidence
          rw [MatchedTerminal.physicalTokenPlan_hardKeyword,
            MatchedTerminal.physicalTokenPlan_symbol] at inputEvidence
          have enclosed := inputEvidence.weakenHeadAndEnclose
            (tailAnchored := TokenPlan.WellAnchored.exact _ _)
            witness.consumed
          simpa [ruleTokenPlan?, statementTokenPlan?, sourceLoc,
            TokenPlan.concat_cons] using enclosed
      | some expression =>
          simp only [Option.map] at inputEvidence
          rw [EbnfValue.tokenPlan?_optional_some] at inputEvidence
          rw [EbnfValue.tokenPlan?_ruleAtom] at inputEvidence
          rw [EbnfValues.tokenPlan?_cons] at inputEvidence
          rw [EbnfValue.tokenPlan?_terminalAtom] at inputEvidence
          rw [EbnfValues.tokenPlan?_nil] at inputEvidence
          simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?]
            at inputEvidence
          rw [MatchedTerminal.physicalTokenPlan_hardKeyword,
            MatchedTerminal.physicalTokenPlan_symbol] at inputEvidence
          cases expressionEq : expressionTokenPlan? expression with
          | none =>
              simp [expressionEq, TokenPlanEvidence] at inputEvidence
          | some expressionPlan =>
              simp only [expressionEq] at inputEvidence
              change expressionTokenPlanAt? .annotation expression =
                some expressionPlan at expressionEq
              have enclosed := inputEvidence.weakenHeadAndEnclose
                (tailAnchored := TokenPlan.WellAnchored.append
                  (expressionTokenPlan?_wellAnchored expression
                    expressionPlan expressionEq)
                  (TokenPlan.WellAnchored.exact _ _))
                witness.consumed
              simpa [ruleTokenPlan?, statementTokenPlan?, sourceLoc,
                TokenPlan.concat_cons, expressionEq] using enclosed

end Solcore.Surface.Multi
