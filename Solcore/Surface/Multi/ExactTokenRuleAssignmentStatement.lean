import Solcore.Surface.Multi.ExactTokenExpressionAnchoring
import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

private theorem TokenPlanEvidence.weakenTailAndEnclose
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {head : TokenPlan} {kind : TokenKind}
    {tailSpan outputSpan : SourceSpan}
    (evidence : TokenPlanEvidence
      (Option.some (head.append (TokenPlan.exact kind tailSpan)))
      (PhysicalTokens tokens origin finish))
    (headAnchored : head.WellAnchored)
    (consumed : ConsumedSpan file tokens origin finish outputSpan) :
    TokenPlanEvidence
      (Option.some (TokenPlan.enclose outputSpan
        (head.append (TokenPlan.plain kind))))
      (PhysicalTokens tokens origin finish) := by
  rcases evidence with ⟨plan, candidateEq, relation⟩
  simp only [Option.some.injEq] at candidateEq
  subst plan
  have innerRelation : TokenSlot.ListMatches
      (head.append (TokenPlan.plain kind)).slots
      (PhysicalTokens tokens origin finish) := by
    apply TokenSlot.ListMatches.exactBetweenToPlain
      (left := head) (right := TokenPlan.empty)
    simpa [TokenPlan.append_assoc] using relation
  have innerAnchored :
      (head.append (TokenPlan.plain kind)).WellAnchored :=
    TokenPlan.WellAnchored.append headAnchored
      (TokenPlan.WellAnchored.plain kind)
  have enclosed := TokenPlanEvidence.enclose
    (TokenPlanEvidence.some innerRelation)
    (fun enclosedPlan success => by
      simp only [Option.some.injEq] at success
      subst enclosedPlan
      exact innerAnchored)
    consumed
  simpa using enclosed

private theorem assignmentOperatorTokenPlan_wellAnchored
    (operator : Located AssignmentOperator) :
    (assignmentOperatorTokenPlan operator).WellAnchored := by
  rcases operator with ⟨span, payload⟩
  cases payload <;> exact TokenPlan.WellAnchored.exact _ _

/-- Assignment reduction preserves both expression plans and the operator,
weakens only the trailing semicolon, and encloses the completed statement. -/
theorem assignmentStatement_tokenPlanSound :
    GrammarRuleTokenPlanSound .assignmentStatement := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | assignmentStatement origin finish left operator right semicolon witness =>
      change EbnfValue file tokens (.sequence [
        .atom (.nonterminal .expression),
        .atom (.nonterminal .assignmentOperator),
        .atom (.nonterminal .expression),
        .atom (.terminal (.symbol .semicolon))]) at input
      simp only [m2cV1, m2cV1Rhs, Grammar.sequence,
        Grammar.nonterminal, Grammar.symbol, Grammar.terminal,
        EbnfExpr.children] at inputEvidence
      rw [EbnfValue.tokenPlan?_sequence] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_ruleAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_ruleAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_ruleAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_terminalAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_nil] at inputEvidence
      simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?] at inputEvidence
      rw [MatchedTerminal.physicalTokenPlan_symbol] at inputEvidence
      cases leftEq : expressionTokenPlan? left with
      | none =>
          simp [leftEq, TokenPlanEvidence] at inputEvidence
      | some leftPlan =>
          cases rightEq : expressionTokenPlan? right with
          | none =>
              simp [leftEq, rightEq, TokenPlanEvidence] at inputEvidence
          | some rightPlan =>
              simp only [leftEq, rightEq] at inputEvidence
              change expressionTokenPlanAt? .annotation left =
                some leftPlan at leftEq
              change expressionTokenPlanAt? .annotation right =
                some rightPlan at rightEq
              let headPlan := TokenPlan.concat [
                leftPlan,
                assignmentOperatorTokenPlan operator,
                rightPlan]
              have normalizedEvidence : TokenPlanEvidence
                  (some (headPlan.append
                    (TokenPlan.exact (.symbol .semicolon) semicolon.span)))
                  (PhysicalTokens tokens origin finish) := by
                simpa [headPlan, TokenPlan.concat_cons,
                  TokenPlan.append_assoc] using inputEvidence
              have headAnchored : headPlan.WellAnchored := by
                simp only [headPlan, TokenPlan.concat_cons,
                  TokenPlan.concat_nil, TokenPlan.append_empty]
                exact TokenPlan.WellAnchored.append
                  (expressionTokenPlan?_wellAnchored left leftPlan leftEq)
                  (TokenPlan.WellAnchored.append
                    (assignmentOperatorTokenPlan_wellAnchored operator)
                    (expressionTokenPlan?_wellAnchored right rightPlan rightEq))
              have enclosed := normalizedEvidence.weakenTailAndEnclose
                headAnchored witness.consumed
              simpa [ruleTokenPlan?, statementTokenPlan?, sourceLoc,
                headPlan, TokenPlan.concat_cons, TokenPlan.append_assoc,
                leftEq, rightEq] using enclosed

end Solcore.Surface.Multi
