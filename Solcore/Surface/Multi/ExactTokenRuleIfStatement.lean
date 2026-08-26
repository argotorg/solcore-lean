import Solcore.Surface.Multi.ExactTokenExpressionAnchoring
import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

private theorem TokenSlot.ListMatches.ifWithoutElseToPlain
    {ifSpan openSpan closeSpan : SourceSpan}
    {condition thenBody : TokenPlan} {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat [
        .exact (.hardKeyword .ifKw) ifSpan,
        .exact (.symbol .leftParen) openSpan,
        condition,
        .exact (.symbol .rightParen) closeSpan,
        thenBody]).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.concat [
        .plain (.hardKeyword .ifKw),
        .plain (.symbol .leftParen),
        condition,
        .plain (.symbol .rightParen),
        thenBody]).slots actual := by
  simp only [TokenPlan.concat, List.flatMap_cons, List.flatMap_nil,
    TokenPlan.exact, TokenPlan.plain, List.append_nil,
    List.singleton_append] at relation ⊢
  cases relation with
  | required ifMatch afterIf =>
      cases afterIf with
      | required openMatch afterOpen =>
          rcases afterOpen.split_append with
            ⟨conditionActual, afterConditionActual, rfl,
              conditionRelation, afterConditionRelation⟩
          cases afterConditionRelation with
          | required closeMatch thenRelation =>
              exact .required ifMatch.toPlain <|
                .required openMatch.toPlain <|
                  conditionRelation.append <|
                    .required closeMatch.toPlain thenRelation

private theorem TokenSlot.ListMatches.ifWithElseToPlain
    {ifSpan openSpan closeSpan elseSpan : SourceSpan}
    {condition thenBody elseBody : TokenPlan} {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat [
        .exact (.hardKeyword .ifKw) ifSpan,
        .exact (.symbol .leftParen) openSpan,
        condition,
        .exact (.symbol .rightParen) closeSpan,
        thenBody,
        .exact (.hardKeyword .elseKw) elseSpan,
        elseBody]).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.concat [
        .plain (.hardKeyword .ifKw),
        .plain (.symbol .leftParen),
        condition,
        .plain (.symbol .rightParen),
        thenBody,
        .plain (.hardKeyword .elseKw),
        elseBody]).slots actual := by
  simp only [TokenPlan.concat, List.flatMap_cons, List.flatMap_nil,
    TokenPlan.exact, TokenPlan.plain, List.append_nil,
    List.singleton_append] at relation ⊢
  cases relation with
  | required ifMatch afterIf =>
      cases afterIf with
      | required openMatch afterOpen =>
          rcases afterOpen.split_append with
            ⟨conditionActual, afterConditionActual, rfl,
              conditionRelation, afterConditionRelation⟩
          cases afterConditionRelation with
          | required closeMatch afterClose =>
              rcases afterClose.split_append with
                ⟨thenActual, afterThenActual, rfl,
                  thenRelation, afterThenRelation⟩
              cases afterThenRelation with
              | required elseMatch elseRelation =>
                  exact .required ifMatch.toPlain <|
                    .required openMatch.toPlain <|
                      conditionRelation.append <|
                        .required closeMatch.toPlain <|
                          thenRelation.append <|
                            .required elseMatch.toPlain elseRelation

private theorem TokenPlan.ifWithoutElse_wellAnchored
    {condition thenBody : TokenPlan}
    (conditionAnchored : condition.WellAnchored)
    (thenAnchored : thenBody.WellAnchored) :
    (TokenPlan.concat [
      .plain (.hardKeyword .ifKw),
      .plain (.symbol .leftParen),
      condition,
      .plain (.symbol .rightParen),
      thenBody]).WellAnchored := by
  apply TokenPlan.WellAnchored.concat
  intro plan member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact TokenPlan.WellAnchored.plain _
  · exact TokenPlan.WellAnchored.plain _
  · exact conditionAnchored
  · exact TokenPlan.WellAnchored.plain _
  · exact thenAnchored

private theorem TokenPlan.ifWithElse_wellAnchored
    {condition thenBody elseBody : TokenPlan}
    (conditionAnchored : condition.WellAnchored)
    (thenAnchored : thenBody.WellAnchored)
    (elseAnchored : elseBody.WellAnchored) :
    (TokenPlan.concat [
      .plain (.hardKeyword .ifKw),
      .plain (.symbol .leftParen),
      condition,
      .plain (.symbol .rightParen),
      thenBody,
      .plain (.hardKeyword .elseKw),
      elseBody]).WellAnchored := by
  apply TokenPlan.WellAnchored.concat
  intro plan member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact TokenPlan.WellAnchored.plain _
  · exact TokenPlan.WellAnchored.plain _
  · exact conditionAnchored
  · exact TokenPlan.WellAnchored.plain _
  · exact thenAnchored
  · exact TokenPlan.WellAnchored.plain _
  · exact elseAnchored

theorem ifStatement_tokenPlanSound :
    GrammarRuleTokenPlanSound .ifStatement := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | ifStatementWithoutElse origin finish ifKeyword openParen condition
      closeParen thenBody witness =>
      change Expression at condition
      change Body at thenBody
      change TokenPlanEvidence
        (statementTokenPlan? false
          (sourceLoc witness
            (.ifThenElse condition thenBody none) : Statement))
        (PhysicalTokens tokens origin finish)
      change EbnfValue file tokens (.sequence [
        .atom (.terminal (.hardKeyword .ifKw)),
        .atom (.terminal (.symbol .leftParen)),
        .atom (.nonterminal .expression),
        .atom (.terminal (.symbol .rightParen)),
        .atom (.nonterminal .body),
        .optional (.sequence [
          .atom (.terminal (.hardKeyword .elseKw)),
          .atom (.nonterminal .body)])]) at input
      simp only [m2cV1, m2cV1Rhs, Grammar.sequence,
        Grammar.nonterminal, Grammar.hardKeyword, Grammar.symbol,
        Grammar.terminal, Grammar.optional, EbnfExpr.children]
        at inputEvidence
      rw [EbnfValue.tokenPlan?_sequence] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_terminalAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_terminalAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_ruleAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_terminalAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_ruleAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_optional_none] at inputEvidence
      rw [EbnfValues.tokenPlan?_nil] at inputEvidence
      simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?] at inputEvidence
      simp only [MatchedTerminal.physicalTokenPlan_hardKeyword,
        MatchedTerminal.physicalTokenPlan_symbol] at inputEvidence
      cases conditionEq : expressionTokenPlan? condition with
      | none => simp [conditionEq, TokenPlanEvidence] at inputEvidence
      | some conditionPlan =>
          cases thenEq : bodyTokenPlan? .braced thenBody with
          | none =>
              simp [conditionEq, thenEq, TokenPlanEvidence] at inputEvidence
          | some thenPlan =>
              simp only [conditionEq, thenEq] at inputEvidence
              change expressionTokenPlanAt? .annotation condition =
                some conditionPlan at conditionEq
              let inner := TokenPlan.concat [
                .plain (.hardKeyword .ifKw),
                .plain (.symbol .leftParen),
                conditionPlan,
                .plain (.symbol .rightParen),
                thenPlan]
              rcases inputEvidence with ⟨sourcePlan, candidateEq, relation⟩
              injection candidateEq with sourcePlanEq
              subst sourcePlan
              have innerRelation : TokenSlot.ListMatches inner.slots
                  (PhysicalTokens tokens origin finish) := by
                exact relation.ifWithoutElseToPlain
              have innerAnchored : inner.WellAnchored := by
                exact TokenPlan.ifWithoutElse_wellAnchored
                  (expressionTokenPlan?_wellAnchored condition conditionPlan
                    conditionEq)
                  (bracedBodyTokenPlan?_wellAnchored thenBody thenPlan thenEq)
              have enclosed := TokenPlanEvidence.enclose
                (TokenPlanEvidence.some innerRelation)
                (fun plan success => by
                  simp only [Option.some.injEq] at success
                  subst plan
                  exact innerAnchored)
                witness.consumed
              simpa [ruleTokenPlan?, statementTokenPlan?, sourceLoc,
                inner, conditionEq, thenEq, TokenPlan.parens,
                TokenPlan.concat_cons, TokenPlan.append_assoc] using enclosed
  | ifStatementWithElse origin finish ifKeyword openParen condition
      closeParen thenBody elseKeyword elseBody witness =>
      change Expression at condition
      change Body at thenBody elseBody
      change TokenPlanEvidence
        (statementTokenPlan? false
          (sourceLoc witness
            (.ifThenElse condition thenBody (some elseBody)) : Statement))
        (PhysicalTokens tokens origin finish)
      change EbnfValue file tokens (.sequence [
        .atom (.terminal (.hardKeyword .ifKw)),
        .atom (.terminal (.symbol .leftParen)),
        .atom (.nonterminal .expression),
        .atom (.terminal (.symbol .rightParen)),
        .atom (.nonterminal .body),
        .optional (.sequence [
          .atom (.terminal (.hardKeyword .elseKw)),
          .atom (.nonterminal .body)])]) at input
      simp only [m2cV1, m2cV1Rhs, Grammar.sequence,
        Grammar.nonterminal, Grammar.hardKeyword, Grammar.symbol,
        Grammar.terminal, Grammar.optional, EbnfExpr.children]
        at inputEvidence
      rw [EbnfValue.tokenPlan?_sequence] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_terminalAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_terminalAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_ruleAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_terminalAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_ruleAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_optional_some] at inputEvidence
      rw [EbnfValue.tokenPlan?_sequence] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_terminalAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_ruleAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_nil] at inputEvidence
      simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?] at inputEvidence
      simp only [MatchedTerminal.physicalTokenPlan_hardKeyword,
        MatchedTerminal.physicalTokenPlan_symbol] at inputEvidence
      cases conditionEq : expressionTokenPlan? condition with
      | none => simp [conditionEq, TokenPlanEvidence] at inputEvidence
      | some conditionPlan =>
          cases thenEq : bodyTokenPlan? .braced thenBody with
          | none =>
              simp [conditionEq, thenEq, TokenPlanEvidence] at inputEvidence
          | some thenPlan =>
              cases elseEq : bodyTokenPlan? .braced elseBody with
              | none =>
                  simp [conditionEq, thenEq, elseEq, TokenPlanEvidence]
                    at inputEvidence
              | some elsePlan =>
                  simp only [conditionEq, thenEq, elseEq] at inputEvidence
                  change expressionTokenPlanAt? .annotation condition =
                    some conditionPlan at conditionEq
                  let inner := TokenPlan.concat [
                    .plain (.hardKeyword .ifKw),
                    .plain (.symbol .leftParen),
                    conditionPlan,
                    .plain (.symbol .rightParen),
                    thenPlan,
                    .plain (.hardKeyword .elseKw),
                    elsePlan]
                  rcases inputEvidence with
                    ⟨sourcePlan, candidateEq, relation⟩
                  injection candidateEq with sourcePlanEq
                  subst sourcePlan
                  have innerRelation : TokenSlot.ListMatches inner.slots
                      (PhysicalTokens tokens origin finish) := by
                    simpa [inner, TokenPlan.append_empty] using
                      relation.ifWithElseToPlain
                  have innerAnchored : inner.WellAnchored := by
                    exact TokenPlan.ifWithElse_wellAnchored
                      (expressionTokenPlan?_wellAnchored condition conditionPlan
                        conditionEq)
                      (bracedBodyTokenPlan?_wellAnchored thenBody thenPlan thenEq)
                      (bracedBodyTokenPlan?_wellAnchored elseBody elsePlan elseEq)
                  have enclosed := TokenPlanEvidence.enclose
                    (TokenPlanEvidence.some innerRelation)
                    (fun plan success => by
                      simp only [Option.some.injEq] at success
                      subst plan
                      exact innerAnchored)
                    witness.consumed
                  simpa [ruleTokenPlan?, statementTokenPlan?, sourceLoc,
                    inner, conditionEq, thenEq, elseEq, TokenPlan.parens,
                    TokenPlan.concat_cons, TokenPlan.append_assoc] using enclosed

end Solcore.Surface.Multi
