import Solcore.Surface.Multi.ExactTokenExpressionAnchoring
import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

private theorem matchedIdentifier_physicalTokenPlan
    {file : WorkspaceFile} {tokens : List Token}
    (data : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (projects : IdentifierProjects data.matched data.spelling data.parsed) :
    data.matched.physicalTokenPlan =
      identifierPlan
        (RuleReduction.terminalLoc data.matched data.parsed) := by
  rcases projects with ⟨token, valueEq, payloadEq, parseEq⟩
  have spellingEq : data.spelling = data.parsed.render := by
    unfold Identifier.parse at parseEq
    split at parseEq
    · have parsedEq := Option.some.inj parseEq
      rw [← parsedEq]
      rfl
    · contradiction
  simp [MatchedTerminal.physicalTokenPlan, identifierPlan,
    RuleReduction.terminalLoc, valueEq, payloadEq, spellingEq]

private theorem TokenSlot.ListMatches.fieldWithoutInitializerToPlain
    {colonSpan semicolonSpan : SourceSpan}
    {name typePlan : TokenPlan} {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat [
        name,
        .exact (.symbol .colon) colonSpan,
        typePlan,
        .exact (.symbol .semicolon) semicolonSpan]).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.concat [
        name,
        .plain (.symbol .colon),
        typePlan,
        .plain (.symbol .semicolon)]).slots actual := by
  simp only [TokenPlan.concat, List.flatMap_cons, List.flatMap_nil,
    TokenPlan.exact, TokenPlan.plain, List.append_nil,
    List.singleton_append] at relation ⊢
  rcases relation.split_append with
    ⟨nameActual, afterNameActual, rfl, nameRelation, afterNameRelation⟩
  cases afterNameRelation with
  | required colonMatch afterColon =>
      rcases afterColon.split_append with
        ⟨typeActual, afterTypeActual, rfl,
          typeRelation, afterTypeRelation⟩
      cases afterTypeRelation with
      | required semicolonMatch afterSemicolon =>
          exact nameRelation.append <|
            .required colonMatch.toPlain <|
              typeRelation.append <|
                .required semicolonMatch.toPlain afterSemicolon

private theorem TokenSlot.ListMatches.fieldWithInitializerToPlain
    {colonSpan equalSpan semicolonSpan : SourceSpan}
    {name typePlan expressionPlan : TokenPlan} {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat [
        name,
        .exact (.symbol .colon) colonSpan,
        typePlan,
        .exact (.symbol .equal) equalSpan,
        expressionPlan,
        .exact (.symbol .semicolon) semicolonSpan]).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.concat [
        name,
        .plain (.symbol .colon),
        typePlan,
        .plain (.symbol .equal),
        expressionPlan,
        .plain (.symbol .semicolon)]).slots actual := by
  simp only [TokenPlan.concat, List.flatMap_cons, List.flatMap_nil,
    TokenPlan.exact, TokenPlan.plain, List.append_nil,
    List.singleton_append] at relation ⊢
  rcases relation.split_append with
    ⟨nameActual, afterNameActual, rfl, nameRelation, afterNameRelation⟩
  cases afterNameRelation with
  | required colonMatch afterColon =>
      rcases afterColon.split_append with
        ⟨typeActual, afterTypeActual, rfl,
          typeRelation, afterTypeRelation⟩
      cases afterTypeRelation with
      | required equalMatch afterEqual =>
          rcases afterEqual.split_append with
            ⟨expressionActual, afterExpressionActual, rfl,
              expressionRelation, afterExpressionRelation⟩
          cases afterExpressionRelation with
          | required semicolonMatch afterSemicolon =>
              exact nameRelation.append <|
                .required colonMatch.toPlain <|
                  typeRelation.append <|
                    .required equalMatch.toPlain <|
                      expressionRelation.append <|
                        .required semicolonMatch.toPlain afterSemicolon

private theorem TokenPlan.fieldWithoutInitializer_wellAnchored
    {name typePlan : TokenPlan}
    (nameAnchored : name.WellAnchored)
    (typeAnchored : typePlan.WellAnchored) :
    (TokenPlan.concat [
      name,
      .plain (.symbol .colon),
      typePlan,
      .plain (.symbol .semicolon)]).WellAnchored := by
  apply TokenPlan.WellAnchored.concat
  intro plan member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact nameAnchored
  · exact TokenPlan.WellAnchored.plain _
  · exact typeAnchored
  · exact TokenPlan.WellAnchored.plain _

private theorem TokenPlan.fieldWithInitializer_wellAnchored
    {name typePlan expressionPlan : TokenPlan}
    (nameAnchored : name.WellAnchored)
    (typeAnchored : typePlan.WellAnchored)
    (expressionAnchored : expressionPlan.WellAnchored) :
    (TokenPlan.concat [
      name,
      .plain (.symbol .colon),
      typePlan,
      .plain (.symbol .equal),
      expressionPlan,
      .plain (.symbol .semicolon)]).WellAnchored := by
  apply TokenPlan.WellAnchored.concat
  intro plan member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact nameAnchored
  · exact TokenPlan.WellAnchored.plain _
  · exact typeAnchored
  · exact TokenPlan.WellAnchored.plain _
  · exact expressionAnchored
  · exact TokenPlan.WellAnchored.plain _

theorem fieldDecl_tokenPlanSound :
    GrammarRuleTokenPlanSound .fieldDecl := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | fieldDecl origin finish name colon typeValue initializer semicolon
      nameProjects witness =>
      change TypeExpr at typeValue
      change TokenPlanEvidence
        (fieldDeclPlan? (sourceLoc witness {
          name := RuleReduction.terminalLoc name.matched name.parsed
          type := typeValue
          initializer := initializer.map fun value => value.2.1
        } : FieldDecl))
        (PhysicalTokens tokens origin finish)
      rw [← inputEq] at inputEvidence
      cases initializer with
      | none =>
          have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout = (do
              let typePlan ← typeExprPlan? typeValue
              pure (TokenPlan.concat [
                identifierPlan
                  (RuleReduction.terminalLoc name.matched name.parsed),
                .exact (.symbol .colon) colon.span,
                typePlan,
            .exact (.symbol .semicolon) semicolon.span])) := by
            rw [inputEq]
            rw [EbnfValue.tokenPlan?_transport]
            rw [EbnfValue.tokenPlan?_sequence]
            rw [EbnfValues.tokenPlan?_cons]
            rw [EbnfValue.tokenPlan?_terminalAtom]
            rw [EbnfValues.tokenPlan?_cons]
            rw [EbnfValue.tokenPlan?_terminalAtom]
            rw [EbnfValues.tokenPlan?_cons]
            rw [EbnfValue.tokenPlan?_ruleAtom]
            rw [EbnfValues.tokenPlan?_cons]
            simp only [Option.map]
            rw [EbnfValue.tokenPlan?_optional_none]
            rw [EbnfValues.tokenPlan?_cons]
            rw [EbnfValue.tokenPlan?_terminalAtom]
            rw [EbnfValues.tokenPlan?_nil]
            rw [matchedIdentifier_physicalTokenPlan name nameProjects]
            simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?,
              MatchedTerminal.physicalTokenPlan_symbol]
            cases typeEq : typeExprPlan? typeValue <;>
              simp [TokenPlan.concat_cons]
          have physicalEvidence := inputEvidence.candidate_eq candidateEq
          cases typeEq : typeExprPlan? typeValue with
          | none =>
              simp [typeEq, TokenPlanEvidence] at physicalEvidence
          | some typePlan =>
              simp only [typeEq] at physicalEvidence
              let namePlan := identifierPlan
                (RuleReduction.terminalLoc name.matched name.parsed)
              let inner := TokenPlan.concat [
                namePlan,
                .plain (.symbol .colon),
                typePlan,
                .plain (.symbol .semicolon)]
              rcases physicalEvidence with
                ⟨sourcePlan, sourceEq, relation⟩
              injection sourceEq with sourcePlanEq
              subst sourcePlan
              have innerRelation : TokenSlot.ListMatches inner.slots
                  (PhysicalTokens tokens origin finish) := by
                exact relation.fieldWithoutInitializerToPlain
              have innerAnchored : inner.WellAnchored := by
                exact TokenPlan.fieldWithoutInitializer_wellAnchored
                  (identifierPlan_wellAnchored _)
                  (typeExprPlan?_wellAnchored typeValue typePlan typeEq)
              have enclosed := TokenPlanEvidence.enclose
                (TokenPlanEvidence.some innerRelation)
                (fun plan success => by
                  simp only [Option.some.injEq] at success
                  subst plan
                  exact innerAnchored)
                witness.consumed
              simpa [fieldDeclPlan?, sourceLoc, typeEq, namePlan, inner,
                TokenPlan.concat_cons, TokenPlan.append_assoc] using enclosed
      | some initializerValue =>
          rcases initializerValue with ⟨equal, expression, tailUnit⟩
          cases tailUnit
          change Expression at expression
          have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout = (do
              let typePlan ← typeExprPlan? typeValue
              let expressionPlan ← expressionTokenPlan? expression
              pure (TokenPlan.concat [
                identifierPlan
                  (RuleReduction.terminalLoc name.matched name.parsed),
                .exact (.symbol .colon) colon.span,
                typePlan,
                .exact (.symbol .equal) equal.span,
                expressionPlan,
            .exact (.symbol .semicolon) semicolon.span])) := by
            rw [inputEq]
            rw [EbnfValue.tokenPlan?_transport]
            rw [EbnfValue.tokenPlan?_sequence]
            rw [EbnfValues.tokenPlan?_cons]
            rw [EbnfValue.tokenPlan?_terminalAtom]
            rw [EbnfValues.tokenPlan?_cons]
            rw [EbnfValue.tokenPlan?_terminalAtom]
            rw [EbnfValues.tokenPlan?_cons]
            rw [EbnfValue.tokenPlan?_ruleAtom]
            rw [EbnfValues.tokenPlan?_cons]
            simp only [Option.map]
            rw [EbnfValue.tokenPlan?_optional_some]
            rw [EbnfValue.tokenPlan?_sequence]
            rw [EbnfValues.tokenPlan?_cons]
            rw [EbnfValue.tokenPlan?_terminalAtom]
            rw [EbnfValues.tokenPlan?_cons]
            rw [EbnfValue.tokenPlan?_ruleAtom]
            rw [EbnfValues.tokenPlan?_nil]
            rw [EbnfValues.tokenPlan?_cons]
            rw [EbnfValue.tokenPlan?_terminalAtom]
            rw [EbnfValues.tokenPlan?_nil]
            rw [matchedIdentifier_physicalTokenPlan name nameProjects]
            simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?,
              MatchedTerminal.physicalTokenPlan_symbol]
            cases typeEq : typeExprPlan? typeValue <;>
            cases expressionEq : expressionTokenPlan? expression <;>
              simp [TokenPlan.concat_cons, TokenPlan.append_assoc]
          have physicalEvidence := inputEvidence.candidate_eq candidateEq
          cases typeEq : typeExprPlan? typeValue with
          | none =>
              simp [typeEq, TokenPlanEvidence] at physicalEvidence
          | some typePlan =>
              cases expressionEq : expressionTokenPlan? expression with
              | none =>
                  simp [typeEq, expressionEq, TokenPlanEvidence]
                    at physicalEvidence
              | some expressionPlan =>
                  simp only [typeEq, expressionEq] at physicalEvidence
                  let namePlan := identifierPlan
                    (RuleReduction.terminalLoc name.matched name.parsed)
                  let inner := TokenPlan.concat [
                    namePlan,
                    .plain (.symbol .colon),
                    typePlan,
                    .plain (.symbol .equal),
                    expressionPlan,
                    .plain (.symbol .semicolon)]
                  rcases physicalEvidence with
                    ⟨sourcePlan, sourceEq, relation⟩
                  injection sourceEq with sourcePlanEq
                  subst sourcePlan
                  have innerRelation : TokenSlot.ListMatches inner.slots
                      (PhysicalTokens tokens origin finish) := by
                    exact relation.fieldWithInitializerToPlain
                  have innerAnchored : inner.WellAnchored := by
                    exact TokenPlan.fieldWithInitializer_wellAnchored
                      (identifierPlan_wellAnchored _)
                      (typeExprPlan?_wellAnchored typeValue typePlan typeEq)
                      (expressionTokenPlan?_wellAnchored expression
                        expressionPlan expressionEq)
                  have enclosed := TokenPlanEvidence.enclose
                    (TokenPlanEvidence.some innerRelation)
                    (fun plan success => by
                      simp only [Option.some.injEq] at success
                      subst plan
                      exact innerAnchored)
                    witness.consumed
                  simpa [fieldDeclPlan?, sourceLoc, typeEq, expressionEq,
                    namePlan, inner, TokenPlan.concat_cons,
                    TokenPlan.append_assoc] using enclosed

end Solcore.Surface.Multi
