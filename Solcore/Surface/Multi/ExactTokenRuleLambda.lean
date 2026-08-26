import Solcore.Surface.Multi.ExactTokenExpressionAnchoring
import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace
private theorem ruleAtomValues_tokenPlans?
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId) (values : List (RuleValue rule)) :
    (values.map (EbnfValue.ruleAtom (file := file) (tokens := tokens)
      rule)).mapM
        (fun value => value.tokenPlan? sourceRuleTokenPlanLayout) =
      values.mapM (ruleTokenPlan? rule) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      rw [List.map_cons, List.mapM_cons, List.mapM_cons]
      have headEq :
          (EbnfValue.ruleAtom (file := file) (tokens := tokens)
            rule value).tokenPlan? sourceRuleTokenPlanLayout =
          ruleTokenPlan? rule value :=
        EbnfValue.tokenPlan?_ruleAtom _ _ _
      rw [headEq, induction]

private theorem parameterRuleValues_tokenPlans?
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : List Parameter) :
    (parameters.map (EbnfValue.ruleAtom
      (file := file) (tokens := tokens) .parameter)).mapM
        (fun value => value.tokenPlan? sourceRuleTokenPlanLayout) =
      parameters.mapM parameterTokenPlan? := by
  rw [ruleAtomValues_tokenPlans? .parameter parameters]
  rfl

private theorem lambdaTokenPlan_eq_mapM
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (parameters : List Parameter)
    (returnType : Option
      (MatchedTerminal file tokens (.symbol .arrow) × TypeExpr))
    (body : Body)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    atomExpressionTokenPlan?
      (sourceLoc witness
        (.lambda parameters (returnType.map Prod.snd) body)) = (do
      let parameterPlans ← parameters.mapM parameterTokenPlan?
      let returnPlan ← match returnType with
        | none => some .empty
        | some value => do
            let typePlan ← typeExprPlan? value.2
            pure (.append (.plain (.symbol .arrow)) typePlan)
      let bodyPlan ← bodyTokenPlan? .braced body
      pure (.enclose witness.span (.concat [
        .plain (.hardKeyword .lamKw),
        .parens (.commaSeparated parameterPlans),
        returnPlan,
        bodyPlan]))) := by
  cases returnType <;>
    simp [atomExpressionTokenPlan?, expressionTokenPlanAt?, sourceLoc,
      parameterTokenPlans?_eq_mapM]

private theorem TokenSlot.ListMatches.lambdaWithoutReturnToPlain
    {lambdaSpan openSpan closeSpan : SourceSpan}
    {parameters body : TokenPlan} {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat [
        .exact (.hardKeyword .lamKw) lambdaSpan,
        .exact (.symbol .leftParen) openSpan,
        parameters,
        .exact (.symbol .rightParen) closeSpan,
        .empty,
        body]).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.concat [
        .plain (.hardKeyword .lamKw),
        .parens parameters,
        .empty,
        body]).slots actual := by
  simp only [TokenPlan.concat, List.flatMap_cons, List.flatMap_nil,
    TokenPlan.exact, TokenPlan.plain, TokenPlan.parens, TokenPlan.empty,
    List.append_nil, List.singleton_append] at relation ⊢
  cases relation with
  | required lambdaMatch afterLambda =>
      cases afterLambda with
      | required openMatch afterOpen =>
          rcases afterOpen.split_append with
            ⟨parameterActual, afterParameterActual, rfl,
              parameterRelation, afterParameterRelation⟩
          cases afterParameterRelation with
          | required closeMatch bodyRelation =>
              have closePlain := closeMatch.toPlain
              change (ExpectedToken.plain
                (.symbol .rightParen)).Matches _ at closePlain
              exact .required lambdaMatch.toPlain <|
                .required openMatch.toPlain <| by
                  simpa [List.append_assoc] using
                    parameterRelation.append
                      (.required closePlain bodyRelation)

private theorem TokenSlot.ListMatches.lambdaWithReturnToPlain
    {lambdaSpan openSpan closeSpan arrowSpan : SourceSpan}
    {parameters typePlan body : TokenPlan} {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat [
        .exact (.hardKeyword .lamKw) lambdaSpan,
        .exact (.symbol .leftParen) openSpan,
        parameters,
        .exact (.symbol .rightParen) closeSpan,
        .append (.exact (.symbol .arrow) arrowSpan) typePlan,
        body]).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.concat [
        .plain (.hardKeyword .lamKw),
        .parens parameters,
        .append (.plain (.symbol .arrow)) typePlan,
        body]).slots actual := by
  simp only [TokenPlan.concat, List.flatMap_cons, List.flatMap_nil,
    TokenPlan.exact, TokenPlan.plain, TokenPlan.parens, TokenPlan.append,
    List.append_nil, List.singleton_append] at relation ⊢
  cases relation with
  | required lambdaMatch afterLambda =>
      cases afterLambda with
      | required openMatch afterOpen =>
          rcases afterOpen.split_append with
            ⟨parameterActual, afterParameterActual, rfl,
              parameterRelation, afterParameterRelation⟩
          cases afterParameterRelation with
          | required closeMatch afterClose =>
              cases afterClose with
              | required arrowMatch afterArrow =>
                  have closePlain := closeMatch.toPlain
                  change (ExpectedToken.plain
                    (.symbol .rightParen)).Matches _ at closePlain
                  have arrowPlain := arrowMatch.toPlain
                  change (ExpectedToken.plain
                    (.symbol .arrow)).Matches _ at arrowPlain
                  exact .required lambdaMatch.toPlain <|
                    .required openMatch.toPlain <| by
                      simpa [List.append_assoc] using
                        parameterRelation.append
                          (.required closePlain <|
                            .required arrowPlain afterArrow)

private theorem TokenPlan.lambdaInner_wellAnchored
    {parameters returnPlan body : TokenPlan}
    (returnAnchored : returnPlan.WellAnchored)
    (bodyAnchored : body.WellAnchored) :
    (TokenPlan.concat [
      .plain (.hardKeyword .lamKw),
      .parens parameters,
      returnPlan,
      body]).WellAnchored := by
  apply TokenPlan.WellAnchored.concat
  intro plan member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact TokenPlan.WellAnchored.plain _
  · exact TokenPlan.WellAnchored.parens parameters
  · exact returnAnchored
  · exact bodyAnchored

theorem lambda_tokenPlanSound :
    GrammarRuleTokenPlanSound .lambda := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | lambda origin finish lambdaKeyword openParen parameters closeParen
      returnType body witness =>
      change List Parameter at parameters
      change Body at body
      change TokenPlanEvidence
        (atomExpressionTokenPlan?
          (show Expression from sourceLoc witness
            (.lambda parameters (returnType.map Prod.snd) body)))
        (PhysicalTokens tokens origin finish)
      rw [← inputEq] at inputEvidence
      have sourceCandidateEq :
          input.tokenPlan? sourceRuleTokenPlanLayout = (do
            let parameterPlans ← parameters.mapM parameterTokenPlan?
            let returnPlan ← match returnType with
              | none => some .empty
              | some value => do
                  let typePlan ← typeExprPlan? value.2
                  pure (.append
                    (.exact (.symbol .arrow) value.1.span) typePlan)
            let bodyPlan ← bodyTokenPlan? .braced body
            pure (TokenPlan.concat [
              .exact (.hardKeyword .lamKw) lambdaKeyword.span,
              .exact (.symbol .leftParen) openParen.span,
              .commaSeparated parameterPlans,
              .exact (.symbol .rightParen) closeParen.span,
              returnPlan,
              bodyPlan])) := by
        rw [inputEq]
        simp only [m2cV1, m2cV1Rhs, Grammar.sequence,
          Grammar.nonterminal, Grammar.hardKeyword, Grammar.symbol,
          Grammar.terminal, Grammar.list0, Grammar.optional,
          EbnfExpr.children]
        rw [EbnfValue.tokenPlan?_sequence]
        rw [EbnfValues.tokenPlan?_cons]
        rw [EbnfValue.tokenPlan?_terminalAtom]
        rw [EbnfValues.tokenPlan?_cons]
        rw [EbnfValue.tokenPlan?_terminalAtom]
        rw [EbnfValues.tokenPlan?_cons]
        rw [EbnfValue.tokenPlan?_list0]
        rw [EbnfValues.tokenPlan?_cons]
        rw [EbnfValue.tokenPlan?_terminalAtom]
        rw [EbnfValues.tokenPlan?_cons]
        cases returnType with
        | none =>
            rw [Option.map_none, EbnfValue.tokenPlan?_optional_none]
            rw [EbnfValues.tokenPlan?_cons]
            rw [EbnfValue.tokenPlan?_ruleAtom]
            rw [EbnfValues.tokenPlan?_nil]
            rw [parameterRuleValues_tokenPlans? parameters]
            simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?,
              MatchedTerminal.physicalTokenPlan_hardKeyword,
              MatchedTerminal.physicalTokenPlan_symbol]
            cases parameterEq : parameters.mapM parameterTokenPlan? <;>
            cases bodyEq : bodyTokenPlan? .braced body <;>
            simp [TokenPlan.concat_cons]
        | some value =>
            rw [Option.map_some, EbnfValue.tokenPlan?_optional_some]
            rw [EbnfValue.tokenPlan?_sequence]
            rw [EbnfValues.tokenPlan?_cons]
            rw [EbnfValue.tokenPlan?_terminalAtom]
            rw [EbnfValues.tokenPlan?_cons]
            rw [EbnfValue.tokenPlan?_ruleAtom]
            rw [EbnfValues.tokenPlan?_nil]
            rw [EbnfValues.tokenPlan?_cons]
            rw [EbnfValue.tokenPlan?_ruleAtom]
            rw [EbnfValues.tokenPlan?_nil]
            rw [parameterRuleValues_tokenPlans? parameters]
            simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?,
              MatchedTerminal.physicalTokenPlan_hardKeyword,
              MatchedTerminal.physicalTokenPlan_symbol]
            cases parameterEq : parameters.mapM parameterTokenPlan? <;>
            cases typeEq : typeExprPlan? value.2 <;>
            cases bodyEq : bodyTokenPlan? .braced body <;>
            simp [TokenPlan.concat_cons]
      have physicalEvidence := inputEvidence.candidate_eq sourceCandidateEq
      cases parameterEq : parameters.mapM parameterTokenPlan? with
      | none =>
          simp [parameterEq, TokenPlanEvidence] at physicalEvidence
      | some parameterPlans =>
          cases returnType with
          | none =>
              cases bodyEq : bodyTokenPlan? .braced body with
              | none =>
                  simp [parameterEq, bodyEq, TokenPlanEvidence]
                    at physicalEvidence
              | some bodyPlan =>
                  simp only [parameterEq, bodyEq] at physicalEvidence
                  let parameterCore :=
                    TokenPlan.commaSeparated parameterPlans
                  let inner := TokenPlan.concat [
                    .plain (.hardKeyword .lamKw),
                    .parens parameterCore,
                    .empty,
                    bodyPlan]
                  rcases physicalEvidence with
                    ⟨sourcePlan, candidateEq, relation⟩
                  injection candidateEq with sourcePlanEq
                  subst sourcePlan
                  have innerRelation : TokenSlot.ListMatches inner.slots
                      (PhysicalTokens tokens origin finish) := by
                    exact relation.lambdaWithoutReturnToPlain
                  have innerAnchored : inner.WellAnchored := by
                    apply TokenPlan.lambdaInner_wellAnchored
                    · exact TokenPlan.WellAnchored.empty
                    · exact bracedBodyTokenPlan?_wellAnchored
                        body bodyPlan bodyEq
                  have enclosed := TokenPlanEvidence.enclose
                    (TokenPlanEvidence.some innerRelation)
                    (fun plan success => by
                      simp only [Option.some.injEq] at success
                      subst plan
                      exact innerAnchored)
                    witness.consumed
                  rw [lambdaTokenPlan_eq_mapM]
                  simpa [ruleTokenPlan?, parameterEq, bodyEq,
                    parameterCore, inner] using enclosed
          | some returnValue =>
              cases typeEq : typeExprPlan? returnValue.2 with
              | none =>
                  simp [parameterEq, typeEq, TokenPlanEvidence]
                    at physicalEvidence
              | some typePlan =>
                  cases bodyEq : bodyTokenPlan? .braced body with
                  | none =>
                      simp [parameterEq, typeEq, bodyEq,
                        TokenPlanEvidence] at physicalEvidence
                  | some bodyPlan =>
                      simp only [parameterEq, typeEq, bodyEq]
                        at physicalEvidence
                      let parameterCore :=
                        TokenPlan.commaSeparated parameterPlans
                      let returnPlan := TokenPlan.append
                        (.plain (.symbol .arrow)) typePlan
                      let inner := TokenPlan.concat [
                        .plain (.hardKeyword .lamKw),
                        .parens parameterCore,
                        returnPlan,
                        bodyPlan]
                      rcases physicalEvidence with
                        ⟨sourcePlan, candidateEq, relation⟩
                      injection candidateEq with sourcePlanEq
                      subst sourcePlan
                      have innerRelation : TokenSlot.ListMatches inner.slots
                          (PhysicalTokens tokens origin finish) := by
                        exact relation.lambdaWithReturnToPlain
                      have innerAnchored : inner.WellAnchored := by
                        apply TokenPlan.lambdaInner_wellAnchored
                        · exact TokenPlan.WellAnchored.append
                            (TokenPlan.WellAnchored.plain _)
                            (typeExprPlan?_wellAnchored
                              returnValue.2 typePlan typeEq)
                        · exact bracedBodyTokenPlan?_wellAnchored
                            body bodyPlan bodyEq
                      have enclosed := TokenPlanEvidence.enclose
                        (TokenPlanEvidence.some innerRelation)
                        (fun plan success => by
                          simp only [Option.some.injEq] at success
                          subst plan
                          exact innerAnchored)
                        witness.consumed
                      rw [lambdaTokenPlan_eq_mapM]
                      simpa [ruleTokenPlan?, parameterEq, typeEq, bodyEq,
                        parameterCore, returnPlan, inner] using enclosed

end Solcore.Surface.Multi
