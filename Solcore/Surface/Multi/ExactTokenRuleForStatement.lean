import Solcore.Surface.Multi.ExactTokenRuleForHelpers
import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

private theorem forInitTokenPlans?_eq_mapM (items : List ForInitItem) :
    forInitTokenPlans? items = items.mapM forInitTokenPlan? := by
  induction items with
  | nil => simp [forInitTokenPlans?]
  | cons head tail induction =>
      simp [forInitTokenPlans?, List.mapM_cons, induction]

private theorem forPostTokenPlans?_eq_mapM (items : List ForPostItem) :
    forPostTokenPlans? items = items.mapM forPostTokenPlan? := by
  induction items with
  | nil => simp [forPostTokenPlans?]
  | cons head tail induction =>
      simp [forPostTokenPlans?, List.mapM_cons, induction]

private theorem ruleTokenPlan?_forInitItem (item : ForInitItem) :
    ruleTokenPlan? .forInitItem item = forInitTokenPlan? item := by
  rfl

private theorem ruleTokenPlan?_forPostItem (item : ForPostItem) :
    ruleTokenPlan? .forPostItem item = forPostTokenPlan? item := by
  rfl

private theorem ruleAtomValues_tokenPlan?
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

private theorem forInitRuleValues_tokenPlans?
    (items : List ForInitItem) :
    items.mapM (ruleTokenPlan? .forInitItem) =
      forInitTokenPlans? items := by
  change items.mapM forInitTokenPlan? = forInitTokenPlans? items
  exact (forInitTokenPlans?_eq_mapM items).symm

private theorem forPostRuleValues_tokenPlans?
    (items : List ForPostItem) :
    items.mapM (ruleTokenPlan? .forPostItem) =
      forPostTokenPlans? items := by
  change items.mapM forPostTokenPlan? = forPostTokenPlans? items
  exact (forPostTokenPlans?_eq_mapM items).symm

private theorem TokenSlot.ListMatches.forStatementToPlain
    {forSpan openSpan firstSemiSpan secondSemiSpan closeSpan : SourceSpan}
    {initializers condition post body : TokenPlan} {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat [
        .exact (.hardKeyword .forKw) forSpan,
        .exact (.symbol .leftParen) openSpan,
        initializers,
        .exact (.symbol .semicolon) firstSemiSpan,
        condition,
        .exact (.symbol .semicolon) secondSemiSpan,
        post,
        .exact (.symbol .rightParen) closeSpan,
        body]).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.concat [
        .plain (.hardKeyword .forKw),
        .plain (.symbol .leftParen),
        initializers,
        .plain (.symbol .semicolon),
        condition,
        .plain (.symbol .semicolon),
        post,
        .plain (.symbol .rightParen),
        body]).slots actual := by
  simp only [TokenPlan.concat, List.flatMap_cons, List.flatMap_nil,
    TokenPlan.exact, TokenPlan.plain, List.append_nil,
    List.singleton_append] at relation ⊢
  cases relation with
  | required forMatch afterFor =>
      cases afterFor with
      | required openMatch afterOpen =>
          rcases afterOpen.split_append with
            ⟨initializerActual, afterInitializerActual, rfl,
              initializerRelation, afterInitializerRelation⟩
          cases afterInitializerRelation with
          | required firstSemiMatch afterFirstSemi =>
              rcases afterFirstSemi.split_append with
                ⟨conditionActual, afterConditionActual, rfl,
                  conditionRelation, afterConditionRelation⟩
              cases afterConditionRelation with
              | required secondSemiMatch afterSecondSemi =>
                  rcases afterSecondSemi.split_append with
                    ⟨postActual, afterPostActual, rfl,
                      postRelation, afterPostRelation⟩
                  cases afterPostRelation with
                  | required closeMatch bodyRelation =>
                      exact .required forMatch.toPlain <|
                        .required openMatch.toPlain <|
                          initializerRelation.append <|
                            .required firstSemiMatch.toPlain <|
                              conditionRelation.append <|
                                .required secondSemiMatch.toPlain <|
                                  postRelation.append <|
                                    .required closeMatch.toPlain bodyRelation

private theorem TokenPlan.forStatement_wellAnchored
    {initializers condition post body : TokenPlan}
    (initializersAnchored : initializers.WellAnchored)
    (conditionAnchored : condition.WellAnchored)
    (postAnchored : post.WellAnchored)
    (bodyAnchored : body.WellAnchored) :
    (TokenPlan.concat [
      .plain (.hardKeyword .forKw),
      .plain (.symbol .leftParen),
      initializers,
      .plain (.symbol .semicolon),
      condition,
      .plain (.symbol .semicolon),
      post,
      .plain (.symbol .rightParen),
      body]).WellAnchored := by
  apply TokenPlan.WellAnchored.concat
  intro plan member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact TokenPlan.WellAnchored.plain _
  · exact TokenPlan.WellAnchored.plain _
  · exact initializersAnchored
  · exact TokenPlan.WellAnchored.plain _
  · exact conditionAnchored
  · exact TokenPlan.WellAnchored.plain _
  · exact postAnchored
  · exact TokenPlan.WellAnchored.plain _
  · exact bodyAnchored

theorem forStatement_tokenPlanSound :
    GrammarRuleTokenPlanSound .forStatement := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | forStatement origin finish forKeyword openParen initializers
      firstSemicolon condition secondSemicolon post closeParen body witness =>
      change List ForInitItem at initializers
      change Expression at condition
      change List ForPostItem at post
      change Body at body
      change TokenPlanEvidence
        (statementTokenPlan? false
          (sourceLoc witness
            (.forLoop initializers condition post body) : Statement))
        (PhysicalTokens tokens origin finish)
      rw [← inputEq] at inputEvidence
      have sourceCandidateEq : input.tokenPlan? sourceRuleTokenPlanLayout = (do
          let initializerPlans ← forInitTokenPlans? initializers
          let conditionPlan ← expressionTokenPlan? condition
          let postPlans ← forPostTokenPlans? post
          let bodyPlan ← bodyTokenPlan? .braced body
          pure (TokenPlan.concat [
            .exact (.hardKeyword .forKw) forKeyword.span,
            .exact (.symbol .leftParen) openParen.span,
            .commaSeparated initializerPlans,
            .exact (.symbol .semicolon) firstSemicolon.span,
            conditionPlan,
            .exact (.symbol .semicolon) secondSemicolon.span,
            .commaSeparated postPlans,
            .exact (.symbol .rightParen) closeParen.span,
            bodyPlan])) := by
        rw [inputEq]
        simp only [m2cV1, m2cV1Rhs, Grammar.sequence,
          Grammar.nonterminal, Grammar.hardKeyword, Grammar.symbol,
          Grammar.terminal, Grammar.list0, EbnfExpr.children]
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
        rw [EbnfValue.tokenPlan?_ruleAtom]
        rw [EbnfValues.tokenPlan?_cons]
        rw [EbnfValue.tokenPlan?_terminalAtom]
        rw [EbnfValues.tokenPlan?_cons]
        rw [EbnfValue.tokenPlan?_list0]
        rw [EbnfValues.tokenPlan?_cons]
        rw [EbnfValue.tokenPlan?_terminalAtom]
        rw [EbnfValues.tokenPlan?_cons]
        rw [EbnfValue.tokenPlan?_ruleAtom]
        rw [EbnfValues.tokenPlan?_nil]
        rw [ruleAtomValues_tokenPlan? .forInitItem initializers,
          ruleAtomValues_tokenPlan? .forPostItem post]
        simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?,
          MatchedTerminal.physicalTokenPlan_hardKeyword,
          MatchedTerminal.physicalTokenPlan_symbol]
        rw [forInitRuleValues_tokenPlans?, forPostRuleValues_tokenPlans?]
        cases initializerPlansEq : forInitTokenPlans? initializers <;>
        cases conditionPlanEq : expressionTokenPlan? condition <;>
        cases postPlansEq : forPostTokenPlans? post <;>
        cases bodyPlanEq : bodyTokenPlan? .braced body <;>
        simp [TokenPlan.concat_cons]
      have physicalEvidence := inputEvidence.candidate_eq sourceCandidateEq
      cases initializersEq : forInitTokenPlans? initializers with
      | none =>
          simp [initializersEq, TokenPlanEvidence] at physicalEvidence
      | some initializerPlans =>
          cases conditionEq : expressionTokenPlan? condition with
          | none =>
              simp [initializersEq, conditionEq, TokenPlanEvidence]
                at physicalEvidence
          | some conditionPlan =>
              cases postEq : forPostTokenPlans? post with
              | none =>
                  simp [initializersEq, conditionEq, postEq,
                    TokenPlanEvidence] at physicalEvidence
              | some postPlans =>
                  cases bodyEq : bodyTokenPlan? .braced body with
                  | none =>
                      simp [initializersEq, conditionEq, postEq, bodyEq,
                        TokenPlanEvidence] at physicalEvidence
                  | some bodyPlan =>
                      simp only [initializersEq, conditionEq, postEq, bodyEq]
                        at physicalEvidence
                      change expressionTokenPlanAt? .annotation condition =
                        some conditionPlan at conditionEq
                      let initializerCore :=
                        TokenPlan.commaSeparated initializerPlans
                      let postCore := TokenPlan.commaSeparated postPlans
                      let inner := TokenPlan.concat [
                        .plain (.hardKeyword .forKw),
                        .plain (.symbol .leftParen),
                        initializerCore,
                        .plain (.symbol .semicolon),
                        conditionPlan,
                        .plain (.symbol .semicolon),
                        postCore,
                        .plain (.symbol .rightParen),
                        bodyPlan]
                      rcases physicalEvidence with
                        ⟨sourcePlan, candidateEq, relation⟩
                      injection candidateEq with sourcePlanEq
                      subst sourcePlan
                      have innerRelation : TokenSlot.ListMatches inner.slots
                          (PhysicalTokens tokens origin finish) := by
                        exact relation.forStatementToPlain
                      have initializerAnchored :
                          initializerCore.WellAnchored := by
                        exact TokenPlan.WellAnchored.commaSeparated
                          initializerPlans
                          (forInitTokenPlans?_allWellAnchored
                            initializers initializerPlans initializersEq)
                      have postAnchored : postCore.WellAnchored := by
                        exact TokenPlan.WellAnchored.commaSeparated postPlans
                          (forPostTokenPlans?_allWellAnchored
                            post postPlans postEq)
                      have innerAnchored : inner.WellAnchored := by
                        exact TokenPlan.forStatement_wellAnchored
                          initializerAnchored
                          (expressionTokenPlan?_wellAnchored condition
                            conditionPlan conditionEq)
                          postAnchored
                          (bracedBodyTokenPlan?_wellAnchored
                            body bodyPlan bodyEq)
                      have enclosed := TokenPlanEvidence.enclose
                        (TokenPlanEvidence.some innerRelation)
                        (fun plan success => by
                          simp only [Option.some.injEq] at success
                          subst plan
                          exact innerAnchored)
                        witness.consumed
                      simpa [statementTokenPlan?, sourceLoc,
                        initializersEq, conditionEq, postEq, bodyEq,
                        initializerCore, postCore, inner,
                        TokenPlan.concat_cons, TokenPlan.append_assoc]
                        using enclosed

end Solcore.Surface.Multi
