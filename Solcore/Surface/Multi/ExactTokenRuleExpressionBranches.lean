import Solcore.Surface.Multi.ExactTokenExpressionAnchoring
import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRulePassThrough
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false
set_option linter.unnecessarySimpa false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- A checked contextual keyword retains the identifier token that spells it. -/
private theorem MatchedTerminal.physicalTokenPlan_contextualKeyword
    {file : WorkspaceFile} {tokens : List Token}
    (keyword : ContextualKeyword)
    (matched : MatchedTerminal file tokens (.contextualKeyword keyword)) :
    matched.physicalTokenPlan =
      TokenPlan.exact (.identifier keyword.spelling) matched.span := by
  rcases matched with
    ⟨cursor, value, span, terminalAt, matchedEvidence⟩
  cases terminalAt with
  | retained token inRange lookup valid =>
      simp [MatchedTerminal.physicalTokenPlan, TerminalMatches]
        at matchedEvidence ⊢
      rw [matchedEvidence]
  | endOfFile atEnd =>
      simp [TerminalMatches] at matchedEvidence

private theorem TokenPlanEvidence.exactMiddleToPlain
    {kind : TokenKind} {span : SourceSpan}
    {beforePlan afterPlan : TokenPlan} {actual : List Token}
    (evidence : TokenPlanEvidence
      (Option.some ((beforePlan.append (.exact kind span)).append afterPlan)) actual) :
    TokenPlanEvidence
      (Option.some ((beforePlan.append (.plain kind)).append afterPlan)) actual := by
  rcases evidence with ⟨plan, candidateEq, relation⟩
  simp only [Option.some.injEq] at candidateEq
  subst plan
  rcases relation.split_append with
    ⟨prefixExactActual, suffixActual, actualEq,
      prefixExactRelation, suffixRelation⟩
  rcases prefixExactRelation.split_append with
    ⟨prefixActual, exactActual, prefixExactEq,
      prefixRelation, exactRelation⟩
  have plainRelation := exactRelation.requiredHeadToPlain
  apply TokenPlanEvidence.some
  rw [actualEq, prefixExactEq, List.append_assoc]
  simpa [TokenPlan.append, TokenPlan.exact, TokenPlan.plain,
    ExpectedToken.exact] using
    (prefixRelation.append plainRelation).append suffixRelation

/-- Forget two fixed-token endpoint constraints while retaining three child
plans and their exact token evidence. -/
private theorem TokenSlot.ListMatches.twoFixedBetweenToPlain
    {firstKind secondKind : TokenKind}
    {firstSpan secondSpan : SourceSpan}
    {before middle after : TokenPlan} {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat [
        before, .exact firstKind firstSpan, middle,
        .exact secondKind secondSpan, after]).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.concat [
        before, .plain firstKind, middle,
        .plain secondKind, after]).slots actual := by
  simp only [TokenPlan.concat, List.flatMap_cons, List.flatMap_nil,
    TokenPlan.exact, TokenPlan.plain, List.append_nil,
    List.singleton_append] at relation ⊢
  rcases relation.split_append with
    ⟨beforeActual, afterBeforeActual, rfl,
      beforeRelation, afterBeforeRelation⟩
  cases afterBeforeRelation with
  | required firstMatch afterFirstRelation =>
      rcases afterFirstRelation.split_append with
        ⟨middleActual, afterMiddleActual, rfl,
          middleRelation, afterMiddleRelation⟩
      cases afterMiddleRelation with
      | required secondMatch afterRelation =>
          exact beforeRelation.append <|
            .required firstMatch.toPlain <|
              middleRelation.append <|
                .required secondMatch.toPlain afterRelation

/-- Forget three fixed-keyword endpoint constraints while retaining the three
interleaved child plans and their exact token evidence. -/
private theorem TokenSlot.ListMatches.threeFixedInterleavedToPlain
    {firstKind secondKind thirdKind : TokenKind}
    {firstSpan secondSpan thirdSpan : SourceSpan}
    {firstPlan secondPlan thirdPlan : TokenPlan} {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat [
        .exact firstKind firstSpan, firstPlan,
        .exact secondKind secondSpan, secondPlan,
        .exact thirdKind thirdSpan, thirdPlan]).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.concat [
        .plain firstKind, firstPlan,
        .plain secondKind, secondPlan,
        .plain thirdKind, thirdPlan]).slots actual := by
  simp only [TokenPlan.concat, List.flatMap_cons, List.flatMap_nil,
    TokenPlan.exact, TokenPlan.plain, List.append_nil,
    List.singleton_append] at relation ⊢
  cases relation with
  | required firstMatch afterFirst =>
      rcases afterFirst.split_append with
        ⟨firstActual, afterFirstActual, rfl,
          firstRelation, afterFirstRelation⟩
      cases afterFirstRelation with
      | required secondMatch afterSecond =>
          rcases afterSecond.split_append with
            ⟨secondActual, afterSecondActual, rfl,
              secondRelation, afterSecondRelation⟩
          cases afterSecondRelation with
          | required thirdMatch thirdRelation =>
              exact .required firstMatch.toPlain <|
                firstRelation.append <|
                  .required secondMatch.toPlain <|
                    secondRelation.append <|
                      .required thirdMatch.toPlain thirdRelation

private abbrev conditionalSourceBranches : List EbnfExpr := [
  .sequence [
    .atom (.terminal (.hardKeyword .ifKw)),
    .atom (.nonterminal .conditional),
    .atom (.terminal (.contextualKeyword .thenKw)),
    .atom (.nonterminal .conditional),
    .atom (.terminal (.hardKeyword .elseKw)),
    .atom (.nonterminal .conditional)],
  .sequence [
    .atom (.nonterminal .logicalOr),
    .optional (.sequence [
      .atom (.terminal (.symbol .question)),
      .atom (.nonterminal .conditional),
      .atom (.terminal (.symbol .colon)),
      .atom (.nonterminal .conditional)])]
]

private abbrev equalitySourceExpr : EbnfExpr := .sequence [
  .atom (.nonterminal .relational),
  .optional (.sequence [
    .group (.choice [
      .atom (.terminal (.symbol .equalEqual)),
      .atom (.terminal (.symbol .notEqual))]),
    .atom (.nonterminal .relational)])
]

private abbrev relationalSourceExpr : EbnfExpr := .sequence [
  .atom (.nonterminal .bitOr),
  .optional (.sequence [
    .group (.choice [
      .atom (.terminal (.symbol .less)),
      .atom (.terminal (.symbol .greater)),
      .atom (.terminal (.symbol .lessEqual)),
      .atom (.terminal (.symbol .greaterEqual))]),
    .atom (.nonterminal .bitOr)])
]

private abbrev prefixSourceBranches : List EbnfExpr := [
  .sequence [
    .atom (.terminal (.symbol .bang)),
    .atom (.nonterminal .prefix)],
  .atom (.nonterminal .postfix)
]

private theorem relationalGreaterEqualChoice_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (operator : MatchedTerminal file tokens (.symbol .greaterEqual)) :
    (EbnfValue.choice [
      .atom (.terminal (.symbol .less)),
      .atom (.terminal (.symbol .greater)),
      .atom (.terminal (.symbol .lessEqual)),
      .atom (.terminal (.symbol .greaterEqual))]
      ⟨⟨3, by decide⟩,
        EbnfValue.terminalAtom (.symbol .greaterEqual) operator⟩).tokenPlan?
        sourceRuleTokenPlanLayout =
      some (TokenPlan.exact (.symbol .greaterEqual) operator.span) := by
  calc
    _ = (EbnfValue.terminalAtom (file := file) (tokens := tokens)
          (.symbol .greaterEqual) operator).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = some operator.physicalTokenPlan :=
        EbnfValue.tokenPlan?_terminalAtom
          sourceRuleTokenPlanLayout _ operator
    _ = _ := by rw [MatchedTerminal.physicalTokenPlan_symbol]

private def relationalGreaterEqualInput
    {file : WorkspaceFile} {tokens : List Token}
    (left : Expression)
    (operator : MatchedTerminal file tokens (.symbol .greaterEqual))
    (right : Expression) :
    EbnfValue file tokens relationalSourceExpr :=
  EbnfValue.sequence _ <|
    EbnfValues.cons _ _ (EbnfValue.ruleAtom .bitOr left) <|
      EbnfValues.cons _ _ (EbnfValue.optional _ (some <|
        EbnfValue.sequence _ <|
          EbnfValues.cons _ _ (EbnfValue.group _ <|
            EbnfValue.choice _ ⟨⟨3, by decide⟩,
              EbnfValue.terminalAtom (.symbol .greaterEqual) operator⟩) <|
            EbnfValues.cons _ _ (EbnfValue.ruleAtom .bitOr right)
              EbnfValues.nil)) EbnfValues.nil

private theorem relationalGreaterEqualInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (left : Expression)
    (operator : MatchedTerminal file tokens (.symbol .greaterEqual))
    (right : Expression) :
    (relationalGreaterEqualInput left operator right).tokenPlan?
        sourceRuleTokenPlanLayout =
      (do
        let leftPlan ← expressionTokenPlanAt? .bitOr left
        let rightPlan ← expressionTokenPlanAt? .bitOr right
        pure (TokenPlan.concat [
          leftPlan,
          TokenPlan.exact (.symbol .greaterEqual) operator.span,
          rightPlan])) := by
  change RuleValue .bitOr at left right
  unfold relationalGreaterEqualInput
  rw [EbnfValue.tokenPlan?_sequence]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_ruleAtom]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_optional_some]
  rw [EbnfValue.tokenPlan?_sequence]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_group]
  rw [relationalGreaterEqualChoice_tokenPlan?]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_ruleAtom]
  rw [EbnfValues.tokenPlan?_nil]
  simp [sourceRuleTokenPlanLayout, ruleTokenPlan?,
    bitOrExpressionTokenPlan?, TokenPlan.concat] <;>
    cases leftEq : expressionTokenPlanAt? .bitOr left <;>
    cases rightEq : expressionTokenPlanAt? .bitOr right <;>
    simp [TokenPlan.append]

/-- Add the consumed source span to an infix-expression core whose child and
operator plans already match the complete parser interval. -/
private theorem TokenPlanEvidence.encloseInfix
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (level : ExpressionTokenLevel)
    (left right : Expression) (operator : Located InfixOperator)
    (witness : ConsumedSpanWitness file tokens origin finish)
    (evidence : TokenPlanEvidence
      (do
        let leftPlan ← expressionTokenPlanAt? level left
        let rightPlan ← expressionTokenPlanAt? level right
        pure (TokenPlan.concat [
          leftPlan, infixOperatorTokenPlan operator, rightPlan]))
      (PhysicalTokens tokens origin finish)) :
    TokenPlanEvidence
      (do
        let leftPlan ← expressionTokenPlanAt? level left
        let rightPlan ← expressionTokenPlanAt? level right
        pure (TokenPlan.enclose witness.span (TokenPlan.concat [
          leftPlan, infixOperatorTokenPlan operator, rightPlan])))
      (PhysicalTokens tokens origin finish) := by
  rcases evidence with ⟨plan, candidateEq, relation⟩
  rcases Option.bind_eq_some_iff.mp candidateEq with
    ⟨leftPlan, leftEq, remainingEq⟩
  rcases Option.bind_eq_some_iff.mp remainingEq with
    ⟨rightPlan, rightEq, planEq⟩
  change Option.some (TokenPlan.concat [
    leftPlan, infixOperatorTokenPlan operator, rightPlan]) =
      Option.some plan at planEq
  injection planEq with planEq
  subst plan
  have coreEvidence : TokenPlanEvidence
      (Option.some (TokenPlan.concat [
        leftPlan, infixOperatorTokenPlan operator, rightPlan])) _ :=
    ⟨_, rfl, relation⟩
  have enclosed := coreEvidence.enclose
    (fun enclosedPlan success => by
      injection success with planEq
      subst enclosedPlan
      apply TokenPlan.WellAnchored.concat
      intro component member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with member | member | member
      · subst component
        exact expressionTokenPlanAt?_wellAnchored
          level left leftPlan leftEq
      · subst component
        exact infixOperatorTokenPlan_wellAnchored operator
      · subst component
        exact expressionTokenPlanAt?_wellAnchored
          level right rightPlan rightEq)
    witness.consumed
  simpa [leftEq, rightEq] using enclosed

/-- Add the consumed source span to a prefix-expression core. -/
private theorem TokenPlanEvidence.enclosePrefix
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (operand : Expression) (operator : Located PrefixOperator)
    (witness : ConsumedSpanWitness file tokens origin finish)
    (evidence : TokenPlanEvidence
      (do
        let operandPlan ← expressionTokenPlanAt? .prefix operand
        pure ((prefixOperatorTokenPlan operator).append operandPlan))
      (PhysicalTokens tokens origin finish)) :
    TokenPlanEvidence
      (do
        let operandPlan ← expressionTokenPlanAt? .prefix operand
        pure (TokenPlan.enclose witness.span
          ((prefixOperatorTokenPlan operator).append operandPlan)))
      (PhysicalTokens tokens origin finish) := by
  rcases evidence with ⟨plan, candidateEq, relation⟩
  rcases Option.bind_eq_some_iff.mp candidateEq with
    ⟨operandPlan, operandEq, planEq⟩
  change Option.some ((prefixOperatorTokenPlan operator).append operandPlan) =
    Option.some plan at planEq
  injection planEq with planEq
  subst plan
  have coreEvidence : TokenPlanEvidence
      (Option.some ((prefixOperatorTokenPlan operator).append operandPlan)) _ :=
    ⟨_, rfl, relation⟩
  have enclosed := coreEvidence.enclose
    (fun enclosedPlan success => by
      injection success with planEq
      subst enclosedPlan
      exact TokenPlan.WellAnchored.append
        (prefixOperatorTokenPlan_wellAnchored operator)
        (expressionTokenPlanAt?_wellAnchored
          .prefix operand operandPlan operandEq))
    witness.consumed
  simpa [operandEq] using enclosed

/-- Annotation-expression reductions preserve the source token plan. -/
theorem annotation_tokenPlanSound :
    GrammarRuleTokenPlanSound .annotation := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | annotationNone =>
      exact RuleReduction.SemanticPassThrough.tokenPlanEvidence
        (by apply RuleReduction.SemanticPassThrough.annotationNone)
        inputEvidence
  | annotationSome origin finish expression colon typeValue witness =>
      change EbnfValue file tokens (.sequence [
        .atom (.nonterminal .conditional),
        .optional (.sequence [
          .atom (.terminal (.symbol .colon)),
          .atom (.nonterminal .type)])]) at input
      rw [← inputEq] at inputEvidence
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          (do
            let expressionPlan ← conditionalExpressionTokenPlan? expression
            let typePlan ← typeExprPlan? typeValue
            pure ((expressionPlan.append
              (TokenPlan.exact (.symbol .colon) colon.span)).append
              typePlan)) := by
        rw [inputEq]
        simp [EbnfExpr.children, sourceRuleTokenPlanLayout,
          ruleTokenPlan?, MatchedTerminal.physicalTokenPlan_symbol,
          TokenPlan.append_assoc] <;>
          cases conditionalEq : conditionalExpressionTokenPlan? expression <;>
          cases typeEq : typeExprPlan? typeValue <;>
          simp
      have physicalEvidence := inputEvidence.candidate_eq candidateEq
      rcases physicalEvidence with ⟨plan, planEq, relation⟩
      unfold conditionalExpressionTokenPlan? at planEq
      cases expressionEq : expressionTokenPlanAt? .conditional expression with
      | none => simp [expressionEq] at planEq
      | some expressionPlan =>
          cases typeEq : typeExprPlan? typeValue with
          | none => simp [expressionEq, typeEq] at planEq
          | some typePlan =>
              simp [expressionEq, typeEq] at planEq
              subst plan
              have exactEvidence : TokenPlanEvidence
                  (some ((expressionPlan.append
                    (TokenPlan.exact (.symbol .colon) colon.span)).append
                    typePlan)) _ := ⟨_, rfl, relation⟩
              have weakened := exactEvidence.exactMiddleToPlain
              have enclosed := weakened.enclose
                (fun enclosedPlan success => by
                  injection success with planEq
                  subst enclosedPlan
                  apply TokenPlan.WellAnchored.append
                  · exact TokenPlan.WellAnchored.append
                      (expressionTokenPlanAt?_wellAnchored
                      .conditional expression expressionPlan expressionEq)
                      (TokenPlan.WellAnchored.plain _)
                  · exact typeExprPlanAt?_wellAnchored
                      false typeValue typePlan typeEq)
                witness.consumed
              simpa [ruleTokenPlan?, annotationExpressionTokenPlan?,
                conditionalExpressionTokenPlan?, expressionTokenPlanAt?,
                sourceLoc, expressionEq, typeEq,
                TokenPlan.append_assoc] using enclosed

/-- Conditional-expression reductions preserve the source token plan. -/
theorem conditional_tokenPlanSound :
    GrammarRuleTokenPlanSound .conditional := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | conditionalLogical =>
      exact RuleReduction.SemanticPassThrough.tokenPlanEvidence
        (by apply RuleReduction.SemanticPassThrough.conditionalLogical)
        inputEvidence
  | conditionalKeyword origin finish ifKeyword condition thenKeyword
      thenBranch elseKeyword elseBranch witness =>
      change EbnfValue file tokens
        (.choice conditionalSourceBranches) at input
      rw [← inputEq] at inputEvidence
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          (do
            let conditionPlan ← expressionTokenPlanAt?
              .conditional condition
            let thenPlan ← expressionTokenPlanAt?
              .conditional thenBranch
            let elsePlan ← expressionTokenPlanAt?
              .conditional elseBranch
            pure (TokenPlan.concat [
              .exact (.hardKeyword .ifKw) ifKeyword.span,
              conditionPlan,
              .exact (.identifier ContextualKeyword.thenKw.spelling)
                thenKeyword.span,
              thenPlan,
              .exact (.hardKeyword .elseKw) elseKeyword.span,
              elsePlan])) := by
        rw [inputEq]
        simp [conditionalSourceBranches, EbnfExpr.children,
          sourceRuleTokenPlanLayout, ruleTokenPlan?,
          conditionalExpressionTokenPlan?,
          MatchedTerminal.physicalTokenPlan_hardKeyword,
          MatchedTerminal.physicalTokenPlan_contextualKeyword,
          TokenPlan.concat] <;>
          cases conditionEq : expressionTokenPlanAt?
            .conditional condition <;>
          cases thenEq : expressionTokenPlanAt?
            .conditional thenBranch <;>
          cases elseEq : expressionTokenPlanAt?
            .conditional elseBranch <;>
          simp [TokenPlan.append]
      have physicalEvidence := inputEvidence.candidate_eq candidateEq
      rcases physicalEvidence with ⟨plan, planEq, relation⟩
      cases conditionEq : expressionTokenPlanAt?
          .conditional condition with
      | none => simp [conditionEq] at planEq
      | some conditionPlan =>
          cases thenEq : expressionTokenPlanAt?
              .conditional thenBranch with
          | none => simp [conditionEq, thenEq] at planEq
          | some thenPlan =>
              cases elseEq : expressionTokenPlanAt?
                  .conditional elseBranch with
              | none => simp [conditionEq, thenEq, elseEq] at planEq
              | some elsePlan =>
                  simp [conditionEq, thenEq, elseEq] at planEq
                  subst plan
                  have concatRelation : TokenSlot.ListMatches
                      (TokenPlan.concat [
                        .exact (.hardKeyword .ifKw) ifKeyword.span,
                        conditionPlan,
                        .exact (.identifier
                          ContextualKeyword.thenKw.spelling)
                          thenKeyword.span,
                        thenPlan,
                        .exact (.hardKeyword .elseKw) elseKeyword.span,
                        elsePlan]).slots
                      (PhysicalTokens tokens origin finish) := by
                    simpa [TokenPlan.concat, TokenPlan.append,
                      List.append_assoc] using relation
                  have weakenedRelation :=
                    concatRelation.threeFixedInterleavedToPlain
                  have coreEvidence :=
                    TokenPlanEvidence.some weakenedRelation
                  have enclosed := coreEvidence.enclose
                    (fun enclosedPlan success => by
                      injection success with planEq
                      subst enclosedPlan
                      apply TokenPlan.WellAnchored.concat
                      intro component member
                      simp only [List.mem_cons, List.not_mem_nil,
                        or_false] at member
                      rcases member with
                        member | member | member | member | member | member
                      · subst component
                        exact TokenPlan.WellAnchored.plain _
                      · subst component
                        exact expressionTokenPlanAt?_wellAnchored
                          .conditional condition conditionPlan conditionEq
                      · subst component
                        exact TokenPlan.WellAnchored.plain _
                      · subst component
                        exact expressionTokenPlanAt?_wellAnchored
                          .conditional thenBranch thenPlan thenEq
                      · subst component
                        exact TokenPlan.WellAnchored.plain _
                      · subst component
                        exact expressionTokenPlanAt?_wellAnchored
                          .conditional elseBranch elsePlan elseEq)
                    witness.consumed
                  simpa [ruleTokenPlan?,
                    conditionalExpressionTokenPlan?,
                    expressionTokenPlanAt?, sourceLoc,
                    conditionEq, thenEq, elseEq] using enclosed
  | conditionalTernary origin finish condition question thenBranch colon
      elseBranch witness =>
      change EbnfValue file tokens
        (.choice conditionalSourceBranches) at input
      rw [← inputEq] at inputEvidence
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          (do
            let conditionPlan ← expressionTokenPlanAt? .logicalOr condition
            let thenPlan ← expressionTokenPlanAt?
              .conditional thenBranch
            let elsePlan ← expressionTokenPlanAt?
              .conditional elseBranch
            pure (TokenPlan.concat [
              conditionPlan,
              .exact (.symbol .question) question.span,
              thenPlan,
              .exact (.symbol .colon) colon.span,
              elsePlan])) := by
        rw [inputEq]
        simp [conditionalSourceBranches, EbnfExpr.children,
          sourceRuleTokenPlanLayout, ruleTokenPlan?,
          conditionalExpressionTokenPlan?, logicalOrExpressionTokenPlan?,
          MatchedTerminal.physicalTokenPlan_symbol,
          TokenPlan.concat] <;>
          cases conditionEq : expressionTokenPlanAt?
            .logicalOr condition <;>
          cases thenEq : expressionTokenPlanAt?
            .conditional thenBranch <;>
          cases elseEq : expressionTokenPlanAt?
            .conditional elseBranch <;>
          simp [TokenPlan.append]
      have physicalEvidence := inputEvidence.candidate_eq candidateEq
      rcases physicalEvidence with ⟨plan, planEq, relation⟩
      cases conditionEq : expressionTokenPlanAt? .logicalOr condition with
      | none => simp [conditionEq] at planEq
      | some conditionPlan =>
          cases thenEq : expressionTokenPlanAt?
              .conditional thenBranch with
          | none => simp [conditionEq, thenEq] at planEq
          | some thenPlan =>
              cases elseEq : expressionTokenPlanAt?
                  .conditional elseBranch with
              | none => simp [conditionEq, thenEq, elseEq] at planEq
              | some elsePlan =>
                  simp [conditionEq, thenEq, elseEq] at planEq
                  subst plan
                  have concatRelation : TokenSlot.ListMatches
                      (TokenPlan.concat [
                        conditionPlan,
                        .exact (.symbol .question) question.span,
                        thenPlan,
                        .exact (.symbol .colon) colon.span,
                        elsePlan]).slots
                      (PhysicalTokens tokens origin finish) := by
                    simpa [TokenPlan.concat, TokenPlan.append,
                      List.append_assoc] using relation
                  have weakenedRelation :=
                    concatRelation.twoFixedBetweenToPlain
                  have coreEvidence :=
                    TokenPlanEvidence.some weakenedRelation
                  have enclosed := coreEvidence.enclose
                    (fun enclosedPlan success => by
                      injection success with planEq
                      subst enclosedPlan
                      apply TokenPlan.WellAnchored.concat
                      intro component member
                      simp only [List.mem_cons, List.not_mem_nil,
                        or_false] at member
                      rcases member with
                        member | member | member | member | member
                      · subst component
                        exact expressionTokenPlanAt?_wellAnchored
                          .logicalOr condition conditionPlan conditionEq
                      · subst component
                        exact TokenPlan.WellAnchored.plain _
                      · subst component
                        exact expressionTokenPlanAt?_wellAnchored
                          .conditional thenBranch thenPlan thenEq
                      · subst component
                        exact TokenPlan.WellAnchored.plain _
                      · subst component
                        exact expressionTokenPlanAt?_wellAnchored
                          .conditional elseBranch elsePlan elseEq)
                    witness.consumed
                  simpa [ruleTokenPlan?,
                    conditionalExpressionTokenPlan?,
                    expressionTokenPlanAt?, sourceLoc,
                    conditionEq, thenEq, elseEq] using enclosed

/-- Equality-expression reductions preserve the source token plan. -/
theorem equality_tokenPlanSound :
    GrammarRuleTokenPlanSound .equality := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | equalityNone =>
      exact RuleReduction.SemanticPassThrough.tokenPlanEvidence
        (by apply RuleReduction.SemanticPassThrough.equalityNone)
        inputEvidence
  | equalityEqual origin finish left operator right witness =>
      change EbnfValue file tokens equalitySourceExpr at input
      rw [← inputEq] at inputEvidence
      let locatedOperator :=
        RuleReduction.infixOperator operator (.equal operator)
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          (do
            let leftPlan ← expressionTokenPlanAt? .relational left
            let rightPlan ← expressionTokenPlanAt? .relational right
            pure (TokenPlan.concat [
              leftPlan, infixOperatorTokenPlan locatedOperator,
              rightPlan])) := by
        rw [inputEq]
        simp [equalitySourceExpr, EbnfExpr.children,
          sourceRuleTokenPlanLayout, ruleTokenPlan?,
          relationalExpressionTokenPlan?, locatedOperator,
          RuleReduction.infixOperator, RuleReduction.terminalLoc,
          infixOperatorTokenPlan,
          MatchedTerminal.physicalTokenPlan_symbol,
          TokenPlan.concat] <;>
          cases leftEq : expressionTokenPlanAt? .relational left <;>
          cases rightEq : expressionTokenPlanAt? .relational right <;>
          simp [TokenPlan.append]
      have exactEvidence := inputEvidence.candidate_eq candidateEq
      have enclosed := exactEvidence.encloseInfix
        .relational left right locatedOperator witness
      simpa [ruleTokenPlan?, equalityExpressionTokenPlan?,
        expressionTokenPlanAt?, sourceLoc, locatedOperator,
        RuleReduction.infixOperator, RuleReduction.terminalLoc,
        infixOperatorTokenPlan] using enclosed
  | equalityNotEqual origin finish left operator right witness =>
      change EbnfValue file tokens equalitySourceExpr at input
      rw [← inputEq] at inputEvidence
      let locatedOperator :=
        RuleReduction.infixOperator operator (.notEqual operator)
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          (do
            let leftPlan ← expressionTokenPlanAt? .relational left
            let rightPlan ← expressionTokenPlanAt? .relational right
            pure (TokenPlan.concat [
              leftPlan, infixOperatorTokenPlan locatedOperator,
              rightPlan])) := by
        rw [inputEq]
        simp [equalitySourceExpr, EbnfExpr.children,
          sourceRuleTokenPlanLayout, ruleTokenPlan?,
          relationalExpressionTokenPlan?, locatedOperator,
          RuleReduction.infixOperator, RuleReduction.terminalLoc,
          infixOperatorTokenPlan,
          MatchedTerminal.physicalTokenPlan_symbol,
          TokenPlan.concat] <;>
          cases leftEq : expressionTokenPlanAt? .relational left <;>
          cases rightEq : expressionTokenPlanAt? .relational right <;>
          simp [TokenPlan.append]
      have exactEvidence := inputEvidence.candidate_eq candidateEq
      have enclosed := exactEvidence.encloseInfix
        .relational left right locatedOperator witness
      simpa [ruleTokenPlan?, equalityExpressionTokenPlan?,
        expressionTokenPlanAt?, sourceLoc, locatedOperator,
        RuleReduction.infixOperator, RuleReduction.terminalLoc,
        infixOperatorTokenPlan] using enclosed

/-- Relational-expression reductions preserve the source token plan. -/
theorem relational_tokenPlanSound :
    GrammarRuleTokenPlanSound .relational := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | relationalNone =>
      exact RuleReduction.SemanticPassThrough.tokenPlanEvidence
        (by apply RuleReduction.SemanticPassThrough.relationalNone)
        inputEvidence
  | relationalLess origin finish left operator right witness =>
      change EbnfValue file tokens relationalSourceExpr at input
      rw [← inputEq] at inputEvidence
      let locatedOperator :=
        RuleReduction.infixOperator operator (.less operator)
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          (do
            let leftPlan ← expressionTokenPlanAt? .bitOr left
            let rightPlan ← expressionTokenPlanAt? .bitOr right
            pure (TokenPlan.concat [
              leftPlan, infixOperatorTokenPlan locatedOperator,
              rightPlan])) := by
        rw [inputEq]
        simp [relationalSourceExpr, EbnfExpr.children,
          sourceRuleTokenPlanLayout, ruleTokenPlan?,
          bitOrExpressionTokenPlan?, locatedOperator,
          RuleReduction.infixOperator, RuleReduction.terminalLoc,
          infixOperatorTokenPlan,
          MatchedTerminal.physicalTokenPlan_symbol,
          TokenPlan.concat] <;>
          cases leftEq : expressionTokenPlanAt? .bitOr left <;>
          cases rightEq : expressionTokenPlanAt? .bitOr right <;>
          simp [TokenPlan.append]
      have exactEvidence := inputEvidence.candidate_eq candidateEq
      have enclosed := exactEvidence.encloseInfix
        .bitOr left right locatedOperator witness
      simpa [ruleTokenPlan?, relationalExpressionTokenPlan?,
        expressionTokenPlanAt?, sourceLoc, locatedOperator,
        RuleReduction.infixOperator, RuleReduction.terminalLoc,
        infixOperatorTokenPlan] using enclosed
  | relationalGreater origin finish left operator right witness =>
      change EbnfValue file tokens relationalSourceExpr at input
      rw [← inputEq] at inputEvidence
      let locatedOperator :=
        RuleReduction.infixOperator operator (.greater operator)
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          (do
            let leftPlan ← expressionTokenPlanAt? .bitOr left
            let rightPlan ← expressionTokenPlanAt? .bitOr right
            pure (TokenPlan.concat [
              leftPlan, infixOperatorTokenPlan locatedOperator,
              rightPlan])) := by
        rw [inputEq]
        simp [relationalSourceExpr, EbnfExpr.children,
          sourceRuleTokenPlanLayout, ruleTokenPlan?,
          bitOrExpressionTokenPlan?, locatedOperator,
          RuleReduction.infixOperator, RuleReduction.terminalLoc,
          infixOperatorTokenPlan,
          MatchedTerminal.physicalTokenPlan_symbol,
          TokenPlan.concat] <;>
          cases leftEq : expressionTokenPlanAt? .bitOr left <;>
          cases rightEq : expressionTokenPlanAt? .bitOr right <;>
          simp [TokenPlan.append]
      have exactEvidence := inputEvidence.candidate_eq candidateEq
      have enclosed := exactEvidence.encloseInfix
        .bitOr left right locatedOperator witness
      simpa [ruleTokenPlan?, relationalExpressionTokenPlan?,
        expressionTokenPlanAt?, sourceLoc, locatedOperator,
        RuleReduction.infixOperator, RuleReduction.terminalLoc,
        infixOperatorTokenPlan] using enclosed
  | relationalLessEqual origin finish left operator right witness =>
      change EbnfValue file tokens relationalSourceExpr at input
      rw [← inputEq] at inputEvidence
      let locatedOperator :=
        RuleReduction.infixOperator operator (.lessEqual operator)
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          (do
            let leftPlan ← expressionTokenPlanAt? .bitOr left
            let rightPlan ← expressionTokenPlanAt? .bitOr right
            pure (TokenPlan.concat [
              leftPlan, infixOperatorTokenPlan locatedOperator,
              rightPlan])) := by
        rw [inputEq]
        simp [relationalSourceExpr, EbnfExpr.children,
          sourceRuleTokenPlanLayout, ruleTokenPlan?,
          bitOrExpressionTokenPlan?, locatedOperator,
          RuleReduction.infixOperator, RuleReduction.terminalLoc,
          infixOperatorTokenPlan,
          MatchedTerminal.physicalTokenPlan_symbol,
          TokenPlan.concat] <;>
          cases leftEq : expressionTokenPlanAt? .bitOr left <;>
          cases rightEq : expressionTokenPlanAt? .bitOr right <;>
          simp [TokenPlan.append]
      have exactEvidence := inputEvidence.candidate_eq candidateEq
      have enclosed := exactEvidence.encloseInfix
        .bitOr left right locatedOperator witness
      simpa [ruleTokenPlan?, relationalExpressionTokenPlan?,
        expressionTokenPlanAt?, sourceLoc, locatedOperator,
        RuleReduction.infixOperator, RuleReduction.terminalLoc,
        infixOperatorTokenPlan] using enclosed
  | relationalGreaterEqual origin finish left operator right witness =>
      change EbnfValue file tokens relationalSourceExpr at input
      rw [← inputEq] at inputEvidence
      let locatedOperator :=
        RuleReduction.infixOperator operator (.greaterEqual operator)
      have canonicalEq : input =
          relationalGreaterEqualInput left operator right := by
        rw [inputEq]
        unfold relationalGreaterEqualInput
        rfl
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          (do
            let leftPlan ← expressionTokenPlanAt? .bitOr left
            let rightPlan ← expressionTokenPlanAt? .bitOr right
            pure (TokenPlan.concat [
              leftPlan, infixOperatorTokenPlan locatedOperator,
              rightPlan])) := by
        rw [canonicalEq, relationalGreaterEqualInput_tokenPlan?]
        simp [locatedOperator, RuleReduction.infixOperator,
          RuleReduction.terminalLoc, infixOperatorTokenPlan]
      have exactEvidence := inputEvidence.candidate_eq candidateEq
      have enclosed := exactEvidence.encloseInfix
        .bitOr left right locatedOperator witness
      simpa [ruleTokenPlan?, relationalExpressionTokenPlan?,
        expressionTokenPlanAt?, sourceLoc, locatedOperator,
        RuleReduction.infixOperator, RuleReduction.terminalLoc,
        infixOperatorTokenPlan] using enclosed

/-- Prefix-expression reductions preserve the source token plan. -/
theorem prefix_tokenPlanSound :
    GrammarRuleTokenPlanSound .prefix := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | prefixPostfix =>
      exact RuleReduction.SemanticPassThrough.tokenPlanEvidence
        (by apply RuleReduction.SemanticPassThrough.prefixPostfix)
        inputEvidence
  | prefixLogicalNot origin finish bang operand witness =>
      change EbnfValue file tokens (.choice prefixSourceBranches) at input
      rw [← inputEq] at inputEvidence
      let locatedOperator := RuleReduction.prefixOperator bang
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          (do
            let operandPlan ← expressionTokenPlanAt? .prefix operand
            pure ((prefixOperatorTokenPlan locatedOperator).append
              operandPlan)) := by
        rw [inputEq]
        simp [prefixSourceBranches, EbnfExpr.children,
          sourceRuleTokenPlanLayout, ruleTokenPlan?,
          prefixExpressionTokenPlan?, locatedOperator,
          RuleReduction.prefixOperator, RuleReduction.terminalLoc,
          prefixOperatorTokenPlan,
          MatchedTerminal.physicalTokenPlan_symbol] <;>
          cases operandEq : expressionTokenPlanAt? .prefix operand <;>
          simp [TokenPlan.append]
      have exactEvidence := inputEvidence.candidate_eq candidateEq
      have enclosed := exactEvidence.enclosePrefix
        operand locatedOperator witness
      simpa [ruleTokenPlan?, prefixExpressionTokenPlan?,
        expressionTokenPlanAt?, sourceLoc, locatedOperator,
        RuleReduction.prefixOperator, RuleReduction.terminalLoc,
        prefixOperatorTokenPlan] using enclosed

end Solcore.Surface.Multi
