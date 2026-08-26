import Solcore.Surface.Multi.ExactTokenCoherentRuleSoundness
import Solcore.Surface.Multi.ExactTokenExpressionAnchoring
import Solcore.Surface.Multi.ExactTokenRuleAssemblyStatement
import Solcore.Surface.Multi.ExactTokenRuleAssignmentStatement
import Solcore.Surface.Multi.ExactTokenRuleClassDecl
import Solcore.Surface.Multi.ExactTokenRuleContractConstructor
import Solcore.Surface.Multi.ExactTokenRuleContractDecl
import Solcore.Surface.Multi.ExactTokenRuleContractMember
import Solcore.Surface.Multi.ExactTokenRuleDataDecl
import Solcore.Surface.Multi.ExactTokenRuleDeclarations
import Solcore.Surface.Multi.ExactTokenRuleDirect
import Solcore.Surface.Multi.ExactTokenRuleExpressionBranches
import Solcore.Surface.Multi.ExactTokenRuleExpressionStatementCoherent
import Solcore.Surface.Multi.ExactTokenRuleExpressionFolds
import Solcore.Surface.Multi.ExactTokenRuleFallbackDecl
import Solcore.Surface.Multi.ExactTokenRuleFieldDecl
import Solcore.Surface.Multi.ExactTokenRuleForHelpers
import Solcore.Surface.Multi.ExactTokenRuleForStatement
import Solcore.Surface.Multi.ExactTokenRuleForallBinder
import Solcore.Surface.Multi.ExactTokenRuleForallClause
import Solcore.Surface.Multi.ExactTokenRuleGenericPrefix
import Solcore.Surface.Multi.ExactTokenRuleHidingClause
import Solcore.Surface.Multi.ExactTokenRuleIfStatement
import Solcore.Surface.Multi.ExactTokenRuleImportExport
import Solcore.Surface.Multi.ExactTokenRuleImportExportDecl
import Solcore.Surface.Multi.ExactTokenRuleInstanceDecl
import Solcore.Surface.Multi.ExactTokenRuleLambda
import Solcore.Surface.Multi.ExactTokenRuleLet
import Solcore.Surface.Multi.ExactTokenRuleParameterBody
import Solcore.Surface.Multi.ExactTokenRulePatternAtom
import Solcore.Surface.Multi.ExactTokenRulePostfixPart
import Solcore.Surface.Multi.ExactTokenRulePragma
import Solcore.Surface.Multi.ExactTokenRulePredicate
import Solcore.Surface.Multi.ExactTokenRulePredicateList
import Solcore.Surface.Multi.ExactTokenRuleSimpleStatements
import Solcore.Surface.Multi.ExactTokenRuleTopItem
import Solcore.Surface.Multi.ExactTokenRuleTypes

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

private theorem expressionPlans_eq_mapM (values : List Expression) :
    expressionTokenPlans? values = values.mapM expressionTokenPlan? := by
  induction values with
  | nil => simp [expressionTokenPlans?]
  | cons head tail induction =>
      simp [expressionTokenPlans?, expressionTokenPlan?, induction]

private theorem nonemptyExpressionPlans_eq_mapM
    (values : NonemptyList Expression) :
    nonemptyExpressionTokenPlans? values = (do
      let headPlan ← expressionTokenPlan? values.head
      let tailPlans ← values.tail.mapM expressionTokenPlan?
      pure (headPlan :: tailPlans)) := by
  rcases values with ⟨head, tail⟩
  simp [nonemptyExpressionTokenPlans?, expressionPlans_eq_mapM,
    expressionTokenPlan?]

private theorem matchArmPlans_eq_mapM (values : List MatchArm) :
    matchArmTokenPlans? values = values.mapM matchArmTokenPlan? := by
  induction values with
  | nil => simp [matchArmTokenPlans?]
  | cons head tail induction =>
      simp [matchArmTokenPlans?, induction]

private theorem nonemptyMatchArmPlans_eq_mapM
    (values : NonemptyList MatchArm) :
    nonemptyMatchArmTokenPlans? values = (do
      let headPlan ← matchArmTokenPlan? values.head
      let tailPlans ← values.tail.mapM matchArmTokenPlan?
      pure (headPlan :: tailPlans)) := by
  rcases values with ⟨head, tail⟩
  simp [nonemptyMatchArmTokenPlans?, matchArmPlans_eq_mapM]

private theorem nonemptyExpressionPlans_eq_ruleMapM
    (values : NonemptyList (RuleValue .expression)) :
    nonemptyExpressionTokenPlans? values = (do
      let headPlan ← ruleTokenPlan? .expression values.head
      let tailPlans ← values.tail.mapM (ruleTokenPlan? .expression)
      pure (headPlan :: tailPlans)) := by
  exact nonemptyExpressionPlans_eq_mapM values

private theorem nonemptyMatchArmPlans_eq_ruleMapM
    (values : NonemptyList (RuleValue .matchArm)) :
    nonemptyMatchArmTokenPlans? values = (do
      let headPlan ← ruleTokenPlan? .matchArm values.head
      let tailPlans ← values.tail.mapM (ruleTokenPlan? .matchArm)
      pure (headPlan :: tailPlans)) := by
  exact nonemptyMatchArmPlans_eq_mapM values

private theorem optionalSemicolonTokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (terminator : Option
      (MatchedTerminal file tokens (.symbol .semicolon))) :
    (EbnfValue.optional
      (.atom (.terminal (.symbol .semicolon)))
      (terminator.map (EbnfValue.terminalAtom
        (.symbol .semicolon)))).tokenPlan?
        sourceRuleTokenPlanLayout =
      some (match terminator with
        | none => TokenPlan.empty
        | some semicolon =>
            TokenPlan.exact (.symbol .semicolon) semicolon.span) := by
  cases terminator with
  | none => simp
  | some semicolon =>
      simp [MatchedTerminal.physicalTokenPlan_symbol]

private abbrev matchStatementChildren : List EbnfExpr := [
  .atom (.terminal (.hardKeyword .matchKw)),
  .list1 (.atom (.nonterminal .expression)),
  .atom (.terminal (.symbol .leftBrace)),
  .plus (.atom (.nonterminal .matchArm)),
  .atom (.terminal (.symbol .rightBrace)),
  .optional (.atom (.terminal (.symbol .semicolon)))]

private def matchStatementSourceValue
    {file : WorkspaceFile} {tokens : List Token}
    (matchKeyword : MatchedTerminal file tokens (.hardKeyword .matchKw))
    (scrutinees : NonemptyList Expression)
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (arms : NonemptyList MatchArm)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (terminator : Option
      (MatchedTerminal file tokens (.symbol .semicolon))) :
    EbnfValue file tokens (.sequence matchStatementChildren) :=
  EbnfValue.sequence matchStatementChildren <|
    EbnfValues.cons
      (.atom (.terminal (.hardKeyword .matchKw)))
      [
        .list1 (.atom (.nonterminal .expression)),
        .atom (.terminal (.symbol .leftBrace)),
        .plus (.atom (.nonterminal .matchArm)),
        .atom (.terminal (.symbol .rightBrace)),
        .optional (.atom (.terminal (.symbol .semicolon)))]
      (EbnfValue.terminalAtom (.hardKeyword .matchKw) matchKeyword) <|
    EbnfValues.cons
      (.list1 (.atom (.nonterminal .expression)))
      [
        .atom (.terminal (.symbol .leftBrace)),
        .plus (.atom (.nonterminal .matchArm)),
        .atom (.terminal (.symbol .rightBrace)),
        .optional (.atom (.terminal (.symbol .semicolon)))]
      (EbnfValue.list1 (.atom (.nonterminal .expression))
        (scrutinees.map (EbnfValue.ruleAtom .expression))) <|
    EbnfValues.cons
      (.atom (.terminal (.symbol .leftBrace)))
      [
        .plus (.atom (.nonterminal .matchArm)),
        .atom (.terminal (.symbol .rightBrace)),
        .optional (.atom (.terminal (.symbol .semicolon)))]
      (EbnfValue.terminalAtom (.symbol .leftBrace) openBrace) <|
    EbnfValues.cons
      (.plus (.atom (.nonterminal .matchArm)))
      [
        .atom (.terminal (.symbol .rightBrace)),
        .optional (.atom (.terminal (.symbol .semicolon)))]
      (EbnfValue.plus (.atom (.nonterminal .matchArm))
        (arms.map (EbnfValue.ruleAtom .matchArm))) <|
    EbnfValues.cons
      (.atom (.terminal (.symbol .rightBrace)))
      [.optional (.atom (.terminal (.symbol .semicolon)))]
      (EbnfValue.terminalAtom (.symbol .rightBrace) closeBrace) <|
    EbnfValues.cons
      (.optional (.atom (.terminal (.symbol .semicolon)))) []
      (EbnfValue.optional (.atom (.terminal (.symbol .semicolon)))
        (terminator.map
          (EbnfValue.terminalAtom (.symbol .semicolon))))
      EbnfValues.nil

private theorem matchStatementSourceValue_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (matchKeyword : MatchedTerminal file tokens (.hardKeyword .matchKw))
    (scrutinees : NonemptyList Expression)
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (arms : NonemptyList MatchArm)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (terminator : Option
      (MatchedTerminal file tokens (.symbol .semicolon))) :
    (matchStatementSourceValue matchKeyword scrutinees openBrace arms
      closeBrace terminator).tokenPlan? sourceRuleTokenPlanLayout = (do
        let scrutineePlans ← nonemptyExpressionTokenPlans? scrutinees
        let armPlans ← nonemptyMatchArmTokenPlans? arms
        let terminatorPlan := match terminator with
          | none => TokenPlan.empty
          | some semicolon =>
              TokenPlan.exact (.symbol .semicolon) semicolon.span
        pure (TokenPlan.concat [
          .exact (.hardKeyword .matchKw) matchKeyword.span,
          .commaSeparated scrutineePlans,
          .exact (.symbol .leftBrace) openBrace.span,
          .concat armPlans,
          .exact (.symbol .rightBrace) closeBrace.span,
          terminatorPlan])) := by
  unfold matchStatementSourceValue
  rw [EbnfValue.tokenPlan?_sequence]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_terminalAtom]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_list1]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_terminalAtom]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_plus]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_terminalAtom]
  rw [EbnfValues.tokenPlan?_cons]
  simp only [optionalSemicolonTokenPlan?]
  rw [EbnfValues.tokenPlan?_nil]
  simp only [NonemptyList.map]
  rw [ruleAtomValues_tokenPlans? .expression scrutinees.tail,
    ruleAtomValues_tokenPlans? .matchArm arms.tail]
  simp only [sourceRuleTokenPlanLayout,
    EbnfValue.tokenPlan?_ruleAtom,
    MatchedTerminal.physicalTokenPlan_hardKeyword,
    MatchedTerminal.physicalTokenPlan_symbol]
  rw [nonemptyExpressionPlans_eq_ruleMapM,
    nonemptyMatchArmPlans_eq_ruleMapM]
  cases scrutineeHeadEq : ruleTokenPlan? .expression scrutinees.head <;>
    cases scrutineeTailEq :
      scrutinees.tail.mapM (ruleTokenPlan? .expression) <;>
    cases armHeadEq : ruleTokenPlan? .matchArm arms.head <;>
    cases armTailEq : arms.tail.mapM (ruleTokenPlan? .matchArm) <;>
    simp_all [TokenPlan.concat_cons]

private theorem TokenSlot.ListMatches.matchStatementToPlain
    {matchSpan openSpan closeSpan : SourceSpan}
    {scrutinees arms terminator : TokenPlan} {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat [
        .exact (.hardKeyword .matchKw) matchSpan,
        scrutinees,
        .exact (.symbol .leftBrace) openSpan,
        arms,
        .exact (.symbol .rightBrace) closeSpan,
        terminator]).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.concat [
        .plain (.hardKeyword .matchKw),
        scrutinees,
        .plain (.symbol .leftBrace),
        arms,
        .plain (.symbol .rightBrace),
        terminator]).slots actual := by
  simp only [TokenPlan.concat, List.flatMap_cons, List.flatMap_nil,
    TokenPlan.exact, TokenPlan.plain, List.append_nil,
    List.singleton_append] at relation ⊢
  cases relation with
  | required matchEvidence afterMatch =>
      rcases afterMatch.split_append with
        ⟨scrutineeActual, afterScrutineeActual, rfl,
          scrutineeRelation, afterScrutineeRelation⟩
      cases afterScrutineeRelation with
      | required openEvidence afterOpen =>
          rcases afterOpen.split_append with
            ⟨armActual, afterArmActual, rfl,
              armRelation, afterArmRelation⟩
          cases afterArmRelation with
          | required closeEvidence terminatorRelation =>
              exact .required matchEvidence.toPlain <|
                scrutineeRelation.append <|
                  .required openEvidence.toPlain <|
                    armRelation.append <|
                      .required closeEvidence.toPlain terminatorRelation

private theorem TokenPlan.matchStatementInner_wellAnchored
    (scrutinees arms terminator : TokenPlan)
    (terminatorShape : terminator = TokenPlan.empty ∨
      ∃ span, terminator = TokenPlan.exact (.symbol .semicolon) span) :
    (TokenPlan.concat [
      .plain (.hardKeyword .matchKw),
      scrutinees,
      .plain (.symbol .leftBrace),
      arms,
      .plain (.symbol .rightBrace),
      terminator]).WellAnchored := by
  let beforeClose := TokenPlan.concat [
    .plain (.hardKeyword .matchKw),
    scrutinees,
    .plain (.symbol .leftBrace),
    arms]
  let afterOpen := TokenPlan.append
    (.plain (.symbol .rightBrace)) terminator
  have starts : TokenPlan.WellAnchored.StartsRequired beforeClose := by
    exact TokenPlan.WellAnchored.StartsRequired.concat_plain_first
      (.hardKeyword .matchKw)
      [scrutinees, .plain (.symbol .leftBrace), arms]
  have ends : TokenPlan.WellAnchored.EndsRequired afterOpen := by
    rcases terminatorShape with terminatorEq | ⟨span, terminatorEq⟩
    · subst terminator
      simpa [afterOpen, TokenPlan.append_assoc] using
        TokenPlan.WellAnchored.EndsRequired.append_plain_last
          TokenPlan.empty (.symbol .rightBrace)
    · subst terminator
      simpa [afterOpen, TokenPlan.append_assoc] using
        TokenPlan.WellAnchored.EndsRequired.concat_exact_last
          [TokenPlan.plain (.symbol .rightBrace)]
          (.symbol .semicolon) span
  have anchored := TokenPlan.WellAnchored.of_starts_ends_append
    (left := beforeClose) (right := afterOpen) starts ends
  simpa [beforeClose, afterOpen, TokenPlan.concat_cons,
    TokenPlan.append_assoc] using anchored

private theorem matchStatement_tokenPlanSound :
    GrammarRuleTokenPlanSound .matchStatement := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces
  cases reduces with
  | matchStatement origin finish matchKeyword scrutinees openBrace arms
      closeBrace terminator witness =>
      change TokenPlanEvidence
        (statementTokenPlan? false
          (sourceLoc witness (.match scrutinees arms
            (terminator.map MatchedTerminal.span)) : Statement))
        (PhysicalTokens tokens origin finish)
      subst input
      change TokenPlanEvidence
        ((matchStatementSourceValue matchKeyword scrutinees openBrace
          arms closeBrace terminator).tokenPlan?
          sourceRuleTokenPlanLayout)
        (PhysicalTokens tokens origin finish) at inputEvidence
      rw [matchStatementSourceValue_tokenPlan?] at inputEvidence
      cases scrutineeEq : nonemptyExpressionTokenPlans? scrutinees with
      | none =>
          simp [scrutineeEq, TokenPlanEvidence] at inputEvidence
      | some scrutineePlans =>
          cases armEq : nonemptyMatchArmTokenPlans? arms with
          | none =>
              simp [scrutineeEq, armEq, TokenPlanEvidence] at inputEvidence
          | some armPlans =>
              simp [scrutineeEq, armEq] at inputEvidence
              let scrutineePlan :=
                TokenPlan.commaSeparated scrutineePlans
              let armPlan := TokenPlan.concat armPlans
              let terminatorPlan := match terminator with
                | none => TokenPlan.empty
                | some semicolon =>
                    TokenPlan.exact (.symbol .semicolon) semicolon.span
              let inner := TokenPlan.concat [
                .plain (.hardKeyword .matchKw),
                scrutineePlan,
                .plain (.symbol .leftBrace),
                armPlan,
                .plain (.symbol .rightBrace),
                terminatorPlan]
              rcases inputEvidence with ⟨sourcePlan, sourceEq, relation⟩
              injection sourceEq with sourcePlanEq
              subst sourcePlan
              have innerRelation :
                  TokenSlot.ListMatches inner.slots
                    (PhysicalTokens tokens origin finish) := by
                have exactRelation : TokenSlot.ListMatches
                    (TokenPlan.concat [
                      .exact (.hardKeyword .matchKw) matchKeyword.span,
                      scrutineePlan,
                      .exact (.symbol .leftBrace) openBrace.span,
                      armPlan,
                      .exact (.symbol .rightBrace) closeBrace.span,
                      terminatorPlan]).slots
                    (PhysicalTokens tokens origin finish) := by
                  simpa [scrutineePlan, armPlan, terminatorPlan,
                    TokenPlan.concat_cons, TokenPlan.append_assoc]
                    using relation
                exact exactRelation.matchStatementToPlain
              have terminatorShape :
                  terminatorPlan = TokenPlan.empty ∨
                    ∃ span, terminatorPlan =
                      TokenPlan.exact (.symbol .semicolon) span := by
                cases terminator with
                | none => exact Or.inl rfl
                | some semicolon =>
                    exact Or.inr ⟨semicolon.span, rfl⟩
              have innerAnchored : inner.WellAnchored := by
                exact TokenPlan.matchStatementInner_wellAnchored
                  scrutineePlan armPlan terminatorPlan terminatorShape
              have enclosed := TokenPlanEvidence.enclose
                (TokenPlanEvidence.some innerRelation)
                (fun plan success => by
                  simp only [Option.some.injEq] at success
                  subst plan
                  exact innerAnchored)
                witness.consumed
              unfold statementTokenPlan?
              simp only [sourceLoc]
              rw [scrutineeEq, armEq]
              cases terminator <;>
                simpa [scrutineePlan, armPlan,
                  terminatorPlan, inner, TokenPlan.concat_cons,
                  TokenPlan.append_assoc] using enclosed

private theorem coherentRuleTokenPlanSound
    {rule : GrammarRuleId}
    (sound : GrammarRuleTokenPlanSound rule) :
    CoherentGrammarRuleTokenPlanSound sourceRuleTokenPlanLayout rule :=
  CoherentGrammarRuleTokenPlanSound.ofGrammarRule sound

/-- Exact-token preservation for all source rules follows from the universal
rules, the lexical-exact assembly bridge, and the five reachability-sensitive
callbacks whose unrestricted forms are not valid. -/
theorem rootActionTokenPlanSound_of_coherentExceptions
    (moduleRefSound : CoherentGrammarRuleTokenPlanSound
      sourceRuleTokenPlanLayout .moduleRef)
    (letBindingSound : CoherentGrammarRuleTokenPlanSound
      sourceRuleTokenPlanLayout .letBinding)
    (matchArmSound : CoherentGrammarRuleTokenPlanSound
      sourceRuleTokenPlanLayout .matchArm)
    (postfixSound : CoherentGrammarRuleTokenPlanSound
      sourceRuleTokenPlanLayout .postfix)
    (bodySound : CoherentGrammarRuleTokenPlanSound
      sourceRuleTokenPlanLayout .body) :
    RootActionTokenPlanSound sourceRuleTokenPlanLayout := by
  intro rule
  cases rule with
  | module => exact coherentRuleTokenPlanSound module_tokenPlanSound
  | topItem =>
      exact coherentRuleTokenPlanSound grammarRuleTokenPlanSound_topItem
  | moduleRef => exact moduleRefSound
  | importDecl => exact coherentRuleTokenPlanSound importDecl_tokenPlanSound
  | importEntry => exact coherentRuleTokenPlanSound importEntry_tokenPlanSound
  | hidingClause => exact coherentRuleTokenPlanSound hidingClause_tokenPlanSound
  | exportDecl => exact coherentRuleTokenPlanSound exportDecl_tokenPlanSound
  | localExportEntry =>
      exact coherentRuleTokenPlanSound localExportEntry_tokenPlanSound
  | remoteExportEntry =>
      exact coherentRuleTokenPlanSound remoteExportEntry_tokenPlanSound
  | exportItem => exact coherentRuleTokenPlanSound exportItem_tokenPlanSound
  | constructorSelection =>
      exact coherentRuleTokenPlanSound constructorSelection_tokenPlanSound
  | pragmaDecl => exact coherentRuleTokenPlanSound pragmaDecl_tokenPlanSound
  | genericPrefix => exact coherentRuleTokenPlanSound genericPrefix_tokenPlanSound
  | forallClause => exact coherentRuleTokenPlanSound forallClause_tokenPlanSound
  | forallBinder => exact coherentRuleTokenPlanSound forallBinder_tokenPlanSound
  | optionalComma => exact coherentRuleTokenPlanSound optionalComma_tokenPlanSound
  | predicateList => exact coherentRuleTokenPlanSound predicateList_tokenPlanSound
  | predicate => exact coherentRuleTokenPlanSound predicate_tokenPlanSound
  | functionSignature =>
      exact coherentRuleTokenPlanSound functionSignature_tokenPlanSound
  | functionDecl => exact coherentRuleTokenPlanSound functionDecl_tokenPlanSound
  | classMethod => exact coherentRuleTokenPlanSound classMethod_tokenPlanSound
  | dataDecl => exact coherentRuleTokenPlanSound dataDecl_tokenPlanSound
  | dataConstructor =>
      exact coherentRuleTokenPlanSound dataConstructor_tokenPlanSound
  | typeAliasDecl => exact coherentRuleTokenPlanSound typeAliasDecl_tokenPlanSound
  | classDecl => exact coherentRuleTokenPlanSound classDecl_tokenPlanSound
  | instanceDecl => exact coherentRuleTokenPlanSound instanceDecl_tokenPlanSound
  | instanceMethod =>
      exact coherentRuleTokenPlanSound instanceMethod_tokenPlanSound
  | contractDecl => exact coherentRuleTokenPlanSound contractDecl_tokenPlanSound
  | contractMember =>
      exact coherentRuleTokenPlanSound contractMember_tokenPlanSound
  | fieldDecl => exact coherentRuleTokenPlanSound fieldDecl_tokenPlanSound
  | fallbackDecl => exact coherentRuleTokenPlanSound fallbackDecl_tokenPlanSound
  | contractConstructorDecl =>
      exact coherentRuleTokenPlanSound contractConstructorDecl_tokenPlanSound
  | parameter => exact coherentRuleTokenPlanSound parameter_tokenPlanSound
  | body => exact bodySound
  | type => exact coherentRuleTokenPlanSound type_tokenPlanSound
  | typeAtom => exact coherentRuleTokenPlanSound typeAtom_tokenPlanSound
  | qualifiedName => exact coherentRuleTokenPlanSound qualifiedName_tokenPlanSound
  | statement => exact coherentRuleTokenPlanSound statement_tokenPlanSound
  | letStatement => exact coherentRuleTokenPlanSound letStatement_tokenPlanSound
  | letBinding => exact letBindingSound
  | returnStatement =>
      exact coherentRuleTokenPlanSound returnStatement_tokenPlanSound
  | blockStatement =>
      exact coherentRuleTokenPlanSound blockStatement_tokenPlanSound
  | breakStatement => exact coherentRuleTokenPlanSound breakStatement_tokenPlanSound
  | continueStatement =>
      exact coherentRuleTokenPlanSound continueStatement_tokenPlanSound
  | assemblyStatement => exact assemblyStatement_coherentTokenPlanSound
  | ifStatement => exact coherentRuleTokenPlanSound ifStatement_tokenPlanSound
  | forStatement => exact coherentRuleTokenPlanSound forStatement_tokenPlanSound
  | forInitItem => exact coherentRuleTokenPlanSound forInitItem_tokenPlanSound
  | forPostItem => exact coherentRuleTokenPlanSound forPostItem_tokenPlanSound
  | matchStatement => exact coherentRuleTokenPlanSound matchStatement_tokenPlanSound
  | matchArm => exact matchArmSound
  | armStatement => exact coherentRuleTokenPlanSound armStatement_tokenPlanSound
  | assignmentStatement =>
      exact coherentRuleTokenPlanSound assignmentStatement_tokenPlanSound
  | assignmentOperator =>
      exact coherentRuleTokenPlanSound assignmentOperator_tokenPlanSound
  | expressionStatement =>
      exact coherentRuleTokenPlanSound expressionStatement_tokenPlanSound
  | terminalExpression =>
      exact coherentRuleTokenPlanSound terminalExpression_tokenPlanSound
  | pattern => exact coherentRuleTokenPlanSound pattern_tokenPlanSound
  | expression => exact coherentRuleTokenPlanSound expression_tokenPlanSound
  | annotation => exact coherentRuleTokenPlanSound annotation_tokenPlanSound
  | conditional => exact coherentRuleTokenPlanSound conditional_tokenPlanSound
  | logicalOr =>
      exact coherentRuleTokenPlanSound grammarRuleTokenPlanSound_logicalOr
  | logicalAnd =>
      exact coherentRuleTokenPlanSound grammarRuleTokenPlanSound_logicalAnd
  | equality => exact coherentRuleTokenPlanSound equality_tokenPlanSound
  | relational => exact coherentRuleTokenPlanSound relational_tokenPlanSound
  | bitOr => exact coherentRuleTokenPlanSound grammarRuleTokenPlanSound_bitOr
  | bitXor => exact coherentRuleTokenPlanSound grammarRuleTokenPlanSound_bitXor
  | bitAnd => exact coherentRuleTokenPlanSound grammarRuleTokenPlanSound_bitAnd
  | additive => exact coherentRuleTokenPlanSound grammarRuleTokenPlanSound_additive
  | multiplicative =>
      exact coherentRuleTokenPlanSound grammarRuleTokenPlanSound_multiplicative
  | «prefix» => exact coherentRuleTokenPlanSound prefix_tokenPlanSound
  | «postfix» => exact postfixSound
  | postfixPart => exact coherentRuleTokenPlanSound postfixPart_tokenPlanSound
  | atom => exact coherentRuleTokenPlanSound atom_tokenPlanSound
  | lambda => exact coherentRuleTokenPlanSound lambda_tokenPlanSound
  | literal => exact coherentRuleTokenPlanSound literal_tokenPlanSound

end Solcore.Surface.Multi
