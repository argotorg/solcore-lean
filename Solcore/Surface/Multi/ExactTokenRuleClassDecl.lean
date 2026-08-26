import Solcore.Surface.Multi.ExactTokenRuleDeclarations
import Solcore.Surface.Multi.ExactTokenRuleLeaf

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace
open Lean Lean.Elab Lean.Elab.Tactic

elab "unfoldClassDeclTypeExprPlansCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.typeExprPlans?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] => unfoldTarget declaration
  | _ => throwError "the class declaration visitor has an unknown type-list helper"

elab "unfoldClassDeclNonemptyTypeExprPlansCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.nonemptyTypeExprPlans?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] => unfoldTarget declaration
  | _ => throwError "the class declaration visitor has an unknown nonempty type-list helper"

private abbrev ClassDeclParameters
    (file : WorkspaceFile) (tokens : List Token) :=
  Option
    (MatchedTerminal file tokens (.symbol .leftParen) ×
      (NonemptyList TypeExpr ×
        (MatchedTerminal file tokens (.symbol .rightParen) × Unit)))

private abbrev classDeclParameterChildren : List EbnfExpr := [
  .atom (.terminal (.symbol .leftParen)),
  .list1 (.atom (.nonterminal .type)),
  .atom (.terminal (.symbol .rightParen))]

private abbrev classDeclChildren : List EbnfExpr := [
  .optional (.atom (.nonterminal .genericPrefix)),
  .atom (.terminal (.hardKeyword .classKw)),
  .atom (.nonterminal .typeAtom),
  .atom (.terminal (.symbol .colon)),
  .atom (.terminal (.category .identifier)),
  .optional (.sequence classDeclParameterChildren),
  .atom (.terminal (.symbol .leftBrace)),
  .star (.atom (.nonterminal .classMethod)),
  .atom (.terminal (.symbol .rightBrace))]

private def classDeclParameterInput
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : ClassDeclParameters file tokens) :
    EbnfValue file tokens
      (.optional (.sequence classDeclParameterChildren)) :=
  EbnfValue.optional _ <| parameters.map fun value =>
    EbnfValue.sequence _ <|
      EbnfValues.cons _ _
        (EbnfValue.terminalAtom (.symbol .leftParen) value.1) <|
      EbnfValues.cons _ _
        (EbnfValue.list1 _
          (value.2.1.map (EbnfValue.ruleAtom .type))) <|
      EbnfValues.cons _ _
        (EbnfValue.terminalAtom (.symbol .rightParen) value.2.2.1)
        EbnfValues.nil

private def classDeclInput
    {file : WorkspaceFile} {tokens : List Token}
    (genericPrefix : Option GenericPrefix)
    (classKw : MatchedTerminal file tokens (.hardKeyword .classKw))
    (main : TypeExpr)
    (colon : MatchedTerminal file tokens (.symbol .colon))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (parameters : ClassDeclParameters file tokens)
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (methods : List ClassMethodDecl)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace)) :
    EbnfValue file tokens (.sequence classDeclChildren) :=
  EbnfValue.sequence _ <|
    EbnfValues.cons _ _
      (EbnfValue.optional _
        (genericPrefix.map (EbnfValue.ruleAtom .genericPrefix))) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.hardKeyword .classKw) classKw) <|
    EbnfValues.cons _ _
      (EbnfValue.ruleAtom .typeAtom main) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .colon) colon) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.category .identifier) name.matched) <|
    EbnfValues.cons _ _
      (classDeclParameterInput parameters) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .leftBrace) openBrace) <|
    EbnfValues.cons _ _
      (EbnfValue.star _
        (methods.map (EbnfValue.ruleAtom .classMethod))) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .rightBrace) closeBrace)
      EbnfValues.nil

private def classDeclOptionalGenericPlan? :
    Option GenericPrefix → Option TokenPlan
  | none => some .empty
  | some value => genericPrefixPlan? value

private def classDeclParameterSourcePlan?
    {file : WorkspaceFile} {tokens : List Token} :
    ClassDeclParameters file tokens → Option TokenPlan
  | none => some .empty
  | some value => do
      let headPlan ← typeExprPlan? value.2.1.head
      let tailPlans ← value.2.1.tail.mapM typeExprPlan?
      pure (.concat [
        .exact (.symbol .leftParen) value.1.span,
        .append headPlan (.commaTail tailPlans),
        .exact (.symbol .rightParen) value.2.2.1.span])

private def classDeclParameterPlainPlan?
    {file : WorkspaceFile} {tokens : List Token} :
    ClassDeclParameters file tokens → Option TokenPlan
  | none => some .empty
  | some value => do
      let headPlan ← typeExprPlan? value.2.1.head
      let tailPlans ← value.2.1.tail.mapM typeExprPlan?
      pure (.parens (.append headPlan (.commaTail tailPlans)))

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

private theorem typeRulePlans_eq
    (values : List TypeExpr) :
    values.mapM (ruleTokenPlan? .type) =
      values.mapM typeExprPlan? := by
  rfl

private theorem classMethodRulePlans_eq
    (values : List ClassMethodDecl) :
    values.mapM (ruleTokenPlan? .classMethod) =
      values.mapM classMethodDeclPlan? := by
  rfl

private theorem typeExprPlans_eq_mapM (values : List TypeExpr) :
    typeExprPlans? values = values.mapM typeExprPlan? := by
  induction values with
  | nil =>
      unfoldClassDeclTypeExprPlansCore
      rfl
  | cons head tail induction =>
      unfoldClassDeclTypeExprPlansCore
      simp [List.mapM_cons, typeExprPlan?, induction]

private theorem nonemptyTypeExprPlans_eq_mapM
    (values : NonemptyList TypeExpr) :
    nonemptyTypeExprPlans? values = (do
      let headPlan ← typeExprPlan? values.head
      let tailPlans ← values.tail.mapM typeExprPlan?
      pure (headPlan :: tailPlans)) := by
  unfoldClassDeclNonemptyTypeExprPlansCore
  rw [typeExprPlans_eq_mapM]
  rfl

private theorem nonemptyTypePlainPlan_eq
    (values : NonemptyList TypeExpr) :
    (do
      let plans ← nonemptyTypeExprPlans? values
      pure (TokenPlan.parens (TokenPlan.commaSeparated plans))) = (do
      let headPlan ← typeExprPlan? values.head
      let tailPlans ← values.tail.mapM typeExprPlan?
      pure (TokenPlan.parens
        (headPlan.append (TokenPlan.commaTail tailPlans)))) := by
  rw [nonemptyTypeExprPlans_eq_mapM]
  cases typeExprPlan? values.head <;>
    cases values.tail.mapM typeExprPlan? <;>
    simp

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

private theorem classDeclParameterInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : ClassDeclParameters file tokens) :
    (classDeclParameterInput parameters).tokenPlan?
        sourceRuleTokenPlanLayout =
      classDeclParameterSourcePlan? parameters := by
  cases parameters with
  | none => simp [classDeclParameterInput, classDeclParameterSourcePlan?]
  | some value =>
      simp only [classDeclParameterInput, Option.map_some,
        EbnfValue.tokenPlan?_optional_some,
        EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_list1,
        EbnfValues.tokenPlan?_nil,
        MatchedTerminal.physicalTokenPlan_symbol]
      simp only [NonemptyList.map]
      rw [EbnfValue.tokenPlan?_ruleAtom,
        ruleAtomValues_tokenPlans? .type value.2.1.tail,
        typeRulePlans_eq]
      simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?]
      cases headEq : typeExprPlan? value.2.1.head <;>
        cases tailEq : value.2.1.tail.mapM typeExprPlan? <;>
        simp [classDeclParameterSourcePlan?, headEq, tailEq,
          TokenPlan.concat_cons]

private theorem classDeclOptionalGenericInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (genericPrefix : Option GenericPrefix) :
    (EbnfValue.optional (.atom (.nonterminal .genericPrefix))
      (genericPrefix.map
        (EbnfValue.ruleAtom (file := file) (tokens := tokens)
          .genericPrefix))).tokenPlan? sourceRuleTokenPlanLayout =
      classDeclOptionalGenericPlan? genericPrefix := by
  change Option (RuleValue .genericPrefix) at genericPrefix
  cases genericPrefix with
  | none =>
      rw [Option.map_none, EbnfValue.tokenPlan?_optional_none]
      rfl
  | some generic =>
      rw [Option.map_some, EbnfValue.tokenPlan?_optional_some,
        EbnfValue.tokenPlan?_ruleAtom]
      rfl

private theorem classDeclInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (genericPrefix : Option GenericPrefix)
    (classKw : MatchedTerminal file tokens (.hardKeyword .classKw))
    (main : TypeExpr)
    (colon : MatchedTerminal file tokens (.symbol .colon))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (parameters : ClassDeclParameters file tokens)
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (methods : List ClassMethodDecl)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (nameProjects : IdentifierProjects name.matched
      name.spelling name.parsed) :
    (classDeclInput genericPrefix classKw main colon name parameters
      openBrace methods closeBrace).tokenPlan? sourceRuleTokenPlanLayout = (do
      let genericPlan ← classDeclOptionalGenericPlan? genericPrefix
      let mainPlan ← typeAtomPlan? main
      let parameterPlan ← classDeclParameterSourcePlan? parameters
      let methodPlans ← methods.mapM classMethodDeclPlan?
      pure (.concat [
        genericPlan,
        .exact (.hardKeyword .classKw) classKw.span,
        mainPlan,
        .exact (.symbol .colon) colon.span,
        identifierPlan (RuleReduction.terminalLoc name.matched name.parsed),
        parameterPlan,
        .exact (.symbol .leftBrace) openBrace.span,
        .concat methodPlans,
        .exact (.symbol .rightBrace) closeBrace.span])) := by
  unfold classDeclInput
  rw [EbnfValue.tokenPlan?_sequence]
  rw [EbnfValues.tokenPlan?_cons,
    classDeclOptionalGenericInput_tokenPlan?]
  simp only [EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValue.tokenPlan?_ruleAtom,
    EbnfValue.tokenPlan?_star,
    EbnfValues.tokenPlan?_nil]
  rw [classDeclParameterInput_tokenPlan?,
    ruleAtomValues_tokenPlans? .classMethod methods,
    classMethodRulePlans_eq,
    matchedIdentifier_physicalTokenPlan name nameProjects]
  simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?,
    MatchedTerminal.physicalTokenPlan_hardKeyword,
    MatchedTerminal.physicalTokenPlan_symbol]
  cases genericEq : classDeclOptionalGenericPlan? genericPrefix <;>
    cases mainEq : typeAtomPlan? main <;>
      cases parameterEq : classDeclParameterSourcePlan? parameters <;>
      cases methodsEq : methods.mapM classMethodDeclPlan? <;>
    simp [TokenPlan.concat_cons]

private theorem classDeclPlan?_sourceLoc
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (genericPrefix : Option GenericPrefix)
    (_classKw : MatchedTerminal file tokens (.hardKeyword .classKw))
    (main : TypeExpr)
    (_colon : MatchedTerminal file tokens (.symbol .colon))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (parameters : ClassDeclParameters file tokens)
    (_openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (methods : List ClassMethodDecl)
    (_closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    classDeclPlan? (sourceLoc witness {
      genericPrefix := genericPrefix
      main := main
      className := RuleReduction.terminalLoc name.matched name.parsed
      parameters := RuleReduction.arguments parameters
      methods := methods
    } : ClassDecl) = (do
      let genericPlan ← classDeclOptionalGenericPlan? genericPrefix
      let mainPlan ← typeAtomPlan? main
      let parameterPlan ← classDeclParameterPlainPlan? parameters
      let methodPlans ← methods.mapM classMethodDeclPlan?
      pure (.enclose witness.span (.concat [
        genericPlan,
        .plain (.hardKeyword .classKw),
        mainPlan,
        .plain (.symbol .colon),
        identifierPlan (RuleReduction.terminalLoc name.matched name.parsed),
        parameterPlan,
        .plain (.symbol .leftBrace),
        .concat methodPlans,
        .plain (.symbol .rightBrace)]))) := by
  unfold classDeclPlan?
  simp only [sourceLoc, RuleReduction.arguments]
  unfoldSignatureOptionalPlanCore
  unfoldOptionalNonemptyTypePlanCore
  unfoldNonemptyTypePlanCore
  rwDeclarationPlansMapM
  cases genericPrefix <;> cases parameters with
  | none =>
      simp [classDeclOptionalGenericPlan?, classDeclParameterPlainPlan?]
  | some value =>
      rcases value with ⟨openParen, values, closeParen, unitValue⟩
      cases unitValue
      simp only [classDeclOptionalGenericPlan?,
        classDeclParameterPlainPlan?]
      rw [nonemptyTypePlainPlan_eq]

private def TokenPlan.WeakensTo
    (source target : TokenPlan) : Prop :=
  ∀ {actual : List Token},
    TokenSlot.ListMatches source.slots actual →
      TokenSlot.ListMatches target.slots actual

private theorem TokenPlan.WeakensTo.refl (plan : TokenPlan) :
    plan.WeakensTo plan := by
  intro actual relation
  exact relation

private theorem TokenPlan.WeakensTo.append
    {sourceLeft sourceRight targetLeft targetRight : TokenPlan}
    (left : sourceLeft.WeakensTo targetLeft)
    (right : sourceRight.WeakensTo targetRight) :
    (sourceLeft.append sourceRight).WeakensTo
      (targetLeft.append targetRight) := by
  intro actual relation
  rcases relation.split_append with
    ⟨leftActual, rightActual, rfl, leftRelation, rightRelation⟩
  exact (left leftRelation).append (right rightRelation)

private theorem TokenPlan.WeakensTo.exactToPlain
    (kind : TokenKind) (span : SourceSpan) :
    (TokenPlan.exact kind span).WeakensTo
      (TokenPlan.plain kind) := by
  intro actual relation
  exact relation.requiredHeadToPlain

private theorem TokenSlot.ListMatches.exactParensToPlain
    {openSpan closeSpan : SourceSpan}
    {middle : TokenPlan} {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat [
        TokenPlan.exact (.symbol .leftParen) openSpan,
        middle,
        TokenPlan.exact (.symbol .rightParen) closeSpan]).slots actual) :
    TokenSlot.ListMatches (TokenPlan.parens middle).slots actual := by
  change TokenSlot.ListMatches
    (.required (ExpectedToken.exact (.symbol .leftParen) openSpan) ::
      middle.slots ++
        [.required (ExpectedToken.exact (.symbol .rightParen) closeSpan)])
    actual at relation
  change TokenSlot.ListMatches
    (.required (ExpectedToken.plain (.symbol .leftParen)) ::
      middle.slots ++
        [.required (ExpectedToken.plain (.symbol .rightParen))]) actual
  cases relation with
  | required firstMatch rest =>
      rcases rest.split_append with
        ⟨middleActual, lastActual, rfl,
          middleRelation, lastRelation⟩
      exact .required firstMatch.toPlain <|
        middleRelation.append lastRelation.requiredHeadToPlain

private theorem classDeclParameterSourcePlan?_weakens
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : ClassDeclParameters file tokens)
    {sourcePlan : TokenPlan}
    (sourceEq : classDeclParameterSourcePlan? parameters = some sourcePlan) :
    ∃ targetPlan,
      classDeclParameterPlainPlan? parameters = some targetPlan ∧
      sourcePlan.WeakensTo targetPlan := by
  cases parameters with
  | none =>
      simp [classDeclParameterSourcePlan?, classDeclParameterPlainPlan?]
        at sourceEq ⊢
      subst sourcePlan
      exact TokenPlan.WeakensTo.refl _
  | some value =>
      cases headEq : typeExprPlan? value.2.1.head with
      | none => simp [classDeclParameterSourcePlan?, headEq] at sourceEq
      | some headPlan =>
          cases tailEq : value.2.1.tail.mapM typeExprPlan? with
          | none =>
              simp [classDeclParameterSourcePlan?, headEq, tailEq]
                at sourceEq
          | some tailPlans =>
              simp [classDeclParameterSourcePlan?, headEq, tailEq]
                at sourceEq
              subst sourcePlan
              refine ⟨TokenPlan.parens
                (headPlan.append (TokenPlan.commaTail tailPlans)), ?_, ?_⟩
              · simp [classDeclParameterPlainPlan?, headEq, tailEq]
              · intro actual relation
                exact TokenSlot.ListMatches.exactParensToPlain relation

/-- Class declarations preserve their recursive child plans and weaken only
the punctuation fixed by the declaration grammar. -/
theorem classDecl_tokenPlanSound :
    GrammarRuleTokenPlanSound .classDecl := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | classDecl origin finish genericPrefix classKw main colon name parameters
      openBrace methods closeBrace nameProjects witness =>
      rw [← inputEq] at inputEvidence
      change TokenPlanEvidence
        (classDeclPlan? (sourceLoc witness {
          genericPrefix := genericPrefix
          main := main
          className := RuleReduction.terminalLoc name.matched name.parsed
          parameters := RuleReduction.arguments parameters
          methods := methods
        } : ClassDecl)) _
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout = (do
          let genericPlan ← classDeclOptionalGenericPlan? genericPrefix
          let mainPlan ← typeAtomPlan? main
          let parameterPlan ← classDeclParameterSourcePlan? parameters
          let methodPlans ← methods.mapM classMethodDeclPlan?
          pure (.concat [
            genericPlan,
            .exact (.hardKeyword .classKw) classKw.span,
            mainPlan,
            .exact (.symbol .colon) colon.span,
            identifierPlan
              (RuleReduction.terminalLoc name.matched name.parsed),
            parameterPlan,
            .exact (.symbol .leftBrace) openBrace.span,
            .concat methodPlans,
            .exact (.symbol .rightBrace) closeBrace.span])) := by
        rw [inputEq]
        simp only [m2cV1, m2cV1Rhs, Grammar.hardKeyword,
          Grammar.identifier, Grammar.category, Grammar.terminal,
          Grammar.sequence, Grammar.symbol, Grammar.nonterminal,
          Grammar.optional, Grammar.list1, Grammar.star]
        rw [EbnfValue.tokenPlan?_transport]
        change (classDeclInput genericPrefix classKw main colon name
          parameters openBrace methods closeBrace).tokenPlan?
            sourceRuleTokenPlanLayout = _
        exact classDeclInput_tokenPlan? genericPrefix classKw main colon name
          parameters openBrace methods closeBrace nameProjects
      have physicalEvidence := inputEvidence.candidate_eq candidateEq
      cases genericEq : classDeclOptionalGenericPlan? genericPrefix with
      | none => simp [genericEq, TokenPlanEvidence] at physicalEvidence
      | some genericPlan =>
          cases mainEq : typeAtomPlan? main with
          | none =>
              simp [genericEq, mainEq, TokenPlanEvidence] at physicalEvidence
          | some mainPlan =>
              cases parameterSourceEq :
                  classDeclParameterSourcePlan? parameters with
              | none =>
                  simp [genericEq, mainEq, parameterSourceEq,
                    TokenPlanEvidence] at physicalEvidence
              | some parameterSourcePlan =>
                  cases methodsEq : methods.mapM classMethodDeclPlan? with
                  | none =>
                      simp [genericEq, mainEq, parameterSourceEq, methodsEq,
                        TokenPlanEvidence] at physicalEvidence
                  | some methodPlans =>
                      simp only [genericEq, mainEq, parameterSourceEq,
                        methodsEq] at physicalEvidence
                      rcases classDeclParameterSourcePlan?_weakens parameters
                          parameterSourceEq with
                        ⟨parameterTargetPlan, parameterTargetEq,
                          parameterWeakens⟩
                      let namePlan := identifierPlan
                        (RuleReduction.terminalLoc name.matched name.parsed)
                      let sourceCore := TokenPlan.concat [
                        genericPlan,
                        .exact (.hardKeyword .classKw) classKw.span,
                        mainPlan,
                        .exact (.symbol .colon) colon.span,
                        namePlan,
                        parameterSourcePlan,
                        .exact (.symbol .leftBrace) openBrace.span,
                        .concat methodPlans,
                        .exact (.symbol .rightBrace) closeBrace.span]
                      let targetCore := TokenPlan.concat [
                        genericPlan,
                        .plain (.hardKeyword .classKw),
                        mainPlan,
                        .plain (.symbol .colon),
                        namePlan,
                        parameterTargetPlan,
                        .plain (.symbol .leftBrace),
                        .concat methodPlans,
                        .plain (.symbol .rightBrace)]
                      rcases physicalEvidence with
                        ⟨sourcePlan, sourcePlanEq, relation⟩
                      change some sourceCore = some sourcePlan at sourcePlanEq
                      injection sourcePlanEq with sourcePlanEq
                      subst sourcePlan
                      have coreWeakens : sourceCore.WeakensTo targetCore := by
                        intro actual sourceRelation
                        have weakened := (TokenPlan.WeakensTo.append
                          (TokenPlan.WeakensTo.refl genericPlan)
                          (TokenPlan.WeakensTo.append
                            (TokenPlan.WeakensTo.exactToPlain
                              (.hardKeyword .classKw) classKw.span)
                            (TokenPlan.WeakensTo.append
                              (TokenPlan.WeakensTo.refl mainPlan)
                              (TokenPlan.WeakensTo.append
                                (TokenPlan.WeakensTo.exactToPlain
                                  (.symbol .colon) colon.span)
                                (TokenPlan.WeakensTo.append
                                  (TokenPlan.WeakensTo.refl namePlan)
                                  (TokenPlan.WeakensTo.append
                                    parameterWeakens
                                    (TokenPlan.WeakensTo.append
                                      (TokenPlan.WeakensTo.exactToPlain
                                        (.symbol .leftBrace) openBrace.span)
                                      (TokenPlan.WeakensTo.append
                                        (TokenPlan.WeakensTo.refl
                                          (.concat methodPlans))
                                        (TokenPlan.WeakensTo.exactToPlain
                                          (.symbol .rightBrace)
                                          closeBrace.span)))))))))
                            sourceRelation
                        simpa [sourceCore, targetCore,
                          TokenPlan.concat_cons, TokenPlan.append_assoc]
                          using weakened
                      have targetRelation : TokenSlot.ListMatches
                          targetCore.slots
                          (PhysicalTokens tokens origin finish) :=
                        coreWeakens relation
                      have genericAnchored : genericPlan.WellAnchored := by
                        cases genericPrefix with
                        | none =>
                            simp [classDeclOptionalGenericPlan?] at genericEq
                            subst genericPlan
                            exact TokenPlan.WellAnchored.empty
                        | some generic =>
                            exact genericPrefixPlan?_wellAnchored generic
                              genericPlan genericEq
                      have targetAnchored : targetCore.WellAnchored := by
                        have suffixAnchored :=
                          TokenPlan.WellAnchored.concat_plain_bookended_six
                            (.hardKeyword .classKw) (.symbol .rightBrace)
                            mainPlan (.plain (.symbol .colon)) namePlan
                            parameterTargetPlan
                            (.plain (.symbol .leftBrace))
                            (.concat methodPlans)
                        simpa [targetCore, TokenPlan.concat,
                          TokenPlan.append] using
                            TokenPlan.WellAnchored.append genericAnchored
                              suffixAnchored
                      have enclosed := TokenPlanEvidence.enclose
                        (TokenPlanEvidence.some targetRelation)
                        (fun plan success => by
                          simp only [Option.some.injEq] at success
                          subst plan
                          exact targetAnchored)
                        witness.consumed
                      apply enclosed.candidate_eq
                      rw [classDeclPlan?_sourceLoc genericPrefix classKw main
                        colon name parameters openBrace methods closeBrace
                        witness]
                      rw [genericEq, mainEq, parameterTargetEq, methodsEq]
                      simp [targetCore, namePlan]

end Solcore.Surface.Multi
