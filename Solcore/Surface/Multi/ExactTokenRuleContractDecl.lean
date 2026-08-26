import Solcore.Surface.Multi.ExactTokenRuleDeclarations
import Solcore.Surface.Multi.ExactTokenRuleLeaf

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

private abbrev ContractDeclParameters
    (file : WorkspaceFile) (tokens : List Token) :=
  Option
    (MatchedTerminal file tokens (.symbol .leftParen) ×
      (NonemptyList (RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier) ×
        (MatchedTerminal file tokens (.symbol .rightParen) × Unit)))

private abbrev contractDeclParameterChildren : List EbnfExpr := [
  .atom (.terminal (.symbol .leftParen)),
  .list1 (.atom (.terminal (.category .identifier))),
  .atom (.terminal (.symbol .rightParen))]

private abbrev contractDeclChildren : List EbnfExpr := [
  .atom (.terminal (.hardKeyword .contractKw)),
  .atom (.terminal (.category .identifier)),
  .optional (.sequence contractDeclParameterChildren),
  .atom (.terminal (.symbol .leftBrace)),
  .star (.atom (.nonterminal .contractMember)),
  .atom (.terminal (.symbol .rightBrace))]

private def contractDeclParameterInput
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : ContractDeclParameters file tokens) :
    EbnfValue file tokens
      (.optional (.sequence contractDeclParameterChildren)) :=
  EbnfValue.optional _ <| parameters.map fun value =>
    EbnfValue.sequence _ <|
      EbnfValues.cons _ _
        (EbnfValue.terminalAtom (.symbol .leftParen) value.1) <|
      EbnfValues.cons _ _
        (EbnfValue.list1 _ {
          head := EbnfValue.terminalAtom (.category .identifier)
            value.2.1.head.matched
          tail := value.2.1.tail.map fun parameter =>
            EbnfValue.terminalAtom (.category .identifier)
              parameter.matched
        }) <|
      EbnfValues.cons _ _
        (EbnfValue.terminalAtom (.symbol .rightParen) value.2.2.1)
        EbnfValues.nil

private def contractDeclInput
    {file : WorkspaceFile} {tokens : List Token}
    (contractKw : MatchedTerminal file tokens (.hardKeyword .contractKw))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (parameters : ContractDeclParameters file tokens)
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (members : List ContractMember)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace)) :
    EbnfValue file tokens (.sequence contractDeclChildren) :=
  EbnfValue.sequence _ <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.hardKeyword .contractKw) contractKw) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.category .identifier) name.matched) <|
    EbnfValues.cons _ _
      (contractDeclParameterInput parameters) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .leftBrace) openBrace) <|
    EbnfValues.cons _ _
      (EbnfValue.star _
        (members.map (EbnfValue.ruleAtom .contractMember))) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .rightBrace) closeBrace)
      EbnfValues.nil

private def contractDeclParameterSourcePlan
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : ContractDeclParameters file tokens) : TokenPlan :=
  match parameters with
  | none => .empty
  | some value => .concat [
      .exact (.symbol .leftParen) value.1.span,
      .commaSeparated
        (identifierPlan
            (RuleReduction.terminalLoc value.2.1.head.matched
              value.2.1.head.parsed) ::
          value.2.1.tail.map fun parameter => identifierPlan
            (RuleReduction.terminalLoc parameter.matched
              parameter.parsed)),
      .exact (.symbol .rightParen) value.2.2.1.span]

private def contractDeclParameterPlainPlan
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : ContractDeclParameters file tokens) : TokenPlan :=
  match parameters with
  | none => .empty
  | some value => .parens (.commaSeparated
      (identifierPlan
          (RuleReduction.terminalLoc value.2.1.head.matched
            value.2.1.head.parsed) ::
        value.2.1.tail.map fun parameter => identifierPlan
          (RuleReduction.terminalLoc parameter.matched
            parameter.parsed)))

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

private theorem contractDeclParameterInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : ContractDeclParameters file tokens)
    (parameterProjects : ∀ value, parameters = some value →
      IdentifierProjects value.2.1.head.matched
        value.2.1.head.spelling value.2.1.head.parsed ∧
      ∀ parameter, parameter ∈ value.2.1.tail →
        IdentifierProjects parameter.matched
          parameter.spelling parameter.parsed) :
    (contractDeclParameterInput parameters).tokenPlan?
        sourceRuleTokenPlanLayout =
      some (contractDeclParameterSourcePlan parameters) := by
  cases parameters with
  | none =>
      simp [contractDeclParameterInput, contractDeclParameterSourcePlan]
  | some value =>
      have projects := parameterProjects value rfl
      have headPlanEq := matchedIdentifier_physicalTokenPlan
        value.2.1.head projects.1
      have tailPlanEq : ∀ parameter ∈ value.2.1.tail,
          parameter.matched.physicalTokenPlan = identifierPlan
            (RuleReduction.terminalLoc parameter.matched
              parameter.parsed) := by
        intro parameter member
        exact matchedIdentifier_physicalTokenPlan parameter
          (projects.2 parameter member)
      have mappedPlansEq :
          List.mapM
              (fun parameter => some parameter.matched.physicalTokenPlan)
              value.2.1.tail =
            some (value.2.1.tail.map fun parameter => identifierPlan
              (RuleReduction.terminalLoc parameter.matched
                parameter.parsed)) := by
        change List.mapM
          (fun parameter =>
            (pure parameter.matched.physicalTokenPlan : Option TokenPlan))
          value.2.1.tail = _
        rw [List.mapM_pure]
        exact congrArg some (List.map_congr_left tailPlanEq)
      simp only [contractDeclParameterInput, Option.map_some,
        EbnfValue.tokenPlan?_optional_some,
        EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_list1,
        EbnfValues.tokenPlan?_nil]
      simp [Function.comp_def, EbnfValue.tokenPlan?_terminalAtom]
      rw [mappedPlansEq, headPlanEq]
      simp [contractDeclParameterSourcePlan, TokenPlan.concat_cons]

private theorem contractMemberRuleValues_tokenPlans?
    {file : WorkspaceFile} {tokens : List Token}
    (members : List ContractMember) :
    (members.map (EbnfValue.ruleAtom
      (file := file) (tokens := tokens) .contractMember)).mapM
        (fun value => value.tokenPlan? sourceRuleTokenPlanLayout) =
      members.mapM contractMemberPlan? := by
  rw [List.mapM_map]
  simp [Function.comp_def, sourceRuleTokenPlanLayout, ruleTokenPlan?]
  congr 1

private theorem contractDeclInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (contractKw : MatchedTerminal file tokens (.hardKeyword .contractKw))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (parameters : ContractDeclParameters file tokens)
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (members : List ContractMember)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (nameProjects : IdentifierProjects name.matched
      name.spelling name.parsed)
    (parameterProjects : ∀ value, parameters = some value →
      IdentifierProjects value.2.1.head.matched
        value.2.1.head.spelling value.2.1.head.parsed ∧
      ∀ parameter, parameter ∈ value.2.1.tail →
        IdentifierProjects parameter.matched
          parameter.spelling parameter.parsed) :
    (contractDeclInput contractKw name parameters openBrace members
      closeBrace).tokenPlan? sourceRuleTokenPlanLayout = (do
      let memberPlans ← members.mapM contractMemberPlan?
      pure (TokenPlan.concat [
        .exact (.hardKeyword .contractKw) contractKw.span,
        identifierPlan
          (RuleReduction.terminalLoc name.matched name.parsed),
        contractDeclParameterSourcePlan parameters,
        .exact (.symbol .leftBrace) openBrace.span,
        .concat memberPlans,
        .exact (.symbol .rightBrace) closeBrace.span])) := by
  unfold contractDeclInput
  rw [EbnfValue.tokenPlan?_sequence,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValues.tokenPlan?_cons,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_star,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValues.tokenPlan?_nil,
    MatchedTerminal.physicalTokenPlan_hardKeyword,
    matchedIdentifier_physicalTokenPlan name nameProjects,
    contractDeclParameterInput_tokenPlan? parameters parameterProjects,
    contractMemberRuleValues_tokenPlans? members,
    MatchedTerminal.physicalTokenPlan_symbol,
    MatchedTerminal.physicalTokenPlan_symbol]
  cases members.mapM contractMemberPlan? <;>
    simp [TokenPlan.concat_cons]

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

private theorem contractDeclParameterSourcePlan_weakens
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : ContractDeclParameters file tokens) :
    (contractDeclParameterSourcePlan parameters).WeakensTo
      (contractDeclParameterPlainPlan parameters) := by
  cases parameters with
  | none => exact TokenPlan.WeakensTo.refl _
  | some value =>
      intro actual relation
      exact TokenSlot.ListMatches.exactParensToPlain relation

private theorem contractDeclPlan?_sourceLoc
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (_contractKw : MatchedTerminal file tokens (.hardKeyword .contractKw))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (parameters : ContractDeclParameters file tokens)
    (_openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (members : List ContractMember)
    (_closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    contractDeclPlan? (sourceLoc witness {
      name := RuleReduction.terminalLoc name.matched name.parsed
      parameters := parameters.map fun value =>
        value.2.1.map fun parameter =>
          RuleReduction.terminalLoc parameter.matched parameter.parsed
      members := members
    } : ContractDecl) = (do
      let memberPlans ← members.mapM contractMemberPlan?
      pure (TokenPlan.enclose witness.span (TokenPlan.concat [
        TokenPlan.plain (.hardKeyword .contractKw),
        identifierPlan
          (RuleReduction.terminalLoc name.matched name.parsed),
        contractDeclParameterPlainPlan parameters,
        TokenPlan.plain (.symbol .leftBrace),
        TokenPlan.concat memberPlans,
        TokenPlan.plain (.symbol .rightBrace)]))) := by
  unfold contractDeclPlan?
  simp only [sourceLoc]
  unfoldOptionalIdentifierPlanCore
  rwDeclarationPlansMapM
  cases parameters <;>
    simp [contractDeclParameterPlainPlan, NonemptyList.map,
      nonemptyIdentifierPlans, identifierPlans,
      TokenPlan.concat_cons, Function.comp_def]

/-- Contract declarations preserve their name, parameters, and member plans
while weakening only punctuation fixed by the declaration grammar. -/
theorem contractDecl_tokenPlanSound :
    GrammarRuleTokenPlanSound .contractDecl := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | contractDecl origin finish contractKw name parameters openBrace members
      closeBrace nameProjects parameterProjects witness =>
      rw [← inputEq] at inputEvidence
      change TokenPlanEvidence
        (contractDeclPlan? (sourceLoc witness {
          name := RuleReduction.terminalLoc name.matched name.parsed
          parameters := parameters.map fun value =>
            value.2.1.map fun parameter =>
              RuleReduction.terminalLoc parameter.matched parameter.parsed
          members := members
        } : ContractDecl)) _
      let namePlan := identifierPlan
        (RuleReduction.terminalLoc name.matched name.parsed)
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout = (do
          let memberPlans ← members.mapM contractMemberPlan?
          pure (TokenPlan.concat [
            TokenPlan.exact (.hardKeyword .contractKw) contractKw.span,
            namePlan,
            contractDeclParameterSourcePlan parameters,
            TokenPlan.exact (.symbol .leftBrace) openBrace.span,
            TokenPlan.concat memberPlans,
            TokenPlan.exact (.symbol .rightBrace) closeBrace.span])) := by
        rw [inputEq]
        simp only [m2cV1, m2cV1Rhs, Grammar.hardKeyword,
          Grammar.identifier, Grammar.category, Grammar.terminal,
          Grammar.sequence, Grammar.symbol, Grammar.nonterminal,
          Grammar.optional, Grammar.list1, Grammar.star]
        rw [EbnfValue.tokenPlan?_transport]
        change (contractDeclInput contractKw name parameters openBrace
          members closeBrace).tokenPlan? sourceRuleTokenPlanLayout = _
        simpa [namePlan] using contractDeclInput_tokenPlan?
          contractKw name parameters openBrace members closeBrace
          nameProjects parameterProjects
      have physicalEvidence := inputEvidence.candidate_eq candidateEq
      cases memberEq : members.mapM contractMemberPlan? with
      | none =>
          simp [memberEq, TokenPlanEvidence] at physicalEvidence
      | some memberPlans =>
          simp only [memberEq] at physicalEvidence
          let sourceCore := TokenPlan.concat [
            TokenPlan.exact (.hardKeyword .contractKw) contractKw.span,
            namePlan,
            contractDeclParameterSourcePlan parameters,
            TokenPlan.exact (.symbol .leftBrace) openBrace.span,
            TokenPlan.concat memberPlans,
            TokenPlan.exact (.symbol .rightBrace) closeBrace.span]
          let targetCore := TokenPlan.concat [
            TokenPlan.plain (.hardKeyword .contractKw),
            namePlan,
            contractDeclParameterPlainPlan parameters,
            TokenPlan.plain (.symbol .leftBrace),
            TokenPlan.concat memberPlans,
            TokenPlan.plain (.symbol .rightBrace)]
          rcases physicalEvidence with ⟨plan, planEq, relation⟩
          change some sourceCore = some plan at planEq
          injection planEq with planEq
          subst plan
          have coreWeakens : sourceCore.WeakensTo targetCore := by
            intro actual sourceRelation
            have weakened := (TokenPlan.WeakensTo.append
              (TokenPlan.WeakensTo.exactToPlain
                (.hardKeyword .contractKw) contractKw.span)
              (TokenPlan.WeakensTo.append
                (TokenPlan.WeakensTo.refl namePlan)
                (TokenPlan.WeakensTo.append
                  (contractDeclParameterSourcePlan_weakens parameters)
                  (TokenPlan.WeakensTo.append
                    (TokenPlan.WeakensTo.exactToPlain
                      (.symbol .leftBrace) openBrace.span)
                    (TokenPlan.WeakensTo.append
                      (TokenPlan.WeakensTo.refl
                        (TokenPlan.concat memberPlans))
                      (TokenPlan.WeakensTo.exactToPlain
                        (.symbol .rightBrace) closeBrace.span))))))
                sourceRelation
            simpa [sourceCore, targetCore, TokenPlan.concat_cons,
              TokenPlan.append_assoc] using weakened
          have targetRelation : TokenSlot.ListMatches targetCore.slots
              (PhysicalTokens tokens origin finish) :=
            coreWeakens relation
          have targetAnchored : targetCore.WellAnchored := by
            exact TokenPlan.WellAnchored.concat_plain_bookended_four
              (.hardKeyword .contractKw) (.symbol .rightBrace)
              namePlan (contractDeclParameterPlainPlan parameters)
              (TokenPlan.plain (.symbol .leftBrace))
              (TokenPlan.concat memberPlans)
          have enclosed := TokenPlanEvidence.enclose
            (TokenPlanEvidence.some targetRelation)
            (fun candidate success => by
              simp only [Option.some.injEq] at success
              subst candidate
              exact targetAnchored)
            witness.consumed
          apply enclosed.candidate_eq
          rw [contractDeclPlan?_sourceLoc contractKw name parameters
            openBrace members closeBrace witness]
          rw [memberEq]
          simp [targetCore, namePlan]

end Solcore.Surface.Multi
