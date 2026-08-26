import Solcore.Surface.Multi.ExactTokenRuleDeclarations
import Solcore.Surface.Multi.ExactTokenRuleLeaf

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace
open Lean Lean.Elab Lean.Elab.Tactic

elab "unfoldInstanceDeclTypeExprPlansCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.typeExprPlans?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] => unfoldTarget declaration
  | _ => throwError "the class declaration visitor has an unknown type-list helper"

elab "unfoldInstanceDeclNonemptyTypeExprPlansCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.nonemptyTypeExprPlans?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] => unfoldTarget declaration
  | _ => throwError "the class declaration visitor has an unknown nonempty type-list helper"

private abbrev InstanceDeclParameters
    (file : WorkspaceFile) (tokens : List Token) :=
  Option
    (MatchedTerminal file tokens (.symbol .leftParen) ×
      (NonemptyList TypeExpr ×
        (MatchedTerminal file tokens (.symbol .rightParen) × Unit)))

private abbrev instanceDeclParameterChildren : List EbnfExpr := [
  .atom (.terminal (.symbol .leftParen)),
  .list1 (.atom (.nonterminal .type)),
  .atom (.terminal (.symbol .rightParen))]

private abbrev instanceDeclChildren : List EbnfExpr := [
  .optional (.atom (.nonterminal .genericPrefix)),
  .optional (.atom (.terminal (.hardKeyword .defaultKw))),
  .atom (.terminal (.hardKeyword .instanceKw)),
  .atom (.nonterminal .typeAtom),
  .atom (.terminal (.symbol .colon)),
  .atom (.nonterminal .qualifiedName),
  .optional (.sequence instanceDeclParameterChildren),
  .atom (.terminal (.symbol .leftBrace)),
  .star (.atom (.nonterminal .instanceMethod)),
  .atom (.terminal (.symbol .rightBrace))]

private def instanceDeclParameterInput
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : InstanceDeclParameters file tokens) :
    EbnfValue file tokens
      (.optional (.sequence instanceDeclParameterChildren)) :=
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

private def instanceDeclInput
    {file : WorkspaceFile} {tokens : List Token}
    (genericPrefix : Option GenericPrefix)
    (defaultToken : Option (MatchedTerminal file tokens
      (.hardKeyword .defaultKw)))
    (instanceKw : MatchedTerminal file tokens (.hardKeyword .instanceKw))
    (main : TypeExpr)
    (colon : MatchedTerminal file tokens (.symbol .colon))
    (className : QualifiedName)
    (parameters : InstanceDeclParameters file tokens)
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (methods : List FunctionDecl)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace)) :
    EbnfValue file tokens (.sequence instanceDeclChildren) :=
  EbnfValue.sequence _ <|
    EbnfValues.cons _ _
      (EbnfValue.optional _
        (genericPrefix.map (EbnfValue.ruleAtom .genericPrefix))) <|
    EbnfValues.cons _ _
      (EbnfValue.optional _ (defaultToken.map fun terminal =>
        EbnfValue.terminalAtom (.hardKeyword .defaultKw) terminal)) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.hardKeyword .instanceKw) instanceKw) <|
    EbnfValues.cons _ _
      (EbnfValue.ruleAtom .typeAtom main) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .colon) colon) <|
    EbnfValues.cons _ _
      (EbnfValue.ruleAtom .qualifiedName className) <|
    EbnfValues.cons _ _
      (instanceDeclParameterInput parameters) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .leftBrace) openBrace) <|
    EbnfValues.cons _ _
      (EbnfValue.star _
        (methods.map (EbnfValue.ruleAtom .instanceMethod))) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .rightBrace) closeBrace)
      EbnfValues.nil

private def instanceDeclOptionalGenericPlan? :
    Option GenericPrefix → Option TokenPlan
  | none => some .empty
  | some value => genericPrefixPlan? value

private def instanceDeclOptionalDefaultPlan
    {file : WorkspaceFile} {tokens : List Token} :
    Option (MatchedTerminal file tokens (.hardKeyword .defaultKw)) → TokenPlan
  | none => .empty
  | some terminal => .exact (.hardKeyword .defaultKw) terminal.span

private def instanceDeclParameterSourcePlan?
    {file : WorkspaceFile} {tokens : List Token} :
    InstanceDeclParameters file tokens → Option TokenPlan
  | none => some .empty
  | some value => do
      let headPlan ← typeExprPlan? value.2.1.head
      let tailPlans ← value.2.1.tail.mapM typeExprPlan?
      pure (.concat [
        .exact (.symbol .leftParen) value.1.span,
        .append headPlan (.commaTail tailPlans),
        .exact (.symbol .rightParen) value.2.2.1.span])

private def instanceDeclParameterPlainPlan?
    {file : WorkspaceFile} {tokens : List Token} :
    InstanceDeclParameters file tokens → Option TokenPlan
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

private theorem instanceMethodRulePlans_eq
    (values : List FunctionDecl) :
    values.mapM (ruleTokenPlan? .instanceMethod) =
      values.mapM functionDeclPlan? := by
  rfl

private theorem typeExprPlans_eq_mapM (values : List TypeExpr) :
    typeExprPlans? values = values.mapM typeExprPlan? := by
  induction values with
  | nil =>
      unfoldInstanceDeclTypeExprPlansCore
      rfl
  | cons head tail induction =>
      unfoldInstanceDeclTypeExprPlansCore
      simp [List.mapM_cons, typeExprPlan?, induction]

private theorem nonemptyTypeExprPlans_eq_mapM
    (values : NonemptyList TypeExpr) :
    nonemptyTypeExprPlans? values = (do
      let headPlan ← typeExprPlan? values.head
      let tailPlans ← values.tail.mapM typeExprPlan?
      pure (headPlan :: tailPlans)) := by
  unfoldInstanceDeclNonemptyTypeExprPlansCore
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

private theorem instanceDeclParameterInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : InstanceDeclParameters file tokens) :
    (instanceDeclParameterInput parameters).tokenPlan?
        sourceRuleTokenPlanLayout =
      instanceDeclParameterSourcePlan? parameters := by
  cases parameters with
  | none => simp [instanceDeclParameterInput, instanceDeclParameterSourcePlan?]
  | some value =>
      simp only [instanceDeclParameterInput, Option.map_some,
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
        simp [instanceDeclParameterSourcePlan?, headEq, tailEq,
          TokenPlan.concat_cons]

private theorem instanceDeclOptionalGenericInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (genericPrefix : Option GenericPrefix) :
    (EbnfValue.optional (.atom (.nonterminal .genericPrefix))
      (genericPrefix.map
        (EbnfValue.ruleAtom (file := file) (tokens := tokens)
          .genericPrefix))).tokenPlan? sourceRuleTokenPlanLayout =
      instanceDeclOptionalGenericPlan? genericPrefix := by
  change Option (RuleValue .genericPrefix) at genericPrefix
  cases genericPrefix with
  | none =>
      rw [Option.map_none, EbnfValue.tokenPlan?_optional_none]
      rfl
  | some generic =>
      rw [Option.map_some, EbnfValue.tokenPlan?_optional_some,
        EbnfValue.tokenPlan?_ruleAtom]
      rfl

private theorem instanceDeclOptionalDefaultInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (defaultToken : Option (MatchedTerminal file tokens
      (.hardKeyword .defaultKw))) :
    (EbnfValue.optional (.atom (.terminal (.hardKeyword .defaultKw)))
      (defaultToken.map fun terminal =>
        EbnfValue.terminalAtom (.hardKeyword .defaultKw) terminal)).tokenPlan?
        sourceRuleTokenPlanLayout =
      some (instanceDeclOptionalDefaultPlan defaultToken) := by
  cases defaultToken with
  | none =>
      rw [Option.map_none, EbnfValue.tokenPlan?_optional_none]
      rfl
  | some terminal =>
      rw [Option.map_some, EbnfValue.tokenPlan?_optional_some,
        EbnfValue.tokenPlan?_terminalAtom,
        MatchedTerminal.physicalTokenPlan_hardKeyword]
      rfl

private theorem instanceDeclInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (genericPrefix : Option GenericPrefix)
    (defaultToken : Option (MatchedTerminal file tokens
      (.hardKeyword .defaultKw)))
    (instanceKw : MatchedTerminal file tokens (.hardKeyword .instanceKw))
    (main : TypeExpr)
    (colon : MatchedTerminal file tokens (.symbol .colon))
    (className : QualifiedName)
    (parameters : InstanceDeclParameters file tokens)
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (methods : List FunctionDecl)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace)) :
    (instanceDeclInput genericPrefix defaultToken instanceKw main colon
      className parameters
      openBrace methods closeBrace).tokenPlan? sourceRuleTokenPlanLayout = (do
      let genericPlan ← instanceDeclOptionalGenericPlan? genericPrefix
      let mainPlan ← typeAtomPlan? main
      let parameterPlan ← instanceDeclParameterSourcePlan? parameters
      let methodPlans ← methods.mapM functionDeclPlan?
      pure (.concat [
        genericPlan,
        instanceDeclOptionalDefaultPlan defaultToken,
        .exact (.hardKeyword .instanceKw) instanceKw.span,
        mainPlan,
        .exact (.symbol .colon) colon.span,
        qualifiedNamePlan className,
        parameterPlan,
        .exact (.symbol .leftBrace) openBrace.span,
        .concat methodPlans,
        .exact (.symbol .rightBrace) closeBrace.span])) := by
  unfold instanceDeclInput
  rw [EbnfValue.tokenPlan?_sequence]
  rw [EbnfValues.tokenPlan?_cons,
    instanceDeclOptionalGenericInput_tokenPlan?]
  rw [EbnfValues.tokenPlan?_cons,
    instanceDeclOptionalDefaultInput_tokenPlan?]
  simp only [EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValue.tokenPlan?_ruleAtom,
    EbnfValue.tokenPlan?_star,
    EbnfValues.tokenPlan?_nil]
  rw [instanceDeclParameterInput_tokenPlan?,
    ruleAtomValues_tokenPlans? .instanceMethod methods,
    instanceMethodRulePlans_eq]
  simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?,
    MatchedTerminal.physicalTokenPlan_hardKeyword,
    MatchedTerminal.physicalTokenPlan_symbol]
  cases genericEq : instanceDeclOptionalGenericPlan? genericPrefix <;>
    cases mainEq : typeAtomPlan? main <;>
      cases parameterEq : instanceDeclParameterSourcePlan? parameters <;>
      cases methodsEq : methods.mapM functionDeclPlan? <;>
    simp [TokenPlan.concat_cons]

private theorem instanceDeclPlan?_sourceLoc
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (genericPrefix : Option GenericPrefix)
    (defaultToken : Option (MatchedTerminal file tokens
      (.hardKeyword .defaultKw)))
    (_instanceKw : MatchedTerminal file tokens (.hardKeyword .instanceKw))
    (main : TypeExpr)
    (_colon : MatchedTerminal file tokens (.symbol .colon))
    (className : QualifiedName)
    (parameters : InstanceDeclParameters file tokens)
    (_openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (methods : List FunctionDecl)
    (_closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (defaultProjects : ∀ terminal, defaultToken = some terminal →
      RuleReduction.MarkerProjects file tokens terminal .defaultModifier)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    instanceDeclPlan? (sourceLoc witness {
      genericPrefix := genericPrefix
      default := match defaultToken with
        | none => none
        | some terminal => some (RuleReduction.marker terminal
            (defaultProjects terminal rfl))
      main := main
      className := className
      parameters := RuleReduction.arguments parameters
      methods := methods
    } : InstanceDecl) = (do
      let genericPlan ← instanceDeclOptionalGenericPlan? genericPrefix
      let mainPlan ← typeAtomPlan? main
      let parameterPlan ← instanceDeclParameterPlainPlan? parameters
      let methodPlans ← methods.mapM functionDeclPlan?
      pure (.enclose witness.span (.concat [
        genericPlan,
        instanceDeclOptionalDefaultPlan defaultToken,
        .plain (.hardKeyword .instanceKw),
        mainPlan,
        .plain (.symbol .colon),
        qualifiedNamePlan className,
        parameterPlan,
        .plain (.symbol .leftBrace),
        .concat methodPlans,
        .plain (.symbol .rightBrace)]))) := by
  unfold instanceDeclPlan?
  simp only [sourceLoc, RuleReduction.arguments]
  unfoldSignatureOptionalPlanCore
  unfoldSignatureOptionalMarkerCore
  unfoldSignatureMarkerCore
  unfoldOptionalNonemptyTypePlanCore
  unfoldNonemptyTypePlanCore
  rwDeclarationPlansMapM
  cases genericPrefix <;> cases defaultToken <;> cases parameters with
  | none =>
      simp [instanceDeclOptionalGenericPlan?, instanceDeclOptionalDefaultPlan,
        instanceDeclParameterPlainPlan?, RuleReduction.marker,
        RuleReduction.terminalLoc]
  | some value =>
      rcases value with ⟨openParen, values, closeParen, unitValue⟩
      cases unitValue
      simp only [instanceDeclOptionalGenericPlan?,
        instanceDeclOptionalDefaultPlan, instanceDeclParameterPlainPlan?,
        RuleReduction.marker, RuleReduction.terminalLoc]
      unfoldInstanceDeclNonemptyTypeExprPlansCore
      rw [typeExprPlans_eq_mapM]
      cases headEq : typeExprPlanAt? false values.head <;>
        cases tailEq : values.tail.mapM typeExprPlan? <;>
      simp [typeExprPlan?, headEq]

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

private theorem instanceDeclParameterSourcePlan?_weakens
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : InstanceDeclParameters file tokens)
    {sourcePlan : TokenPlan}
    (sourceEq : instanceDeclParameterSourcePlan? parameters = some sourcePlan) :
    ∃ targetPlan,
      instanceDeclParameterPlainPlan? parameters = some targetPlan ∧
      sourcePlan.WeakensTo targetPlan := by
  cases parameters with
  | none =>
      simp [instanceDeclParameterSourcePlan?, instanceDeclParameterPlainPlan?]
        at sourceEq ⊢
      subst sourcePlan
      exact TokenPlan.WeakensTo.refl _
  | some value =>
      cases headEq : typeExprPlan? value.2.1.head with
      | none => simp [instanceDeclParameterSourcePlan?, headEq] at sourceEq
      | some headPlan =>
          cases tailEq : value.2.1.tail.mapM typeExprPlan? with
          | none =>
              simp [instanceDeclParameterSourcePlan?, headEq, tailEq]
                at sourceEq
          | some tailPlans =>
              simp [instanceDeclParameterSourcePlan?, headEq, tailEq]
                at sourceEq
              subst sourcePlan
              refine ⟨TokenPlan.parens
                (headPlan.append (TokenPlan.commaTail tailPlans)), ?_, ?_⟩
              · simp [instanceDeclParameterPlainPlan?, headEq, tailEq]
              · intro actual relation
                exact TokenSlot.ListMatches.exactParensToPlain relation

/-- Instance declarations preserve their recursive child plans and weaken only
the punctuation fixed by the declaration grammar. -/
theorem instanceDecl_tokenPlanSound :
    GrammarRuleTokenPlanSound .instanceDecl := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  change TokenPlanEvidence (instanceDeclPlan? output)
    (PhysicalTokens tokens origin finish)
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | instanceDecl origin finish genericPrefix defaultToken instanceKw main colon
      className parameters openBrace methods closeBrace defaultProjects witness =>
      rw [← inputEq] at inputEvidence
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout = (do
          let genericPlan ← instanceDeclOptionalGenericPlan? genericPrefix
          let mainPlan ← typeAtomPlan? main
          let parameterPlan ← instanceDeclParameterSourcePlan? parameters
          let methodPlans ← methods.mapM functionDeclPlan?
          pure (.concat [
            genericPlan,
            instanceDeclOptionalDefaultPlan defaultToken,
            .exact (.hardKeyword .instanceKw) instanceKw.span,
            mainPlan,
            .exact (.symbol .colon) colon.span,
            qualifiedNamePlan className,
            parameterPlan,
            .exact (.symbol .leftBrace) openBrace.span,
            .concat methodPlans,
            .exact (.symbol .rightBrace) closeBrace.span])) := by
        rw [inputEq]
        simp only [m2cV1, m2cV1Rhs, Grammar.hardKeyword, Grammar.terminal,
          Grammar.sequence, Grammar.symbol, Grammar.nonterminal,
          Grammar.optional, Grammar.list1, Grammar.star]
        rw [EbnfValue.tokenPlan?_transport]
        change (instanceDeclInput genericPrefix defaultToken instanceKw main
          colon className parameters openBrace methods closeBrace).tokenPlan?
            sourceRuleTokenPlanLayout = _
        exact instanceDeclInput_tokenPlan? genericPrefix defaultToken instanceKw
          main colon className parameters openBrace methods closeBrace
      have physicalEvidence := inputEvidence.candidate_eq candidateEq
      cases genericEq : instanceDeclOptionalGenericPlan? genericPrefix with
      | none => simp [genericEq, TokenPlanEvidence] at physicalEvidence
      | some genericPlan =>
          cases mainEq : typeAtomPlan? main with
          | none =>
              simp [genericEq, mainEq, TokenPlanEvidence] at physicalEvidence
          | some mainPlan =>
              cases parameterSourceEq :
                  instanceDeclParameterSourcePlan? parameters with
              | none =>
                  simp [genericEq, mainEq, parameterSourceEq,
                    TokenPlanEvidence] at physicalEvidence
              | some parameterSourcePlan =>
                  cases methodsEq : methods.mapM functionDeclPlan? with
                  | none =>
                      simp [genericEq, mainEq, parameterSourceEq, methodsEq,
                        TokenPlanEvidence] at physicalEvidence
                  | some methodPlans =>
                      simp only [genericEq, mainEq, parameterSourceEq,
                        methodsEq] at physicalEvidence
                      rcases instanceDeclParameterSourcePlan?_weakens parameters
                          parameterSourceEq with
                        ⟨parameterTargetPlan, parameterTargetEq,
                          parameterWeakens⟩
                      let defaultPlan :=
                        instanceDeclOptionalDefaultPlan defaultToken
                      let classPlan := qualifiedNamePlan className
                      let sourceCore := TokenPlan.concat [
                        genericPlan,
                        defaultPlan,
                        .exact (.hardKeyword .instanceKw) instanceKw.span,
                        mainPlan,
                        .exact (.symbol .colon) colon.span,
                        classPlan,
                        parameterSourcePlan,
                        .exact (.symbol .leftBrace) openBrace.span,
                        .concat methodPlans,
                        .exact (.symbol .rightBrace) closeBrace.span]
                      let targetCore := TokenPlan.concat [
                        genericPlan,
                        defaultPlan,
                        .plain (.hardKeyword .instanceKw),
                        mainPlan,
                        .plain (.symbol .colon),
                        classPlan,
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
                            (TokenPlan.WeakensTo.refl defaultPlan)
                            (TokenPlan.WeakensTo.append
                              (TokenPlan.WeakensTo.exactToPlain
                                (.hardKeyword .instanceKw) instanceKw.span)
                              (TokenPlan.WeakensTo.append
                                (TokenPlan.WeakensTo.refl mainPlan)
                                (TokenPlan.WeakensTo.append
                                  (TokenPlan.WeakensTo.exactToPlain
                                    (.symbol .colon) colon.span)
                                  (TokenPlan.WeakensTo.append
                                    (TokenPlan.WeakensTo.refl classPlan)
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
                                            closeBrace.span))))))))))
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
                            simp [instanceDeclOptionalGenericPlan?] at genericEq
                            subst genericPlan
                            exact TokenPlan.WellAnchored.empty
                        | some generic =>
                            exact genericPrefixPlan?_wellAnchored generic
                              genericPlan genericEq
                      have defaultAnchored : defaultPlan.WellAnchored := by
                        cases defaultToken with
                        | none => exact TokenPlan.WellAnchored.empty
                        | some terminal => exact TokenPlan.WellAnchored.exact _ _
                      have targetAnchored : targetCore.WellAnchored := by
                        have suffixAnchored :=
                          TokenPlan.WellAnchored.concat_plain_bookended_six
                            (.hardKeyword .instanceKw) (.symbol .rightBrace)
                            mainPlan (.plain (.symbol .colon)) classPlan
                            parameterTargetPlan
                            (.plain (.symbol .leftBrace))
                            (.concat methodPlans)
                        simpa [targetCore, TokenPlan.concat,
                          TokenPlan.append] using
                            TokenPlan.WellAnchored.append genericAnchored
                              (TokenPlan.WellAnchored.append defaultAnchored
                                suffixAnchored)
                      have enclosed := TokenPlanEvidence.enclose
                        (TokenPlanEvidence.some targetRelation)
                        (fun plan success => by
                          simp only [Option.some.injEq] at success
                          subst plan
                          exact targetAnchored)
                        witness.consumed
                      apply enclosed.candidate_eq
                      refine Eq.trans ?_ (instanceDeclPlan?_sourceLoc
                        genericPrefix defaultToken instanceKw main colon
                        className parameters openBrace methods closeBrace
                        defaultProjects witness).symm
                      rw [genericEq, mainEq, parameterTargetEq, methodsEq]
                      simp [targetCore, defaultPlan, classPlan]

end Solcore.Surface.Multi
