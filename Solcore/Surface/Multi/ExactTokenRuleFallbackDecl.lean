import Solcore.Surface.Multi.ExactTokenAnchoring
import Solcore.Surface.Multi.ExactTokenExpressionAnchoring
import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace
open Lean Lean.Elab Lean.Elab.Tactic

elab "unfoldFallbackOptionalPlanCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.optionalPlan?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] => unfoldTarget declaration
  | _ => throwError "the declaration visitor has an unknown optional helper"

elab "unfoldFallbackOptionalMarkerCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.optionalMarkerPlan?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] => unfoldTarget declaration
  | _ => throwError "the declaration visitor has an unknown marker helper"

elab "unfoldFallbackMarkerCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.markerPlan?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] => unfoldTarget declaration
  | _ => throwError "the declaration visitor has an unknown marker plan"

elab "unfoldFallbackReturnCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.optionalReturnTypePlan?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] => unfoldTarget declaration
  | _ => throwError "the declaration visitor has an unknown return helper"

elab "rwFallbackPlansMapM" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.plans?_eq_mapM
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] =>
      rewriteTarget (mkIdent declaration).raw false
  | _ => throwError "the declaration visitor has an unknown list theorem"

private def optionalGenericPlan? : Option GenericPrefix → Option TokenPlan
  | none => some .empty
  | some value => genericPrefixPlan? value

private def optionalKeywordPlan
    {file : WorkspaceFile} {tokens : List Token} (keyword : HardKeyword) :
    Option (MatchedTerminal file tokens (.hardKeyword keyword)) → TokenPlan
  | none => .empty
  | some terminal => .exact (.hardKeyword keyword) terminal.span

private def fallbackReturnSourcePlan?
    {file : WorkspaceFile} {tokens : List Token} :
    Option (MatchedTerminal file tokens (.symbol .arrow) ×
      (TypeExpr × Unit)) → Option TokenPlan
  | none => some .empty
  | some value => do
      let typePlan ← typeExprPlan? value.2.1
      pure ((TokenPlan.exact (.symbol .arrow) value.1.span).append typePlan)

private def fallbackReturnPlainPlan?
    {file : WorkspaceFile} {tokens : List Token} :
    Option (MatchedTerminal file tokens (.symbol .arrow) ×
      (TypeExpr × Unit)) → Option TokenPlan
  | none => some .empty
  | some value => do
      let typePlan ← typeExprPlan? value.2.1
      pure ((TokenPlan.plain (.symbol .arrow)).append typePlan)

private abbrev fallbackReturnChildren : List EbnfExpr := [
  .atom (.terminal (.symbol .arrow)),
  .atom (.nonterminal .type)]

private abbrev fallbackDeclChildren : List EbnfExpr := [
  .optional (.atom (.nonterminal .genericPrefix)),
  .optional (.atom (.terminal (.hardKeyword .publicKw))),
  .optional (.atom (.terminal (.hardKeyword .payableKw))),
  .atom (.terminal (.hardKeyword .fallbackKw)),
  .atom (.terminal (.symbol .leftParen)),
  .list0 (.atom (.nonterminal .parameter)),
  .atom (.terminal (.symbol .rightParen)),
  .optional (.sequence fallbackReturnChildren),
  .atom (.nonterminal .body)]

private def fallbackDeclInput
    {file : WorkspaceFile} {tokens : List Token}
    (genericPrefix : Option GenericPrefix)
    (publicToken : Option (MatchedTerminal file tokens
      (.hardKeyword .publicKw)))
    (payableToken : Option (MatchedTerminal file tokens
      (.hardKeyword .payableKw)))
    (fallbackKw : MatchedTerminal file tokens
      (.hardKeyword .fallbackKw))
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (parameters : List Parameter)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (returnValue : Option
      (MatchedTerminal file tokens (.symbol .arrow) ×
        (TypeExpr × Unit)))
    (body : Body) :
    EbnfValue file tokens (.sequence fallbackDeclChildren) :=
  EbnfValue.sequence _ <|
    EbnfValues.cons _ _
      (EbnfValue.optional _
        (genericPrefix.map (EbnfValue.ruleAtom .genericPrefix))) <|
    EbnfValues.cons _ _
      (EbnfValue.optional _ (publicToken.map fun terminal =>
        EbnfValue.terminalAtom (.hardKeyword .publicKw) terminal)) <|
    EbnfValues.cons _ _
      (EbnfValue.optional _ (payableToken.map fun terminal =>
        EbnfValue.terminalAtom (.hardKeyword .payableKw) terminal)) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.hardKeyword .fallbackKw) fallbackKw) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .leftParen) openParen) <|
    EbnfValues.cons _ _
      (EbnfValue.list0 _
        (parameters.map (EbnfValue.ruleAtom .parameter))) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .rightParen) closeParen) <|
    EbnfValues.cons _ _
      (EbnfValue.optional _ (returnValue.map fun value =>
        EbnfValue.sequence _ <|
          EbnfValues.cons _ _
            (EbnfValue.terminalAtom (.symbol .arrow) value.1) <|
          EbnfValues.cons _ _
            (EbnfValue.ruleAtom .type value.2.1)
            EbnfValues.nil)) <|
    EbnfValues.cons _ _
      (EbnfValue.ruleAtom .body body)
      EbnfValues.nil

private theorem matchedHardKeyword_physicalTokenPlan
    {file : WorkspaceFile} {tokens : List Token} (keyword : HardKeyword)
    (matched : MatchedTerminal file tokens (.hardKeyword keyword)) :
    matched.physicalTokenPlan =
      TokenPlan.exact (.hardKeyword keyword) matched.span := by
  rcases matched with
    ⟨cursor, value, span, terminalAt, matchedEvidence⟩
  cases terminalAt with
  | retained token inRange lookup valid =>
      simp [MatchedTerminal.physicalTokenPlan, TerminalMatches]
        at matchedEvidence ⊢
      rw [matchedEvidence]
  | endOfFile atEnd =>
      simp [TerminalMatches] at matchedEvidence

private theorem matchedSymbol_physicalTokenPlan
    {file : WorkspaceFile} {tokens : List Token} (symbol : Symbol)
    (matched : MatchedTerminal file tokens (.symbol symbol)) :
    matched.physicalTokenPlan =
      TokenPlan.exact (.symbol symbol) matched.span := by
  rcases matched with
    ⟨cursor, value, span, terminalAt, matchedEvidence⟩
  cases terminalAt with
  | retained token inRange lookup valid =>
      simp [MatchedTerminal.physicalTokenPlan, TerminalMatches]
        at matchedEvidence ⊢
      rw [matchedEvidence]
  | endOfFile atEnd =>
      simp [TerminalMatches] at matchedEvidence

private theorem parameterRuleValues_tokenPlans?
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : List Parameter) :
    (parameters.map (EbnfValue.ruleAtom
      (file := file) (tokens := tokens) .parameter)).mapM
        (fun value => value.tokenPlan? sourceRuleTokenPlanLayout) =
      parameters.mapM parameterTokenPlan? := by
  rw [List.mapM_map]
  simp [Function.comp_def, sourceRuleTokenPlanLayout, ruleTokenPlan?]
  congr 1

private theorem optionalGenericInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (genericPrefix : Option GenericPrefix) :
    (EbnfValue.optional
      (file := file) (tokens := tokens)
      (.atom (.nonterminal .genericPrefix))
      (genericPrefix.map (EbnfValue.ruleAtom .genericPrefix))).tokenPlan?
        sourceRuleTokenPlanLayout = optionalGenericPlan? genericPrefix := by
  cases genericPrefix with
  | none =>
      change (EbnfValue.optional
        (.atom (.nonterminal .genericPrefix))
        (none : Option (EbnfValue file tokens
          (.atom (.nonterminal .genericPrefix))))).tokenPlan?
          sourceRuleTokenPlanLayout = some TokenPlan.empty
      rw [EbnfValue.tokenPlan?_optional_none]
  | some generic =>
      change (EbnfValue.optional
        (.atom (.nonterminal .genericPrefix))
        (some (EbnfValue.ruleAtom .genericPrefix generic))).tokenPlan?
          sourceRuleTokenPlanLayout = genericPrefixPlan? generic
      rw [EbnfValue.tokenPlan?_optional_some,
        EbnfValue.tokenPlan?_ruleAtom]
      rfl

private theorem optionalKeywordInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token} (keyword : HardKeyword)
    (value : Option (MatchedTerminal file tokens (.hardKeyword keyword))) :
    (EbnfValue.optional
      (.atom (.terminal (.hardKeyword keyword)))
      (value.map fun terminal =>
        EbnfValue.terminalAtom (.hardKeyword keyword) terminal)).tokenPlan?
        sourceRuleTokenPlanLayout =
      some (optionalKeywordPlan keyword value) := by
  cases value with
  | none =>
      rw [Option.map_none, EbnfValue.tokenPlan?_optional_none]
      rfl
  | some terminal =>
      rw [Option.map_some, EbnfValue.tokenPlan?_optional_some,
        EbnfValue.tokenPlan?_terminalAtom,
        matchedHardKeyword_physicalTokenPlan]
      rfl

private theorem parameterListInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : List Parameter) :
    (EbnfValue.list0
      (file := file) (tokens := tokens)
      (.atom (.nonterminal .parameter))
      (parameters.map (EbnfValue.ruleAtom .parameter))).tokenPlan?
        sourceRuleTokenPlanLayout = (do
      let plans ← parameters.mapM parameterTokenPlan?
      pure (TokenPlan.commaSeparated plans)) := by
  rw [EbnfValue.tokenPlan?_list0]
  rw [parameterRuleValues_tokenPlans? parameters]

private theorem fallbackReturnInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (returnValue : Option
      (MatchedTerminal file tokens (.symbol .arrow) ×
        (TypeExpr × Unit))) :
    (EbnfValue.optional
      (.sequence fallbackReturnChildren)
      (returnValue.map fun value =>
        EbnfValue.sequence _ <|
          EbnfValues.cons _ _
            (EbnfValue.terminalAtom (.symbol .arrow) value.1) <|
          EbnfValues.cons _ _
            (EbnfValue.ruleAtom .type value.2.1)
            EbnfValues.nil)).tokenPlan? sourceRuleTokenPlanLayout =
      fallbackReturnSourcePlan? returnValue := by
  cases returnValue with
  | none =>
      rw [Option.map_none, EbnfValue.tokenPlan?_optional_none]
      rfl
  | some value =>
      rw [Option.map_some, EbnfValue.tokenPlan?_optional_some,
        EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValues.tokenPlan?_nil,
        matchedSymbol_physicalTokenPlan]
      cases typePlanEq : typeExprPlan? value.2.1 <;>
        simp [fallbackReturnSourcePlan?, typePlanEq,
          sourceRuleTokenPlanLayout, ruleTokenPlan?]

private theorem fallbackDeclInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (genericPrefix : Option GenericPrefix)
    (publicToken : Option (MatchedTerminal file tokens
      (.hardKeyword .publicKw)))
    (payableToken : Option (MatchedTerminal file tokens
      (.hardKeyword .payableKw)))
    (fallbackKw : MatchedTerminal file tokens
      (.hardKeyword .fallbackKw))
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (parameters : List Parameter)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (returnValue : Option
      (MatchedTerminal file tokens (.symbol .arrow) ×
        (TypeExpr × Unit)))
    (body : Body) :
    (fallbackDeclInput genericPrefix publicToken payableToken fallbackKw
      openParen parameters closeParen returnValue body).tokenPlan?
        sourceRuleTokenPlanLayout = (do
      let genericPlan ← optionalGenericPlan? genericPrefix
      let parameterPlans ← parameters.mapM parameterTokenPlan?
      let returnPlan ← fallbackReturnSourcePlan? returnValue
      let bodyPlan ← bodyTokenPlan? .braced body
      pure (TokenPlan.concat [
        genericPlan,
        optionalKeywordPlan .publicKw publicToken,
        optionalKeywordPlan .payableKw payableToken,
        TokenPlan.exact (.hardKeyword .fallbackKw) fallbackKw.span,
        TokenPlan.concat [
          TokenPlan.exact (.symbol .leftParen) openParen.span,
          TokenPlan.commaSeparated parameterPlans,
          TokenPlan.exact (.symbol .rightParen) closeParen.span],
        returnPlan,
        bodyPlan])) := by
  unfold fallbackDeclInput
  rw [EbnfValue.tokenPlan?_sequence,
    EbnfValues.tokenPlan?_cons,
    optionalGenericInput_tokenPlan? genericPrefix,
    EbnfValues.tokenPlan?_cons,
    optionalKeywordInput_tokenPlan? .publicKw publicToken,
    EbnfValues.tokenPlan?_cons,
    optionalKeywordInput_tokenPlan? .payableKw payableToken,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValues.tokenPlan?_cons,
    parameterListInput_tokenPlan? parameters,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValues.tokenPlan?_cons,
    fallbackReturnInput_tokenPlan? returnValue,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_ruleAtom,
    EbnfValues.tokenPlan?_nil,
    matchedHardKeyword_physicalTokenPlan,
    matchedSymbol_physicalTokenPlan,
    matchedSymbol_physicalTokenPlan]
  cases genericEq : optionalGenericPlan? genericPrefix <;>
    cases parametersEq : parameters.mapM parameterTokenPlan? <;>
    cases returnEq : fallbackReturnSourcePlan? returnValue <;>
    cases bodyEq : bodyTokenPlan? .braced body <;>
    simp [bodyEq, sourceRuleTokenPlanLayout, ruleTokenPlan?,
      TokenPlan.concat_cons, TokenPlan.append_assoc]

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
        ⟨middleActual, lastActual, actualEq,
          middleRelation, lastRelation⟩
      rw [actualEq]
      exact .required firstMatch.toPlain <|
        middleRelation.append lastRelation.requiredHeadToPlain

private theorem TokenSlot.ListMatches.replaceMiddle
    {before source target after : TokenPlan} {actual : List Token}
    (convert : ∀ part,
      TokenSlot.ListMatches source.slots part →
        TokenSlot.ListMatches target.slots part)
    (relation : TokenSlot.ListMatches
      (before.append (source.append after)).slots actual) :
    TokenSlot.ListMatches
      (before.append (target.append after)).slots actual := by
  change TokenSlot.ListMatches
    (before.slots ++ (source.slots ++ after.slots)) actual at relation
  change TokenSlot.ListMatches
    (before.slots ++ (target.slots ++ after.slots)) actual
  rcases relation.split_append with
    ⟨beforeActual, restActual, actualEq,
      beforeRelation, restRelation⟩
  rcases restRelation.split_append with
    ⟨sourceActual, afterActual, restEq,
      sourceRelation, afterRelation⟩
  rw [actualEq, restEq]
  exact beforeRelation.append <|
    (convert sourceActual sourceRelation).append afterRelation

private theorem optionalGenericPlan_wellAnchored
    (genericPrefix : Option GenericPrefix) (plan : TokenPlan)
    (success : optionalGenericPlan? genericPrefix = some plan) :
    plan.WellAnchored := by
  cases genericPrefix with
  | none =>
      simp [optionalGenericPlan?] at success
      subst plan
      exact TokenPlan.WellAnchored.empty
  | some generic =>
      change genericPrefixPlan? generic = some plan at success
      exact genericPrefixPlan?_wellAnchored generic plan success

private theorem optionalKeywordPlan_wellAnchored
    {file : WorkspaceFile} {tokens : List Token} (keyword : HardKeyword)
    (value : Option (MatchedTerminal file tokens (.hardKeyword keyword))) :
    (optionalKeywordPlan keyword value).WellAnchored := by
  cases value with
  | none => exact TokenPlan.WellAnchored.empty
  | some terminal => exact TokenPlan.WellAnchored.exact _ _

private theorem fallbackReturnPlan_conversion
    {file : WorkspaceFile} {tokens : List Token}
    (returnValue : Option
      (MatchedTerminal file tokens (.symbol .arrow) ×
        (TypeExpr × Unit)))
    (sourcePlan : TokenPlan)
    (sourceSuccess : fallbackReturnSourcePlan? returnValue =
      some sourcePlan) :
    ∃ plainPlan,
      fallbackReturnPlainPlan? returnValue = some plainPlan ∧
      (∀ actual,
        TokenSlot.ListMatches sourcePlan.slots actual →
          TokenSlot.ListMatches plainPlan.slots actual) ∧
      plainPlan.WellAnchored := by
  cases returnValue with
  | none =>
      simp [fallbackReturnSourcePlan?] at sourceSuccess
      subst sourcePlan
      refine ⟨TokenPlan.empty, rfl, ?_, TokenPlan.WellAnchored.empty⟩
      intro actual relation
      exact relation
  | some value =>
      cases typeEq : typeExprPlan? value.2.1 with
      | none =>
          simp [fallbackReturnSourcePlan?, typeEq] at sourceSuccess
      | some typePlan =>
          simp [fallbackReturnSourcePlan?, typeEq] at sourceSuccess
          subst sourcePlan
          let plainPlan :=
            (TokenPlan.plain (.symbol .arrow)).append typePlan
          refine ⟨plainPlan, ?_, ?_, ?_⟩
          · simp [fallbackReturnPlainPlan?, typeEq, plainPlan]
          · intro actual relation
            apply TokenSlot.ListMatches.exactBetweenToPlain
              (left := TokenPlan.empty)
              (right := typePlan)
              (kind := .symbol .arrow)
              (span := value.1.span)
            simpa [TokenPlan.append_assoc] using relation
          · apply TokenPlan.WellAnchored.append
              (TokenPlan.WellAnchored.plain (.symbol .arrow))
            exact typeExprPlan?_wellAnchored value.2.1 typePlan typeEq

private theorem fallbackDeclPlan?_sourceLoc
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (genericPrefix : Option GenericPrefix)
    (publicToken : Option (MatchedTerminal file tokens
      (.hardKeyword .publicKw)))
    (payableToken : Option (MatchedTerminal file tokens
      (.hardKeyword .payableKw)))
    (fallbackKw : MatchedTerminal file tokens
      (.hardKeyword .fallbackKw))
    (parameters : List Parameter)
    (returnValue : Option
      (MatchedTerminal file tokens (.symbol .arrow) ×
        (TypeExpr × Unit)))
    (body : Body)
    (publicProjects : ∀ terminal, publicToken = some terminal →
      RuleReduction.MarkerProjects file tokens terminal .publicModifier)
    (payableProjects : ∀ terminal, payableToken = some terminal →
      RuleReduction.MarkerProjects file tokens terminal .payableModifier)
    (fallbackProjects : RuleReduction.MarkerProjects file tokens
      fallbackKw .fallbackName)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    fallbackDeclPlan? (sourceLoc witness {
      genericPrefix := genericPrefix
      «public» := match publicToken with
        | none => none
        | some terminal => some (RuleReduction.marker terminal
            (publicProjects terminal rfl))
      payable := match payableToken with
        | none => none
        | some terminal => some (RuleReduction.marker terminal
            (payableProjects terminal rfl))
      marker := RuleReduction.marker fallbackKw fallbackProjects
      parameters := parameters
      returnType := returnValue.map fun value => value.2.1
      body := body
    } : FallbackDecl) = (do
      let genericPlan ← optionalGenericPlan? genericPrefix
      let parameterPlans ← parameters.mapM parameterTokenPlan?
      let returnPlan ← fallbackReturnPlainPlan? returnValue
      let bodyPlan ← bodyTokenPlan? .braced body
      pure (TokenPlan.enclose witness.span (TokenPlan.concat [
        genericPlan,
        optionalKeywordPlan .publicKw publicToken,
        optionalKeywordPlan .payableKw payableToken,
        TokenPlan.exact (.hardKeyword .fallbackKw) fallbackKw.span,
        TokenPlan.parens (TokenPlan.commaSeparated parameterPlans),
        returnPlan,
        bodyPlan]))) := by
  unfold fallbackDeclPlan?
  simp only [sourceLoc]
  rwFallbackPlansMapM
  unfoldFallbackOptionalPlanCore
  unfoldFallbackOptionalMarkerCore
  unfoldFallbackMarkerCore
  unfoldFallbackReturnCore
  cases genericPrefix <;>
    cases publicToken <;>
    cases payableToken <;>
    cases returnValue <;>
    simp [optionalGenericPlan?, optionalKeywordPlan,
      fallbackReturnPlainPlan?, RuleReduction.marker,
      RuleReduction.terminalLoc, TokenPlan.concat_cons]

theorem fallbackDecl_tokenPlanSound :
    GrammarRuleTokenPlanSound .fallbackDecl := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  change TokenPlanEvidence (fallbackDeclPlan? output)
    (PhysicalTokens tokens origin finish)
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | fallbackDecl origin finish genericPrefix publicToken payableToken
      fallbackKw openParen parameters closeParen returnValue body
      publicProjects payableProjects fallbackProjects witness =>
      change List Parameter at parameters
      change Body at body
      simp only [m2cV1, m2cV1Rhs, Grammar.sequence,
        Grammar.nonterminal, Grammar.hardKeyword, Grammar.symbol,
        Grammar.terminal, Grammar.list0, Grammar.optional] at inputEvidence
      rw [EbnfValue.tokenPlan?_transport] at inputEvidence
      change TokenPlanEvidence
        ((fallbackDeclInput genericPrefix publicToken payableToken
          fallbackKw openParen parameters closeParen returnValue body).tokenPlan?
            sourceRuleTokenPlanLayout)
        (PhysicalTokens tokens origin finish) at inputEvidence
      have sourceCandidateEq := fallbackDeclInput_tokenPlan?
        genericPrefix publicToken payableToken fallbackKw openParen
        parameters closeParen returnValue body
      have physicalEvidence := inputEvidence.candidate_eq sourceCandidateEq
      cases genericEq : optionalGenericPlan? genericPrefix with
      | none =>
          simp [genericEq, TokenPlanEvidence] at physicalEvidence
      | some genericPlan =>
          cases parameterEq : parameters.mapM parameterTokenPlan? with
          | none =>
              simp [genericEq, parameterEq, TokenPlanEvidence]
                at physicalEvidence
          | some parameterPlans =>
              cases returnSourceEq :
                  fallbackReturnSourcePlan? returnValue with
              | none =>
                  simp [genericEq, parameterEq, returnSourceEq,
                    TokenPlanEvidence] at physicalEvidence
              | some sourceReturnPlan =>
                  cases bodyEq : bodyTokenPlan? .braced body with
                  | none =>
                      simp [genericEq, parameterEq, returnSourceEq,
                        bodyEq, TokenPlanEvidence] at physicalEvidence
                  | some bodyPlan =>
                      simp only [genericEq, parameterEq, returnSourceEq,
                        bodyEq] at physicalEvidence
                      let publicPlan := optionalKeywordPlan
                        .publicKw publicToken
                      let payablePlan := optionalKeywordPlan
                        .payableKw payableToken
                      let markerPlan := TokenPlan.exact
                        (.hardKeyword .fallbackKw) fallbackKw.span
                      let sourceParameterPlan := TokenPlan.concat [
                        TokenPlan.exact (.symbol .leftParen) openParen.span,
                        TokenPlan.commaSeparated parameterPlans,
                        TokenPlan.exact (.symbol .rightParen) closeParen.span]
                      let plainParameterPlan := TokenPlan.parens
                        (TokenPlan.commaSeparated parameterPlans)
                      let sourceCore := TokenPlan.concat [
                        genericPlan, publicPlan, payablePlan, markerPlan,
                        sourceParameterPlan, sourceReturnPlan, bodyPlan]
                      rcases physicalEvidence with
                        ⟨plan, planEq, relation⟩
                      change some sourceCore = some plan at planEq
                      injection planEq with planEq
                      subst plan
                      let beforeParameters := TokenPlan.concat [
                        genericPlan, publicPlan, payablePlan, markerPlan]
                      let afterParameters := TokenPlan.concat [
                        sourceReturnPlan, bodyPlan]
                      have parameterShape : TokenSlot.ListMatches
                          (beforeParameters.append
                            (sourceParameterPlan.append
                              afterParameters)).slots
                          (PhysicalTokens tokens origin finish) := by
                        simpa [sourceCore, beforeParameters,
                          afterParameters, TokenPlan.concat_cons,
                          TokenPlan.append_assoc] using relation
                      have parameterConverted :=
                        TokenSlot.ListMatches.replaceMiddle
                          (before := beforeParameters)
                          (source := sourceParameterPlan)
                          (target := plainParameterPlan)
                          (after := afterParameters)
                          (fun part partRelation =>
                            TokenSlot.ListMatches.exactParensToPlain
                              partRelation)
                          parameterShape
                      let parameterCore := TokenPlan.concat [
                        genericPlan, publicPlan, payablePlan, markerPlan,
                        plainParameterPlan, sourceReturnPlan, bodyPlan]
                      have parameterRelation : TokenSlot.ListMatches
                          parameterCore.slots
                          (PhysicalTokens tokens origin finish) := by
                        simpa [parameterCore, beforeParameters,
                          afterParameters, TokenPlan.concat_cons,
                          TokenPlan.append_assoc] using parameterConverted
                      rcases fallbackReturnPlan_conversion returnValue
                          sourceReturnPlan returnSourceEq with
                        ⟨plainReturnPlan, plainReturnEq,
                          convertReturn, returnAnchored⟩
                      let beforeReturn := TokenPlan.concat [
                        genericPlan, publicPlan, payablePlan, markerPlan,
                        plainParameterPlan]
                      have returnShape : TokenSlot.ListMatches
                          (beforeReturn.append
                            (sourceReturnPlan.append bodyPlan)).slots
                          (PhysicalTokens tokens origin finish) := by
                        simpa [parameterCore, beforeReturn,
                          TokenPlan.concat_cons, TokenPlan.append_assoc]
                          using parameterRelation
                      have returnConverted :=
                        TokenSlot.ListMatches.replaceMiddle
                          (before := beforeReturn)
                          (source := sourceReturnPlan)
                          (target := plainReturnPlan)
                          (after := bodyPlan)
                          convertReturn returnShape
                      let plainCore := TokenPlan.concat [
                        genericPlan, publicPlan, payablePlan, markerPlan,
                        plainParameterPlan, plainReturnPlan, bodyPlan]
                      have plainRelation : TokenSlot.ListMatches
                          plainCore.slots
                          (PhysicalTokens tokens origin finish) := by
                        simpa [plainCore, beforeReturn,
                          TokenPlan.concat_cons, TokenPlan.append_assoc]
                          using returnConverted
                      have genericAnchored :=
                        optionalGenericPlan_wellAnchored
                          genericPrefix genericPlan genericEq
                      have bodyAnchored :=
                        bracedBodyTokenPlan?_wellAnchored
                          body bodyPlan bodyEq
                      have plainAnchored : plainCore.WellAnchored := by
                        apply TokenPlan.WellAnchored.concat
                        intro candidate member
                        simp only [List.mem_cons, List.not_mem_nil,
                          or_false] at member
                        rcases member with
                          rfl | rfl | rfl | rfl | rfl | rfl | rfl
                        · exact genericAnchored
                        · exact optionalKeywordPlan_wellAnchored
                            .publicKw publicToken
                        · exact optionalKeywordPlan_wellAnchored
                            .payableKw payableToken
                        · exact TokenPlan.WellAnchored.exact _ _
                        · exact TokenPlan.WellAnchored.parens _
                        · exact returnAnchored
                        · exact bodyAnchored
                      have enclosed := TokenPlanEvidence.enclose
                        (TokenPlanEvidence.some plainRelation)
                        (fun candidate success => by
                          simp only [Option.some.injEq] at success
                          subst candidate
                          exact plainAnchored)
                        witness.consumed
                      apply enclosed.candidate_eq
                      revert publicProjects payableProjects
                        fallbackProjects
                      cases publicToken <;> cases payableToken <;>
                        intro publicProjects payableProjects fallbackProjects
                      all_goals
                        have outputEq := fallbackDeclPlan?_sourceLoc
                          genericPrefix _ _ fallbackKw parameters returnValue
                          body publicProjects payableProjects
                          fallbackProjects witness
                        rw [genericEq, parameterEq, plainReturnEq, bodyEq]
                          at outputEq
                        simpa [plainCore, publicPlan, payablePlan, markerPlan,
                          plainParameterPlan, RuleReduction.marker,
                          RuleReduction.terminalLoc] using outputEq.symm

end Solcore.Surface.Multi
