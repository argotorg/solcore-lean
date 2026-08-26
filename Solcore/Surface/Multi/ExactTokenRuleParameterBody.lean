import Solcore.Surface.Multi.ExactTokenAnchoring
import Solcore.Surface.Multi.ExactTokenExpressionAnchoring
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

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

private theorem matchedContextualKeyword_physicalTokenPlan
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

private theorem TokenPlanEvidence.exactMiddleToPlain
    {kind : TokenKind} {span : SourceSpan}
    {beforePlan afterPlan : TokenPlan} {actual : List Token}
    (evidence : TokenPlanEvidence
      (Option.some ((beforePlan.append (.exact kind span)).append afterPlan))
      actual) :
    TokenPlanEvidence
      (Option.some ((beforePlan.append (.plain kind)).append afterPlan))
      actual := by
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
    TokenSlot.ListMatches.append
      (TokenSlot.ListMatches.append prefixRelation plainRelation)
      suffixRelation

local syntax "parameterTypeChildren!" : term
local macro_rules
  | `(parameterTypeChildren!) =>
      `([.atom (.terminal (.symbol .colon)),
        .atom (.nonterminal .type)])

local syntax "parameterChildren!" : term
local macro_rules
  | `(parameterChildren!) =>
      `([.optional (.atom (.terminal
          (.contextualKeyword .comptimeKw))),
        .atom (.terminal (.category .identifier)),
        .optional (.sequence parameterTypeChildren!)])

local syntax "parameterComptimeValue![" term "]" : term
local macro_rules
  | `(parameterComptimeValue![$comptimeToken:term]) =>
      `(EbnfValue.optional
        (.atom (.terminal (.contextualKeyword .comptimeKw)))
        (($comptimeToken).map fun terminal =>
          EbnfValue.terminalAtom
            (.contextualKeyword .comptimeKw) terminal))

local syntax "parameterTypeValue![" term "]" : term
local macro_rules
  | `(parameterTypeValue![$typeValue:term]) =>
      `(EbnfValue.optional (.sequence parameterTypeChildren!)
        (($typeValue).map fun value =>
          EbnfValue.sequence parameterTypeChildren!
            (EbnfValues.cons _ _
              (EbnfValue.terminalAtom (.symbol .colon) value.1)
              (EbnfValues.cons _ _
                (EbnfValue.ruleAtom .type value.2.1)
                EbnfValues.nil))))

local syntax "parameterRootValue![" term "," term "," term "]" : term
local macro_rules
  | `(parameterRootValue![$comptimeToken:term, $name:term,
      $typeValue:term]) =>
      `(EbnfValue.transport (by rfl)
        (EbnfValue.sequence parameterChildren!
          (EbnfValues.cons _ _
            parameterComptimeValue![$comptimeToken]
            (EbnfValues.cons _ _
              (EbnfValue.terminalAtom (.category .identifier)
                ($name).matched)
              (EbnfValues.cons _ _
                parameterTypeValue![$typeValue]
                EbnfValues.nil)))))

private def parameterComptimePlan
    {file : WorkspaceFile} {tokens : List Token}
    (comptimeToken : Option (MatchedTerminal file tokens
      (.contextualKeyword .comptimeKw))) : TokenPlan :=
  match comptimeToken with
  | none => TokenPlan.empty
  | some terminal => TokenPlan.exact
      (.identifier ContextualKeyword.comptimeKw.spelling) terminal.span

private def parameterPrefixPlan
    {file : WorkspaceFile} {tokens : List Token}
    (comptimeToken : Option (MatchedTerminal file tokens
      (.contextualKeyword .comptimeKw)))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier) : TokenPlan :=
  (parameterComptimePlan comptimeToken).append
    (identifierPlan (RuleReduction.terminalLoc name.matched name.parsed))

private def parameterPhysicalPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (comptimeToken : Option (MatchedTerminal file tokens
      (.contextualKeyword .comptimeKw)))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (typeValue : Option
      (MatchedTerminal file tokens (.symbol .colon) × (TypeExpr × Unit))) :
    Option TokenPlan :=
  match typeValue with
  | none => some (parameterPrefixPlan comptimeToken name)
  | some value => do
      let typePlan ← typeExprPlan? value.2.1
      pure (((parameterPrefixPlan comptimeToken name).append
        (TokenPlan.exact (.symbol .colon) value.1.span)).append typePlan)

private def parameterPlainPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (comptimeToken : Option (MatchedTerminal file tokens
      (.contextualKeyword .comptimeKw)))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (typeValue : Option
      (MatchedTerminal file tokens (.symbol .colon) × (TypeExpr × Unit))) :
    Option TokenPlan :=
  match typeValue with
  | none => some (parameterPrefixPlan comptimeToken name)
  | some value => do
      let typePlan ← typeExprPlan? value.2.1
      pure (((parameterPrefixPlan comptimeToken name).append
        (TokenPlan.plain (.symbol .colon))).append typePlan)

private theorem typeRuleAtom_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (typeExpression : TypeExpr) :
    (EbnfValue.ruleAtom (file := file) (tokens := tokens)
      .type typeExpression).tokenPlan? sourceRuleTokenPlanLayout =
      typeExprPlan? typeExpression := by
  change
    (EbnfValue.ruleAtom (file := file) (tokens := tokens)
      .type typeExpression).tokenPlan? sourceRuleTokenPlanLayout =
      ruleTokenPlan? .type typeExpression
  exact EbnfValue.tokenPlan?_ruleAtom _ _ _

private theorem parameterInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (comptimeToken : Option (MatchedTerminal file tokens
      (.contextualKeyword .comptimeKw)))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (typeValue : Option
      (MatchedTerminal file tokens (.symbol .colon) × (TypeExpr × Unit)))
    (nameProjects : IdentifierProjects name.matched
      name.spelling name.parsed) :
    (parameterRootValue![comptimeToken, name, typeValue]).tokenPlan?
        sourceRuleTokenPlanLayout =
      parameterPhysicalPlan? comptimeToken name typeValue := by
  rw [EbnfValue.tokenPlan?_transport,
    EbnfValue.tokenPlan?_sequence,
    EbnfValues.tokenPlan?_cons,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValues.tokenPlan?_cons,
    EbnfValues.tokenPlan?_nil,
    matchedIdentifier_physicalTokenPlan name nameProjects]
  cases comptimeToken with
  | none =>
      rw [Option.map_none, EbnfValue.tokenPlan?_optional_none]
      cases typeValue with
      | none =>
          rw [Option.map_none, EbnfValue.tokenPlan?_optional_none]
          simp [parameterPhysicalPlan?, parameterPrefixPlan,
            parameterComptimePlan, TokenPlan.append, TokenPlan.empty]
      | some value =>
          rw [Option.map_some, EbnfValue.tokenPlan?_optional_some,
            EbnfValue.tokenPlan?_sequence,
            EbnfValues.tokenPlan?_cons,
            EbnfValue.tokenPlan?_terminalAtom,
            EbnfValues.tokenPlan?_cons,
            typeRuleAtom_tokenPlan? value.2.1,
            EbnfValues.tokenPlan?_nil,
            matchedSymbol_physicalTokenPlan .colon value.1]
          cases typePlanEq : typeExprPlan? value.2.1 with
          | none =>
              simp [typePlanEq, parameterPhysicalPlan?]
          | some typePlan =>
              simp [typePlanEq, parameterPhysicalPlan?,
                parameterPrefixPlan, parameterComptimePlan,
                TokenPlan.append, TokenPlan.empty, List.append_assoc]
  | some terminal =>
      rw [Option.map_some, EbnfValue.tokenPlan?_optional_some,
        EbnfValue.tokenPlan?_terminalAtom,
        matchedContextualKeyword_physicalTokenPlan .comptimeKw terminal]
      cases typeValue with
      | none =>
          rw [Option.map_none, EbnfValue.tokenPlan?_optional_none]
          simp [parameterPhysicalPlan?, parameterPrefixPlan,
            parameterComptimePlan, TokenPlan.append, TokenPlan.empty]
      | some value =>
          rw [Option.map_some, EbnfValue.tokenPlan?_optional_some,
            EbnfValue.tokenPlan?_sequence,
            EbnfValues.tokenPlan?_cons,
            EbnfValue.tokenPlan?_terminalAtom,
            EbnfValues.tokenPlan?_cons,
            typeRuleAtom_tokenPlan? value.2.1,
            EbnfValues.tokenPlan?_nil,
            matchedSymbol_physicalTokenPlan .colon value.1]
          cases typePlanEq : typeExprPlan? value.2.1 with
          | none =>
              simp [typePlanEq, parameterPhysicalPlan?]
          | some typePlan =>
              simp [typePlanEq, parameterPhysicalPlan?,
                parameterPrefixPlan, parameterComptimePlan,
                TokenPlan.append, TokenPlan.empty, List.append_assoc]

private theorem parameterComptimePlan_wellAnchored
    {file : WorkspaceFile} {tokens : List Token}
    (comptimeToken : Option (MatchedTerminal file tokens
      (.contextualKeyword .comptimeKw))) :
    (parameterComptimePlan comptimeToken).WellAnchored := by
  cases comptimeToken with
  | none =>
      exact TokenPlan.WellAnchored.empty
  | some terminal =>
      exact TokenPlan.WellAnchored.exact _ _

private theorem parameterPrefixPlan_wellAnchored
    {file : WorkspaceFile} {tokens : List Token}
    (comptimeToken : Option (MatchedTerminal file tokens
      (.contextualKeyword .comptimeKw)))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier) :
    (parameterPrefixPlan comptimeToken name).WellAnchored := by
  exact TokenPlan.WellAnchored.append
    (parameterComptimePlan_wellAnchored comptimeToken)
    (identifierPlan_wellAnchored
      (RuleReduction.terminalLoc name.matched name.parsed))

private theorem parameterPlainPlan?_wellAnchored
    {file : WorkspaceFile} {tokens : List Token}
    (comptimeToken : Option (MatchedTerminal file tokens
      (.contextualKeyword .comptimeKw)))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (typeValue : Option
      (MatchedTerminal file tokens (.symbol .colon) × (TypeExpr × Unit)))
    (plan : TokenPlan)
    (success : parameterPlainPlan? comptimeToken name typeValue = some plan) :
    plan.WellAnchored := by
  cases typeValue with
  | none =>
      simp [parameterPlainPlan?] at success
      subst plan
      exact parameterPrefixPlan_wellAnchored comptimeToken name
  | some value =>
      simp only [parameterPlainPlan?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨typePlan, typePlanEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact TokenPlan.WellAnchored.append
        (TokenPlan.WellAnchored.append
          (parameterPrefixPlan_wellAnchored comptimeToken name)
          (TokenPlan.WellAnchored.plain _))
        (typeExprPlan?_wellAnchored value.2.1 typePlan typePlanEq)

private theorem parameterPhysicalEvidence_toPlain
    {file : WorkspaceFile} {tokens : List Token}
    (comptimeToken : Option (MatchedTerminal file tokens
      (.contextualKeyword .comptimeKw)))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (typeValue : Option
      (MatchedTerminal file tokens (.symbol .colon) × (TypeExpr × Unit)))
    (actual : List Token)
    (evidence : TokenPlanEvidence
      (parameterPhysicalPlan? comptimeToken name typeValue) actual) :
    TokenPlanEvidence
      (parameterPlainPlan? comptimeToken name typeValue) actual := by
  cases typeValue with
  | none =>
      simpa [parameterPhysicalPlan?, parameterPlainPlan?] using evidence
  | some value =>
      cases typePlanEq : typeExprPlan? value.2.1 with
      | none =>
          simpa [parameterPhysicalPlan?, parameterPlainPlan?, typePlanEq]
            using evidence
      | some typePlan =>
          have exactEvidence : TokenPlanEvidence
              (some (((parameterPrefixPlan comptimeToken name).append
                (TokenPlan.exact (.symbol .colon) value.1.span)).append
                  typePlan)) actual := by
            simpa [parameterPhysicalPlan?, typePlanEq] using evidence
          have plainEvidence := exactEvidence.exactMiddleToPlain
          simpa [parameterPlainPlan?, typePlanEq] using plainEvidence

private theorem ruleTokenPlan?_parameter (parameter : Parameter) :
    ruleTokenPlan? .parameter parameter = parameterTokenPlan? parameter := by
  rfl

private theorem parameterTokenPlan?_sourceLoc
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (comptimeToken : Option (MatchedTerminal file tokens
      (.contextualKeyword .comptimeKw)))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (typeValue : Option
      (MatchedTerminal file tokens (.symbol .colon) × (TypeExpr × Unit)))
    (comptimeProjects : ∀ terminal, comptimeToken = some terminal →
      RuleReduction.MarkerProjects file tokens terminal .comptimeModifier)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    parameterTokenPlan? (sourceLoc witness {
      comptime := match comptimeToken with
        | none => none
        | some terminal => some (RuleReduction.marker terminal
            (comptimeProjects terminal rfl))
      name := RuleReduction.terminalLoc name.matched name.parsed
      type := typeValue.map fun value => value.2.1
    }) = (do
      let innerPlan ← parameterPlainPlan? comptimeToken name typeValue
      pure (TokenPlan.enclose witness.span innerPlan)) := by
  cases comptimeToken with
  | none =>
      cases typeValue with
      | none =>
          simp [parameterTokenPlan?, parameterPlainPlan?,
            parameterPrefixPlan, parameterComptimePlan, sourceLoc]
      | some value =>
          cases typePlanEq : typeExprPlan? value.2.1 with
          | none =>
              simp [typePlanEq, parameterTokenPlan?, parameterPlainPlan?,
                sourceLoc]
          | some typePlan =>
              simp [typePlanEq, parameterTokenPlan?, parameterPlainPlan?,
                parameterPrefixPlan, parameterComptimePlan, sourceLoc,
                TokenPlan.append, TokenPlan.empty, List.append_assoc]
  | some terminal =>
      have projects := comptimeProjects terminal rfl
      cases projects
      cases typeValue with
      | none =>
          simp [parameterTokenPlan?, parameterPlainPlan?,
            parameterPrefixPlan, parameterComptimePlan, sourceLoc,
            RuleReduction.marker, RuleReduction.terminalLoc]
      | some value =>
          cases typePlanEq : typeExprPlan? value.2.1 with
          | none =>
              simp [typePlanEq, parameterTokenPlan?, parameterPlainPlan?,
                sourceLoc, RuleReduction.marker,
                RuleReduction.terminalLoc]
          | some typePlan =>
              simp [typePlanEq, parameterTokenPlan?, parameterPlainPlan?,
                parameterPrefixPlan, parameterComptimePlan,
                sourceLoc, RuleReduction.marker,
                RuleReduction.terminalLoc, TokenPlan.append,
                TokenPlan.empty, List.append_assoc]

theorem parameter_tokenPlanSound : GrammarRuleTokenPlanSound .parameter := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | parameter origin finish comptimeToken name typeValue comptimeProjects
      nameProjects witness =>
      change EbnfValue file tokens (.sequence parameterChildren!) at input
      rw [← inputEq] at inputEvidence
      have candidateEq :
          input.tokenPlan? sourceRuleTokenPlanLayout =
            parameterPhysicalPlan? comptimeToken name typeValue := by
        rw [inputEq]
        exact parameterInput_tokenPlan? comptimeToken name typeValue
          nameProjects
      have physicalEvidence := inputEvidence.candidate_eq candidateEq
      have plainEvidence := parameterPhysicalEvidence_toPlain
        comptimeToken name typeValue _ physicalEvidence
      have enclosed := plainEvidence.enclose
        (fun plan success =>
          parameterPlainPlan?_wellAnchored comptimeToken name typeValue
            plan success)
        witness.consumed
      have enclosureCandidateEq :
          Option.map (TokenPlan.enclose witness.span)
              (parameterPlainPlan? comptimeToken name typeValue) =
            (do
              let innerPlan ←
                parameterPlainPlan? comptimeToken name typeValue
              pure (TokenPlan.enclose witness.span innerPlan)) := by
        cases planEq : parameterPlainPlan? comptimeToken name typeValue <;>
          simp
      apply TokenPlanEvidence.candidate_eq enclosed
      rw [ruleTokenPlan?_parameter]
      rw [enclosureCandidateEq]
      exact (parameterTokenPlan?_sourceLoc comptimeToken name typeValue
        comptimeProjects witness).symm

private theorem statementTokenPlan?_allowsTerminalLocal
    {statement : Statement} {plan : TokenPlan}
    (success : statementTokenPlan? false statement = some plan) :
    statementTokenPlan? true statement = some plan := by
  rcases statement with ⟨span, payload⟩
  cases payload <;> try simp_all only [statementTokenPlan?]
  case expression expression terminator =>
    cases terminator <;> simp_all [statementTokenPlan?]
  case «return» value terminator =>
    cases value <;> simp_all [statementTokenPlan?]
  case «match» scrutinees arms terminator =>
    cases terminator <;> simp_all [statementTokenPlan?]

private theorem statementTokenPlans?_of_mapM
    (statements : List Statement) (plans : List TokenPlan)
    (success : statements.mapM (statementTokenPlan? false) = some plans) :
    statementTokenPlans? statements = some plans := by
  induction statements generalizing plans with
  | nil =>
      simp at success
      subst plans
      simp [statementTokenPlans?]
  | cons head tail induction =>
      cases tail with
      | nil =>
          cases headEq : statementTokenPlan? false head with
          | none => simp [headEq] at success
          | some headPlan =>
              simp [headEq] at success
              subst plans
              have finalEq := statementTokenPlan?_allowsTerminalLocal headEq
              simp [statementTokenPlans?, finalEq]
      | cons second rest =>
          cases headEq : statementTokenPlan? false head with
          | none => simp [headEq] at success
          | some headPlan =>
              cases tailEq : (second :: rest).mapM
                  (statementTokenPlan? false) with
              | none => simp [headEq, tailEq] at success
              | some tailPlans =>
                  simp [headEq, tailEq] at success
                  subst plans
                  have acceptedTail := induction tailPlans tailEq
                  simp [statementTokenPlans?, headEq, acceptedTail]

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

private theorem statementRuleAtomValues_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (statements : List Statement) :
    (statements.map (EbnfValue.ruleAtom (file := file) (tokens := tokens)
      .statement)).mapM
        (fun value => value.tokenPlan? sourceRuleTokenPlanLayout) =
      statements.mapM (statementTokenPlan? false) := by
  change
    (statements.map (EbnfValue.ruleAtom (file := file) (tokens := tokens)
      .statement)).mapM
        (fun value => value.tokenPlan? sourceRuleTokenPlanLayout) =
      statements.mapM (ruleTokenPlan? .statement)
  exact ruleAtomValues_tokenPlan? .statement statements

private theorem bodyInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (statements : List Statement)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace)) :
    (EbnfValue.transport (file := file) (tokens := tokens) (by rfl)
      (EbnfValue.sequence [
        .atom (.terminal (.symbol .leftBrace)),
        .star (.atom (.nonterminal .statement)),
        .atom (.terminal (.symbol .rightBrace))]
        (EbnfValues.cons _ _
          (EbnfValue.terminalAtom (.symbol .leftBrace) openBrace)
          (EbnfValues.cons _ _
            (EbnfValue.star (.atom (.nonterminal .statement))
              (statements.map (EbnfValue.ruleAtom .statement)))
            (EbnfValues.cons _ _
              (EbnfValue.terminalAtom (.symbol .rightBrace) closeBrace)
              EbnfValues.nil))))).tokenPlan? sourceRuleTokenPlanLayout =
      (do
        let statementPlans ←
          statements.mapM (statementTokenPlan? false)
        pure (TokenPlan.concat [
          TokenPlan.exact (.symbol .leftBrace) openBrace.span,
          TokenPlan.concat statementPlans,
          TokenPlan.exact (.symbol .rightBrace) closeBrace.span])) := by
  rw [EbnfValue.tokenPlan?_transport,
    EbnfValue.tokenPlan?_sequence,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_star,
    statementRuleAtomValues_tokenPlan? statements,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValues.tokenPlan?_nil,
    matchedSymbol_physicalTokenPlan .leftBrace openBrace,
    matchedSymbol_physicalTokenPlan .rightBrace closeBrace]
  simp [TokenPlan.concat, TokenPlan.append, TokenPlan.empty]
  cases plansEq : statements.mapM (statementTokenPlan? false) with
  | none =>
      simp
  | some statementPlans =>
      simp

private theorem ruleTokenPlan?_body (body : Body) :
    ruleTokenPlan? .body body = bodyTokenPlan? .braced body := by
  rfl

private theorem bracedBodyTokenPlan?_sourceLoc
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (statements : List Statement)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (statementPlans : List TokenPlan)
    (plansEq : statementTokenPlans? statements = some statementPlans)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    bodyTokenPlan? .braced (sourceLoc witness {
      origin := BodyOrigin.braced openBrace.span closeBrace.span
      statements := statements
    }) = some (TokenPlan.enclose witness.span (TokenPlan.concat [
      TokenPlan.exact (.symbol .leftBrace) openBrace.span,
      TokenPlan.concat statementPlans,
      TokenPlan.exact (.symbol .rightBrace) closeBrace.span])) := by
  unfold bodyTokenPlan?
  simp [sourceLoc]
  rw [plansEq]
  unfold bracedBodyPlanWith?
  rfl

theorem body_tokenPlanSound : GrammarRuleTokenPlanSound .body := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | body origin finish openBrace statements closeBrace witness =>
      change EbnfValue file tokens (.sequence [
        .atom (.terminal (.symbol .leftBrace)),
        .star (.atom (.nonterminal .statement)),
        .atom (.terminal (.symbol .rightBrace))]) at input
      rw [← inputEq] at inputEvidence
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          (do
            let statementPlans ←
              statements.mapM (statementTokenPlan? false)
            pure (TokenPlan.concat [
              TokenPlan.exact (.symbol .leftBrace) openBrace.span,
              TokenPlan.concat statementPlans,
              TokenPlan.exact (.symbol .rightBrace) closeBrace.span])) := by
        rw [inputEq]
        exact bodyInput_tokenPlan? openBrace statements closeBrace
      have physicalEvidence := inputEvidence.candidate_eq candidateEq
      rcases physicalEvidence with ⟨inputPlan, planEq, relation⟩
      cases statementPlansEq :
          statements.mapM (statementTokenPlan? false) with
      | none => simp [statementPlansEq] at planEq
      | some statementPlans =>
          simp [statementPlansEq] at planEq
          subst inputPlan
          have outputPlansEq := statementTokenPlans?_of_mapM
            statements statementPlans statementPlansEq
          have exactEvidence : TokenPlanEvidence
              (some (TokenPlan.concat [
                TokenPlan.exact (.symbol .leftBrace) openBrace.span,
                TokenPlan.concat statementPlans,
                TokenPlan.exact (.symbol .rightBrace) closeBrace.span]))
              (PhysicalTokens tokens origin finish) :=
            ⟨_, rfl, relation⟩
          have enclosed := exactEvidence.enclose
            (fun plan success => by
              injection success with planEq
              subst plan
              exact TokenPlan.WellAnchored.concatExactBookended
                (.symbol .leftBrace) openBrace.span
                (.symbol .rightBrace) closeBrace.span
                [TokenPlan.concat statementPlans])
            witness.consumed
          apply TokenPlanEvidence.candidate_eq enclosed
          rw [ruleTokenPlan?_body]
          exact (bracedBodyTokenPlan?_sourceLoc openBrace statements
            closeBrace statementPlans outputPlansEq witness).symm
