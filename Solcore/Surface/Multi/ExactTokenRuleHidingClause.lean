import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- An identifier projection gives the exact plan retained by its AST node. -/
private theorem identifierPhysicalPlan_eq
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
    · simpa [Identifier.render] using
        congrArg Identifier.text (Option.some.inj parseEq)
    · contradiction
  simp [MatchedTerminal.physicalTokenPlan, valueEq,
    identifierPlan, RuleReduction.terminalLoc, ← spellingEq, payloadEq]

/-- A matched hard keyword retains its fixed payload and checked span. -/
private theorem physicalTokenPlan_hardKeyword
    {file : WorkspaceFile} {tokens : List Token}
    (keyword : HardKeyword)
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

/-- A matched symbol retains its fixed payload and checked span. -/
private theorem physicalTokenPlan_symbol
    {file : WorkspaceFile} {tokens : List Token}
    (symbol : Symbol)
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

/-- Forget the local span constraints on three fixed delimiters while keeping
the complete middle-token relation unchanged. -/
private theorem TokenSlot.ListMatches.threeFixedToPlain
    {firstKind secondKind lastKind : TokenKind}
    {firstSpan secondSpan lastSpan : SourceSpan}
    {middle : TokenPlan} {actual : List Token}
    (relation : TokenSlot.ListMatches
      ((TokenPlan.exact firstKind firstSpan).append
        ((TokenPlan.exact secondKind secondSpan).append
          (middle.append (TokenPlan.exact lastKind lastSpan)))).slots
      actual) :
    TokenSlot.ListMatches
      ((TokenPlan.plain firstKind).append
        ((TokenPlan.plain secondKind).append
          (middle.append (TokenPlan.plain lastKind)))).slots
      actual := by
  change TokenSlot.ListMatches
    (.required (ExpectedToken.exact firstKind firstSpan) ::
      .required (ExpectedToken.exact secondKind secondSpan) ::
      middle.slots ++
        [.required (ExpectedToken.exact lastKind lastSpan)]) actual at relation
  change TokenSlot.ListMatches
    (.required (ExpectedToken.plain firstKind) ::
      .required (ExpectedToken.plain secondKind) ::
      middle.slots ++
        [.required (ExpectedToken.plain lastKind)]) actual
  cases relation with
  | required firstMatch tail =>
      cases tail with
      | required secondMatch rest =>
          rcases rest.split_append with
            ⟨middleActual, lastActual, actualEq,
              middleRelation, lastRelation⟩
          rw [actualEq]
          exact .required firstMatch.toPlain <|
            .required secondMatch.toPlain <|
              middleRelation.append lastRelation.requiredHeadToPlain

/-- The hiding-clause reduction preserves the comma-separated identifier
plans and derives its enclosing span from the consumed parser interval. -/
theorem hidingClause_tokenPlanSound :
    GrammarRuleTokenPlanSound .hidingClause := by
  intro file tokens origin finish input output reduces inputEvidence
  cases reduces with
  | hidingClause origin finish hidingKw openBrace names closeBrace
      nameProjects witness =>
      have namePlanEq : ∀ name ∈ names,
          name.matched.physicalTokenPlan =
            identifierPlan
              (RuleReduction.terminalLoc name.matched name.parsed) := by
        intro name member
        exact identifierPhysicalPlan_eq name
          (nameProjects name member)
      have mappedPlansEq :
          List.mapM (fun name => some name.matched.physicalTokenPlan) names =
            some (names.map fun name => identifierPlan
              (RuleReduction.terminalLoc name.matched name.parsed)) := by
        change List.mapM
          (fun name => (pure name.matched.physicalTokenPlan : Option TokenPlan))
          names = _
        rw [List.mapM_pure]
        exact congrArg some (List.map_congr_left namePlanEq)
      simp only [EbnfValue.tokenPlan?_transport,
        EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_list0,
        EbnfValues.tokenPlan?_nil,
        sourceRuleTokenPlanLayout] at inputEvidence
      simp [Function.comp_def, EbnfValue.tokenPlan?_terminalAtom]
        at inputEvidence
      rw [mappedPlansEq] at inputEvidence
      simp only [Option.bind_some] at inputEvidence
      rcases inputEvidence with ⟨plan, candidateEq, relation⟩
      simp only [Option.some.injEq] at candidateEq
      subst plan
      rw [physicalTokenPlan_hardKeyword,
        physicalTokenPlan_symbol,
        physicalTokenPlan_symbol] at relation
      let namesPlan := TokenPlan.commaSeparated
        (names.map fun name => identifierPlan
          (RuleReduction.terminalLoc name.matched name.parsed))
      have innerRelation : TokenSlot.ListMatches
          ((TokenPlan.plain (.hardKeyword .hidingKw)).append
            ((TokenPlan.plain (.symbol .leftBrace)).append
              (namesPlan.append
                (TokenPlan.plain (.symbol .rightBrace))))).slots
          (PhysicalTokens tokens origin finish) := by
        apply TokenSlot.ListMatches.threeFixedToPlain relation
      let innerPlan :=
        (TokenPlan.plain (.hardKeyword .hidingKw)).append
          ((TokenPlan.plain (.symbol .leftBrace)).append
            (namesPlan.append (TokenPlan.plain (.symbol .rightBrace))))
      have innerAnchored : innerPlan.WellAnchored := by
        dsimp [innerPlan]
        simpa [TokenPlan.concat_cons] using
          TokenPlan.WellAnchored.concatPlainBookended
            (.hardKeyword .hidingKw) (.symbol .rightBrace)
            [TokenPlan.plain (.symbol .leftBrace), namesPlan]
      have enclosed := TokenPlanEvidence.enclose
        (TokenPlanEvidence.some innerRelation)
        (fun plan success => by
          simp only [Option.some.injEq] at success
          subst plan
          exact innerAnchored)
        witness.consumed
      apply enclosed.candidate_eq
      simp only [ruleTokenPlan?]
      unfold hidingClausePlan?
      change some (TokenPlan.enclose witness.span innerPlan) =
        some (TokenPlan.enclose witness.span (TokenPlan.concat [
          TokenPlan.plain (.hardKeyword .hidingKw),
          TokenPlan.plain (.symbol .leftBrace),
          TokenPlan.commaSeparated
            ((names.map fun name =>
              RuleReduction.terminalLoc name.matched name.parsed).map
              identifierPlan),
          TokenPlan.plain (.symbol .rightBrace)]))
      simp [innerPlan, namesPlan, TokenPlan.concat_cons,
        List.map_map, Function.comp_def]

end Solcore.Surface.Multi
