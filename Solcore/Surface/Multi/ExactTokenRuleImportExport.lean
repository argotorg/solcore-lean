import Solcore.Surface.Multi.ExactTokenAnchoring
import Solcore.Surface.Multi.ExactTokenRuleSoundness
import Solcore.Surface.Multi.ExactTokenTypeAnchoring

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
      (Option.some ((beforePlan.append (.exact kind span)).append afterPlan)) actual) :
    TokenPlanEvidence
      (Option.some ((beforePlan.append (.plain kind)).append afterPlan)) actual := by
  rcases evidence with ⟨plan, candidateEq, relation⟩
  simp only [Option.some.injEq] at candidateEq
  subst plan
  rcases TokenSlot.ListMatches.split_append relation with
    ⟨prefixExactActual, suffixActual, actualEq,
      prefixExactRelation, suffixRelation⟩
  rcases TokenSlot.ListMatches.split_append prefixExactRelation with
    ⟨prefixActual, exactActual, prefixExactEq,
      prefixRelation, exactRelation⟩
  have plainRelation :=
    TokenSlot.ListMatches.requiredHeadToPlain exactRelation
  apply TokenPlanEvidence.some
  rw [actualEq, prefixExactEq, List.append_assoc]
  simpa [TokenPlan.append, TokenPlan.exact, TokenPlan.plain,
    ExpectedToken.exact] using
    TokenSlot.ListMatches.append
      (TokenSlot.ListMatches.append prefixRelation plainRelation)
      suffixRelation

private theorem TokenSlot.ListMatches.twoFixedToParens
    {firstSpan lastSpan : SourceSpan}
    {middle : TokenPlan} {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat [
        TokenPlan.exact (.symbol .leftParen) firstSpan,
        middle,
        TokenPlan.exact (.symbol .rightParen) lastSpan]).slots actual) :
    TokenSlot.ListMatches (TokenPlan.parens middle).slots actual := by
  change TokenSlot.ListMatches
    (.required (ExpectedToken.exact (.symbol .leftParen) firstSpan) ::
      middle.slots ++
        [.required (ExpectedToken.exact (.symbol .rightParen) lastSpan)])
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

private theorem constructorSelectionPlan?_anchored
    (selection : ConstructorSelection) (plan : TokenPlan)
    (success : constructorSelectionPlan? selection = some plan) :
    plan.WellAnchored := by
  cases payloadEq : selection.payload with
  | all marker =>
      rw [constructorSelectionPlan?, payloadEq] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨starPlan, starPlanEq, resultEq⟩
      change (if marker.payload = .wildcard then
          some (TokenPlan.exact (.symbol .star) marker.span) else none) =
        some starPlan at starPlanEq
      split at starPlanEq
      · injection starPlanEq with starPlanValueEq
        subst starPlan
        injection resultEq with planEq
        subst plan
        apply TokenPlan.WellAnchored.enclose
        change (TokenPlan.concat [
          TokenPlan.plain (.symbol .leftParen),
          TokenPlan.exact (.symbol .star) marker.span,
          TokenPlan.plain (.symbol .rightParen)]).WellAnchored
        exact TokenPlan.WellAnchored.concatPlainBookended
          (.symbol .leftParen) (.symbol .rightParen)
          [TokenPlan.exact (.symbol .star) marker.span]
      · contradiction
  | named constructors =>
      rw [constructorSelectionPlan?, payloadEq] at success
      dsimp at success
      injection success with planEq
      subst plan
      change (TokenPlan.enclose selection.span
        (TokenPlan.parens (TokenPlan.commaSeparated
          (identifierPlan constructors.head ::
            constructors.tail.map identifierPlan)))).WellAnchored
      apply TokenPlan.WellAnchored.enclose
      change (TokenPlan.concat [
        TokenPlan.plain (.symbol .leftParen),
        TokenPlan.commaSeparated
          (identifierPlan constructors.head ::
            constructors.tail.map identifierPlan),
        TokenPlan.plain (.symbol .rightParen)]).WellAnchored
      exact TokenPlan.WellAnchored.concatPlainBookended
        (.symbol .leftParen) (.symbol .rightParen)
        [TokenPlan.commaSeparated
          (identifierPlan constructors.head ::
            constructors.tail.map identifierPlan)]

private theorem exportItemPlan?_anchored
    (item : ExportItem) (plan : TokenPlan)
    (success : exportItemPlan? item = some plan) :
    plan.WellAnchored := by
  cases selectionEq : item.payload.constructors with
  | none =>
      rw [exportItemPlan?, selectionEq] at success
      dsimp at success
      injection success with planEq
      subst plan
      apply TokenPlan.WellAnchored.enclose
      simpa using TokenPlan.WellAnchored.append
        (identifierPlan_wellAnchored item.payload.name)
        TokenPlan.WellAnchored.empty
  | some selection =>
      rw [exportItemPlan?, selectionEq] at success
      have decomposed := Option.bind_eq_some_iff.mp success
      rcases decomposed with ⟨selectionPlan, selectionPlanEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      apply TokenPlan.WellAnchored.enclose
      exact TokenPlan.WellAnchored.append
        (identifierPlan_wellAnchored item.payload.name)
        (constructorSelectionPlan?_anchored selection selectionPlan
          selectionPlanEq)

private theorem moduleReferencePlan?_anchored
    (reference : ModuleReference) (plan : TokenPlan)
    (success : moduleReferencePlan? reference = some plan) :
    plan.WellAnchored := by
  cases payloadEq : reference.payload with
  | relative components =>
      by_cases shapeEq : relativeModuleReferenceShapeExactBool components
      · simp [moduleReferencePlan?, payloadEq, shapeEq] at success
        subst plan
        apply TokenPlan.WellAnchored.enclose
        apply TokenPlan.WellAnchored.append
        · exact pathComponentPlan_wellAnchored components.head
        · apply TokenPlan.WellAnchored.concat
          intro combined member
          simp only [List.mem_map] at member
          rcases member with ⟨component, _member, rfl⟩
          exact TokenPlan.WellAnchored.append
            (TokenPlan.WellAnchored.plain (.symbol .dot))
            (pathComponentPlan_wellAnchored component)
      · simp [moduleReferencePlan?, payloadEq, shapeEq] at success
  | libraryRoot marker tail =>
      by_cases roleEq : marker.payload = .libraryRoot
      · simp [moduleReferencePlan?, payloadEq, roleEq] at success

        subst plan
        apply TokenPlan.WellAnchored.enclose
        apply TokenPlan.WellAnchored.append
        · exact TokenPlan.WellAnchored.exact _ _
        · apply TokenPlan.WellAnchored.append
          · exact TokenPlan.WellAnchored.plain _
          · apply TokenPlan.WellAnchored.append
            · exact pathComponentPlan_wellAnchored tail.head
            · apply TokenPlan.WellAnchored.concat
              intro combined combinedMember
              simp only [List.mem_map] at combinedMember
              rcases combinedMember with ⟨path, _pathMember, rfl⟩
              exact TokenPlan.WellAnchored.append
                (TokenPlan.WellAnchored.plain (.symbol .dot))
                (pathComponentPlan_wellAnchored path)
      · simp [moduleReferencePlan?, payloadEq, roleEq] at success
  | standard marker tail =>
      by_cases roleEq : marker.payload = .standardRoot
      · simp [moduleReferencePlan?, payloadEq, roleEq] at success
        subst plan
        apply TokenPlan.WellAnchored.enclose
        apply TokenPlan.WellAnchored.append
        · exact TokenPlan.WellAnchored.exact _ _
        · apply TokenPlan.WellAnchored.concat
          intro combined member
          simp only [List.mem_map] at member
          rcases member with ⟨component, _member, rfl⟩
          exact TokenPlan.WellAnchored.append
            (TokenPlan.WellAnchored.plain (.symbol .dot))
            (pathComponentPlan_wellAnchored component)
      · simp [moduleReferencePlan?, payloadEq, roleEq] at success
  | external marker library tail =>
      by_cases roleEq : marker.payload = .externalSigil
      · simp [moduleReferencePlan?, payloadEq, roleEq] at success
        subst plan
        apply TokenPlan.WellAnchored.enclose
        apply TokenPlan.WellAnchored.append
        · exact TokenPlan.WellAnchored.exact _ _
        · apply TokenPlan.WellAnchored.append
          · exact externalLibraryPlan_wellAnchored library
          · apply TokenPlan.WellAnchored.append
            · exact TokenPlan.WellAnchored.plain _
            · apply TokenPlan.WellAnchored.append
              · exact pathComponentPlan_wellAnchored tail.head
              · apply TokenPlan.WellAnchored.concat
                intro combined combinedMember
                simp only [List.mem_map] at combinedMember
                rcases combinedMember with ⟨path, _pathMember, rfl⟩
                exact TokenPlan.WellAnchored.append
                  (TokenPlan.WellAnchored.plain (.symbol .dot))
                  (pathComponentPlan_wellAnchored path)
      · simp [moduleReferencePlan?, payloadEq, roleEq] at success

private theorem ruleTokenPlan?_localExportEntry (entry : ExportEntry) :
    ruleTokenPlan? .localExportEntry entry = localExportEntryPlan? entry := by
  rfl

private abbrev localExportEntrySourceBranches : List EbnfExpr := [
  .atom (.terminal (.symbol .star)),
  .atom (.nonterminal .exportItem),
  .sequence [
    .atom (.nonterminal .moduleRef),
    .atom (.terminal (.symbol .dot)),
    .atom (.terminal (.symbol .star))]
]

private abbrev localExportEntryChoiceView
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens (m2cV1.rhs .localExportEntry)) :=
  EbnfValue.choiceView localExportEntrySourceBranches input

private theorem EbnfValue.choiceView_choice_local
    {file : WorkspaceFile} {tokens : List Token}
    (branches : List EbnfExpr)
    (value : (branch : Fin branches.length) ×
      EbnfValue file tokens (branches.get branch)) :
    EbnfValue.choiceView branches (EbnfValue.choice branches value) =
      value := by
  simp [EbnfValue.choiceView, EbnfValue.choice, cast_cast]

private theorem localExportEntryInput_tokenPlan?_choiceView
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout)
    (input : EbnfValue file tokens (m2cV1.rhs .localExportEntry)) :
    input.tokenPlan? layout =
      (localExportEntryChoiceView input).2.tokenPlan? layout := by
  calc
    input.tokenPlan? layout =
        (EbnfValue.choice localExportEntrySourceBranches
          (localExportEntryChoiceView input)).tokenPlan? layout := by
      rw [EbnfValue.choice_of_view localExportEntrySourceBranches input]
      rfl
    _ = (localExportEntryChoiceView input).2.tokenPlan? layout :=
      EbnfValue.tokenPlan?_choice layout localExportEntrySourceBranches _

private theorem localExportEntryItemInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (item : ExportItem) :
    (EbnfValue.transport (file := file) (tokens := tokens) (by rfl)
      (EbnfValue.choice [
        .atom (.terminal (.symbol .star)),
        .atom (.nonterminal .exportItem),
        .sequence [
          .atom (.nonterminal .moduleRef),
          .atom (.terminal (.symbol .dot)),
          .atom (.terminal (.symbol .star))]]
        ⟨⟨1, by decide⟩,
          EbnfValue.ruleAtom .exportItem item⟩)).tokenPlan?
        sourceRuleTokenPlanLayout = exportItemPlan? item := by
  calc
    _ = (EbnfValue.choice [
          .atom (.terminal (.symbol .star)),
          .atom (.nonterminal .exportItem),
          .sequence [
            .atom (.nonterminal .moduleRef),
            .atom (.terminal (.symbol .dot)),
            .atom (.terminal (.symbol .star))]]
          ⟨⟨1, by decide⟩,
            EbnfValue.ruleAtom .exportItem item⟩).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
    _ = (EbnfValue.ruleAtom (file := file) (tokens := tokens)
          .exportItem item).tokenPlan? sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = exportItemPlan? item := by
      rw [EbnfValue.tokenPlan?_ruleAtom]
      rfl

private theorem localExportEntryWildcardInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (star : MatchedTerminal file tokens (.symbol .star)) :
    (EbnfValue.transport (file := file) (tokens := tokens) (by rfl)
      (EbnfValue.choice [
        .atom (.terminal (.symbol .star)),
        .atom (.nonterminal .exportItem),
        .sequence [
          .atom (.nonterminal .moduleRef),
          .atom (.terminal (.symbol .dot)),
          .atom (.terminal (.symbol .star))]]
        ⟨⟨0, by decide⟩,
          EbnfValue.terminalAtom (.symbol .star) star⟩)).tokenPlan?
        sourceRuleTokenPlanLayout =
      some (TokenPlan.exact (.symbol .star) star.span) := by
  calc
    _ = (EbnfValue.choice [
          .atom (.terminal (.symbol .star)),
          .atom (.nonterminal .exportItem),
          .sequence [
            .atom (.nonterminal .moduleRef),
            .atom (.terminal (.symbol .dot)),
            .atom (.terminal (.symbol .star))]]
          ⟨⟨0, by decide⟩,
            EbnfValue.terminalAtom (.symbol .star) star⟩).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
    _ = (EbnfValue.terminalAtom
          (.symbol .star) star).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = some (TokenPlan.exact (.symbol .star) star.span) := by
      rw [EbnfValue.tokenPlan?_terminalAtom,
        matchedSymbol_physicalTokenPlan]

private theorem localExportEntryAllFromInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (star : MatchedTerminal file tokens (.symbol .star)) :
    (EbnfValue.transport (file := file) (tokens := tokens) (by rfl)
      (EbnfValue.choice [
        .atom (.terminal (.symbol .star)),
        .atom (.nonterminal .exportItem),
        .sequence [
          .atom (.nonterminal .moduleRef),
          .atom (.terminal (.symbol .dot)),
          .atom (.terminal (.symbol .star))]]
        ⟨⟨2, by decide⟩,
          EbnfValue.sequence
            [
              .atom (.nonterminal .moduleRef),
              .atom (.terminal (.symbol .dot)),
              .atom (.terminal (.symbol .star))]
            (EbnfValues.cons _ _
              (EbnfValue.ruleAtom .moduleRef reference)
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom (.symbol .dot) dot)
                (EbnfValues.cons _ _
                  (EbnfValue.terminalAtom (.symbol .star) star)
                  EbnfValues.nil)))⟩)).tokenPlan?
        sourceRuleTokenPlanLayout =
      (do
        let referencePlan ← moduleReferencePlan? reference
        pure ((referencePlan.append
          (TokenPlan.exact (.symbol .dot) dot.span)).append
          (TokenPlan.exact (.symbol .star) star.span))) := by
  calc
    _ = (EbnfValue.choice [
          .atom (.terminal (.symbol .star)),
          .atom (.nonterminal .exportItem),
          .sequence [
            .atom (.nonterminal .moduleRef),
            .atom (.terminal (.symbol .dot)),
            .atom (.terminal (.symbol .star))]]
          ⟨⟨2, by decide⟩,
            EbnfValue.sequence
              [
                .atom (.nonterminal .moduleRef),
                .atom (.terminal (.symbol .dot)),
                .atom (.terminal (.symbol .star))]
              (EbnfValues.cons _ _
                (EbnfValue.ruleAtom .moduleRef reference)
                (EbnfValues.cons _ _
                  (EbnfValue.terminalAtom (.symbol .dot) dot)
                  (EbnfValues.cons _ _
                    (EbnfValue.terminalAtom (.symbol .star) star)
                    EbnfValues.nil)))⟩).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
    _ = (EbnfValue.sequence
          [
            .atom (.nonterminal .moduleRef),
            .atom (.terminal (.symbol .dot)),
            .atom (.terminal (.symbol .star))]
          (EbnfValues.cons _ _
            (EbnfValue.ruleAtom .moduleRef reference)
            (EbnfValues.cons _ _
              (EbnfValue.terminalAtom (.symbol .dot) dot)
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom (.symbol .star) star)
                EbnfValues.nil)))).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = _ := by
      rw [EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValues.tokenPlan?_nil,
        matchedSymbol_physicalTokenPlan (.dot) dot,
        matchedSymbol_physicalTokenPlan (.star) star]
      simp [sourceRuleTokenPlanLayout, ruleTokenPlan?,
        TokenPlan.append_assoc]

theorem localExportEntry_tokenPlanSound :
    GrammarRuleTokenPlanSound .localExportEntry := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | localExportEntryItem origin finish item witness =>
      change EbnfValue file tokens
        (.choice localExportEntrySourceBranches) at input
      rw [← inputEq] at inputEvidence
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          exportItemPlan? item := by
        rw [inputEq]
        exact localExportEntryItemInput_tokenPlan? item
      have innerEvidence := inputEvidence.candidate_eq candidateEq
      have enclosed := innerEvidence.enclose
        (fun plan success => exportItemPlan?_anchored item plan success)
        witness.consumed
      apply TokenPlanEvidence.candidate_eq enclosed
      cases candidateEq : exportItemPlan? item <;>
        simp [candidateEq, ruleTokenPlan?, localExportEntryPlan?, sourceLoc]
  | localExportEntryWildcard origin finish star starMarker witness =>
      change EbnfValue file tokens
        (.choice localExportEntrySourceBranches) at input
      rw [← inputEq] at inputEvidence
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          some (TokenPlan.exact (.symbol .star) star.span) := by
        rw [inputEq]
        exact localExportEntryWildcardInput_tokenPlan? star
      have innerEvidence := inputEvidence.candidate_eq candidateEq
      have enclosed := innerEvidence.enclose
        (fun plan success => by
          injection success with planEq
          subst plan
          exact TokenPlan.WellAnchored.exact _ _)
        witness.consumed
      apply TokenPlanEvidence.candidate_eq enclosed
      change some (TokenPlan.enclose witness.span
        (TokenPlan.exact (.symbol .star) star.span)) = _
      rfl
  | localExportEntryAllFrom origin finish reference dot star starMarker witness =>
      change EbnfValue file tokens
        (.choice localExportEntrySourceBranches) at input
      rw [← inputEq] at inputEvidence
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          (do
            let referencePlan ← moduleReferencePlan? reference
            pure ((referencePlan.append
              (TokenPlan.exact (.symbol .dot) dot.span)).append
              (TokenPlan.exact (.symbol .star) star.span))) := by
        rw [inputEq]
        exact localExportEntryAllFromInput_tokenPlan?
          reference dot star
      have exactInputEvidence := inputEvidence.candidate_eq candidateEq
      rcases exactInputEvidence with ⟨inputPlan, planEq, relation⟩
      cases referenceEq : moduleReferencePlan? reference with
      | none => simp [referenceEq] at planEq
      | some referencePlan =>
          simp [referenceEq] at planEq
          subst inputPlan
          have exactEvidence : TokenPlanEvidence
              (some ((referencePlan.append
                (TokenPlan.exact (.symbol .dot) dot.span)).append
                (TokenPlan.exact (.symbol .star) star.span)))
              (PhysicalTokens tokens origin finish) := by
            exact ⟨_, rfl, relation⟩
          have innerEvidence := exactEvidence.exactMiddleToPlain
          have enclosed := innerEvidence.enclose
            (fun plan success => by
              injection success with planEq
              subst plan
              apply TokenPlan.WellAnchored.append
              · exact TokenPlan.WellAnchored.append
                  (moduleReferencePlan?_anchored reference
                    referencePlan referenceEq)
                  (TokenPlan.WellAnchored.plain _)
              · exact TokenPlan.WellAnchored.exact _ _)
            witness.consumed
          have outputEq :
              ruleTokenPlan? .localExportEntry
                (sourceLoc witness (.allFrom reference
                  (RuleReduction.marker star starMarker))) =
              some (TokenPlan.enclose witness.span
                (referencePlan.append
                  ((TokenPlan.plain (.symbol .dot)).append
                    (TokenPlan.exact (.symbol .star) star.span)))) := by
            rw [ruleTokenPlan?_localExportEntry]
            simp [localExportEntryPlan?, sourceLoc,
              RuleReduction.marker, RuleReduction.terminalLoc, referenceEq]
            rfl
          apply TokenPlanEvidence.candidate_eq enclosed
          rw [outputEq]
          simp only [Option.map_some, Option.some.injEq]
          rw [TokenPlan.append_assoc]

private abbrev remoteExportEntrySourceBranches : List EbnfExpr := [
  .atom (.terminal (.symbol .star)),
  .atom (.nonterminal .exportItem)
]

private theorem remoteExportEntryWildcardInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (star : MatchedTerminal file tokens (.symbol .star)) :
    (EbnfValue.transport (file := file) (tokens := tokens) (by rfl)
      (EbnfValue.choice [
        .atom (.terminal (.symbol .star)),
        .atom (.nonterminal .exportItem)]
        ⟨⟨0, by decide⟩,
          EbnfValue.terminalAtom (.symbol .star) star⟩)).tokenPlan?
        sourceRuleTokenPlanLayout =
      some (TokenPlan.exact (.symbol .star) star.span) := by
  calc
    _ = (EbnfValue.choice [
          .atom (.terminal (.symbol .star)),
          .atom (.nonterminal .exportItem)]
          ⟨⟨0, by decide⟩,
            EbnfValue.terminalAtom (.symbol .star) star⟩).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
    _ = (EbnfValue.terminalAtom
          (.symbol .star) star).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = some (TokenPlan.exact (.symbol .star) star.span) := by
      rw [EbnfValue.tokenPlan?_terminalAtom,
        matchedSymbol_physicalTokenPlan]

private theorem remoteExportEntryItemInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (item : ExportItem) :
    (EbnfValue.transport (file := file) (tokens := tokens) (by rfl)
      (EbnfValue.choice [
        .atom (.terminal (.symbol .star)),
        .atom (.nonterminal .exportItem)]
        ⟨⟨1, by decide⟩,
          EbnfValue.ruleAtom .exportItem item⟩)).tokenPlan?
        sourceRuleTokenPlanLayout = exportItemPlan? item := by
  calc
    _ = (EbnfValue.choice [
          .atom (.terminal (.symbol .star)),
          .atom (.nonterminal .exportItem)]
          ⟨⟨1, by decide⟩,
            EbnfValue.ruleAtom .exportItem item⟩).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
    _ = (EbnfValue.ruleAtom (file := file) (tokens := tokens)
          .exportItem item).tokenPlan? sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = exportItemPlan? item := by
      rw [EbnfValue.tokenPlan?_ruleAtom]
      rfl

private theorem ruleTokenPlan?_remoteExportEntry
    (entry : RemoteExportEntry) :
    ruleTokenPlan? .remoteExportEntry entry =
      remoteExportEntryPlan? entry := by
  rfl

theorem remoteExportEntry_tokenPlanSound :
    GrammarRuleTokenPlanSound .remoteExportEntry := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | remoteExportEntryWildcard origin finish star starMarker witness =>
      change EbnfValue file tokens
        (.choice remoteExportEntrySourceBranches) at input
      rw [← inputEq] at inputEvidence
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          some (TokenPlan.exact (.symbol .star) star.span) := by
        rw [inputEq]
        exact remoteExportEntryWildcardInput_tokenPlan? star
      have innerEvidence := inputEvidence.candidate_eq candidateEq
      have enclosed := innerEvidence.enclose
        (fun plan success => by
          injection success with planEq
          subst plan
          exact TokenPlan.WellAnchored.exact _ _)
        witness.consumed
      apply TokenPlanEvidence.candidate_eq enclosed
      change some (TokenPlan.enclose witness.span
        (TokenPlan.exact (.symbol .star) star.span)) = _
      rfl
  | remoteExportEntryItem origin finish item witness =>
      change EbnfValue file tokens
        (.choice remoteExportEntrySourceBranches) at input
      rw [← inputEq] at inputEvidence
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          exportItemPlan? item := by
        rw [inputEq]
        exact remoteExportEntryItemInput_tokenPlan? item
      have innerEvidence := inputEvidence.candidate_eq candidateEq
      have enclosed := innerEvidence.enclose
        (fun plan success => exportItemPlan?_anchored item plan success)
        witness.consumed
      apply TokenPlanEvidence.candidate_eq enclosed
      cases itemEq : exportItemPlan? item <;>
        simp [itemEq, ruleTokenPlan?_remoteExportEntry,
          remoteExportEntryPlan?, sourceLoc]

private theorem exportItemNoneInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (nameProjects : IdentifierProjects name.matched
      name.spelling name.parsed) :
    (EbnfValue.transport (file := file) (tokens := tokens) (by rfl)
      (EbnfValue.sequence [
        .atom (.terminal (.category .identifier)),
        .optional (.atom (.nonterminal .constructorSelection))]
        (EbnfValues.cons _ _
          (EbnfValue.terminalAtom (.category .identifier) name.matched)
          (EbnfValues.cons _ _
            (EbnfValue.optional
              (.atom (.nonterminal .constructorSelection))
              none)
            EbnfValues.nil)))).tokenPlan? sourceRuleTokenPlanLayout =
      some (identifierPlan
        (RuleReduction.terminalLoc name.matched name.parsed)) := by
  simp only [EbnfValue.tokenPlan?_transport,
    EbnfValue.tokenPlan?_sequence,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValue.tokenPlan?_optional_none,
    EbnfValues.tokenPlan?_nil]
  rw [matchedIdentifier_physicalTokenPlan name nameProjects]
  exact congrArg some (TokenPlan.append_empty _)

private theorem exportItemSomeInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (selection : ConstructorSelection)
    (nameProjects : IdentifierProjects name.matched
      name.spelling name.parsed) :
    (EbnfValue.transport (file := file) (tokens := tokens) (by rfl)
      (EbnfValue.sequence [
        .atom (.terminal (.category .identifier)),
        .optional (.atom (.nonterminal .constructorSelection))]
        (EbnfValues.cons _ _
          (EbnfValue.terminalAtom (.category .identifier) name.matched)
          (EbnfValues.cons _ _
            (EbnfValue.optional
              (.atom (.nonterminal .constructorSelection))
              (some (EbnfValue.ruleAtom
                .constructorSelection selection)))
            EbnfValues.nil)))).tokenPlan? sourceRuleTokenPlanLayout =
      (do
        let selectionPlan ← constructorSelectionPlan? selection
        pure ((identifierPlan
          (RuleReduction.terminalLoc name.matched name.parsed)).append
            selectionPlan)) := by
  simp only [EbnfValue.tokenPlan?_transport,
    EbnfValue.tokenPlan?_sequence,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValue.tokenPlan?_optional_some,
    EbnfValue.tokenPlan?_ruleAtom,
    EbnfValues.tokenPlan?_nil]
  rw [matchedIdentifier_physicalTokenPlan name nameProjects]
  rw [show sourceRuleTokenPlanLayout.plan?
    .constructorSelection selection =
      constructorSelectionPlan? selection by rfl]
  simp

private theorem ruleTokenPlan?_exportItem (item : ExportItem) :
    ruleTokenPlan? .exportItem item = exportItemPlan? item := by
  rfl

private theorem exportItemPlan?_sourceLoc_none
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (name : IdentifierOccurrence)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    exportItemPlan? (sourceLoc witness {
      name := name
      constructors := none
    }) = some (TokenPlan.enclose witness.span (identifierPlan name)) := by
  unfold exportItemPlan?
  change (some TokenPlan.empty).bind (fun constructors =>
    some (TokenPlan.enclose witness.span
      ((identifierPlan name).append constructors))) = _
  simp

private theorem exportItemPlan?_sourceLoc_some
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (name : IdentifierOccurrence) (selection : ConstructorSelection)
    (selectionPlan : TokenPlan)
    (selectionEq : constructorSelectionPlan? selection =
      some selectionPlan)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    exportItemPlan? (sourceLoc witness {
      name := name
      constructors := some selection
    }) = some (TokenPlan.enclose witness.span
      ((identifierPlan name).append selectionPlan)) := by
  unfold exportItemPlan?
  change (constructorSelectionPlan? selection).bind
    (fun constructors => some (TokenPlan.enclose witness.span
      ((identifierPlan name).append constructors))) = _
  rw [selectionEq]
  rfl

theorem exportItem_tokenPlanSound :
    GrammarRuleTokenPlanSound .exportItem := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | exportItem origin finish name selection nameProjects witness =>
      change EbnfValue file tokens (.sequence [
        .atom (.terminal (.category .identifier)),
        .optional (.atom (.nonterminal .constructorSelection))]) at input
      rw [← inputEq] at inputEvidence
      let nameLoc := RuleReduction.terminalLoc name.matched name.parsed
      cases selection with
      | none =>
          have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
              some (identifierPlan nameLoc) := by
            rw [inputEq]
            exact exportItemNoneInput_tokenPlan? name nameProjects
          have innerEvidence := inputEvidence.candidate_eq candidateEq
          have enclosed := innerEvidence.enclose
            (fun plan success => by
              injection success with planEq
              subst plan
              exact identifierPlan_wellAnchored nameLoc)
            witness.consumed
          apply TokenPlanEvidence.candidate_eq enclosed
          rw [ruleTokenPlan?_exportItem]
          exact exportItemPlan?_sourceLoc_none nameLoc witness
      | some selection =>
          have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
              (do
                let selectionPlan ←
                  constructorSelectionPlan? selection
                pure ((identifierPlan nameLoc).append selectionPlan)) := by
            rw [inputEq]
            exact exportItemSomeInput_tokenPlan?
              name selection nameProjects
          have innerEvidence := inputEvidence.candidate_eq candidateEq
          rcases innerEvidence with ⟨inputPlan, planEq, relation⟩
          cases selectionEq : constructorSelectionPlan? selection with
          | none => simp [selectionEq] at planEq
          | some selectionPlan =>
              simp [selectionEq] at planEq
              subst inputPlan
              have exactEvidence : TokenPlanEvidence
                  (some ((identifierPlan nameLoc).append selectionPlan))
                  (PhysicalTokens tokens origin finish) :=
                ⟨_, rfl, relation⟩
              have enclosed := exactEvidence.enclose
                (fun plan success => by
                  injection success with planEq
                  subst plan
                  exact TokenPlan.WellAnchored.append
                    (identifierPlan_wellAnchored nameLoc)
                    (constructorSelectionPlan?_anchored selection
                      selectionPlan selectionEq))
                witness.consumed
              apply TokenPlanEvidence.candidate_eq enclosed
              rw [ruleTokenPlan?_exportItem]
              simpa using (exportItemPlan?_sourceLoc_some
                nameLoc selection selectionPlan selectionEq witness).symm

private abbrev constructorSelectionSourceBranches : List EbnfExpr := [
  .sequence [
    .atom (.terminal (.symbol .leftParen)),
    .atom (.terminal (.symbol .star)),
    .atom (.terminal (.symbol .rightParen))],
  .sequence [
    .atom (.terminal (.symbol .leftParen)),
    .list1 (.atom (.terminal (.category .identifier))),
    .atom (.terminal (.symbol .rightParen))]
]

private theorem constructorSelectionAllInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (star : MatchedTerminal file tokens (.symbol .star))
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen)) :
    (EbnfValue.transport (file := file) (tokens := tokens) (by rfl)
      (EbnfValue.choice [
        .sequence [
          .atom (.terminal (.symbol .leftParen)),
          .atom (.terminal (.symbol .star)),
          .atom (.terminal (.symbol .rightParen))],
        .sequence [
          .atom (.terminal (.symbol .leftParen)),
          .list1 (.atom (.terminal (.category .identifier))),
          .atom (.terminal (.symbol .rightParen))]]
        ⟨⟨0, by decide⟩,
          EbnfValue.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .atom (.terminal (.symbol .star)),
            .atom (.terminal (.symbol .rightParen))]
            (EbnfValues.cons _ _
              (EbnfValue.terminalAtom
                (.symbol .leftParen) openParen)
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom (.symbol .star) star)
                (EbnfValues.cons _ _
                  (EbnfValue.terminalAtom
                    (.symbol .rightParen) closeParen)
                  EbnfValues.nil)))⟩)).tokenPlan?
        sourceRuleTokenPlanLayout =
      some (TokenPlan.concat [
        TokenPlan.exact (.symbol .leftParen) openParen.span,
        TokenPlan.exact (.symbol .star) star.span,
        TokenPlan.exact (.symbol .rightParen) closeParen.span]) := by
  calc
    _ = (EbnfValue.choice [
          .sequence [
            .atom (.terminal (.symbol .leftParen)),
            .atom (.terminal (.symbol .star)),
            .atom (.terminal (.symbol .rightParen))],
          .sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.terminal (.category .identifier))),
            .atom (.terminal (.symbol .rightParen))]]
          ⟨⟨0, by decide⟩,
            EbnfValue.sequence [
              .atom (.terminal (.symbol .leftParen)),
              .atom (.terminal (.symbol .star)),
              .atom (.terminal (.symbol .rightParen))]
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom
                  (.symbol .leftParen) openParen)
                (EbnfValues.cons _ _
                  (EbnfValue.terminalAtom (.symbol .star) star)
                  (EbnfValues.cons _ _
                    (EbnfValue.terminalAtom
                      (.symbol .rightParen) closeParen)
                    EbnfValues.nil)))⟩).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
    _ = (EbnfValue.sequence [
          .atom (.terminal (.symbol .leftParen)),
          .atom (.terminal (.symbol .star)),
          .atom (.terminal (.symbol .rightParen))]
          (EbnfValues.cons _ _
            (EbnfValue.terminalAtom (.symbol .leftParen) openParen)
            (EbnfValues.cons _ _
              (EbnfValue.terminalAtom (.symbol .star) star)
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom
                  (.symbol .rightParen) closeParen)
                EbnfValues.nil)))).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = _ := by
      rw [EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValues.tokenPlan?_nil,
        matchedSymbol_physicalTokenPlan (.leftParen) openParen,
        matchedSymbol_physicalTokenPlan (.star) star,
        matchedSymbol_physicalTokenPlan (.rightParen) closeParen]
      simp [TokenPlan.append]

private theorem constructorSelectionNamedInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (names : NonemptyList (RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier))
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (headProjects : IdentifierProjects names.head.matched
      names.head.spelling names.head.parsed)
    (tailProjects : ∀ name, name ∈ names.tail →
      IdentifierProjects name.matched name.spelling name.parsed) :
    (EbnfValue.transport (file := file) (tokens := tokens) (by rfl)
      (EbnfValue.choice [
        .sequence [
          .atom (.terminal (.symbol .leftParen)),
          .atom (.terminal (.symbol .star)),
          .atom (.terminal (.symbol .rightParen))],
        .sequence [
          .atom (.terminal (.symbol .leftParen)),
          .list1 (.atom (.terminal (.category .identifier))),
          .atom (.terminal (.symbol .rightParen))]]
        ⟨⟨1, by decide⟩,
          EbnfValue.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.terminal (.category .identifier))),
            .atom (.terminal (.symbol .rightParen))]
            (EbnfValues.cons _ _
              (EbnfValue.terminalAtom
                (.symbol .leftParen) openParen)
              (EbnfValues.cons _ _
                (EbnfValue.list1
                  (.atom (.terminal (.category .identifier))) {
                    head := EbnfValue.terminalAtom
                      (.category .identifier) names.head.matched
                    tail := names.tail.map fun name =>
                      EbnfValue.terminalAtom
                        (.category .identifier) name.matched
                  })
                (EbnfValues.cons _ _
                  (EbnfValue.terminalAtom
                    (.symbol .rightParen) closeParen)
                  EbnfValues.nil)))⟩)).tokenPlan?
        sourceRuleTokenPlanLayout =
      some (TokenPlan.concat [
        TokenPlan.exact (.symbol .leftParen) openParen.span,
        TokenPlan.commaSeparated
          (identifierPlan
              (RuleReduction.terminalLoc names.head.matched
                names.head.parsed) ::
            names.tail.map fun name => identifierPlan
              (RuleReduction.terminalLoc name.matched name.parsed)),
        TokenPlan.exact (.symbol .rightParen) closeParen.span]) := by
  have tailPlanEq : ∀ name ∈ names.tail,
      name.matched.physicalTokenPlan = identifierPlan
        (RuleReduction.terminalLoc name.matched name.parsed) := by
    intro name member
    exact matchedIdentifier_physicalTokenPlan name
      (tailProjects name member)
  have mappedPlansEq :
      List.mapM (fun name => some name.matched.physicalTokenPlan)
          names.tail =
        some (names.tail.map fun name => identifierPlan
          (RuleReduction.terminalLoc name.matched name.parsed)) := by
    change List.mapM
      (fun name => (pure name.matched.physicalTokenPlan : Option TokenPlan))
      names.tail = _
    rw [List.mapM_pure]
    exact congrArg some (List.map_congr_left tailPlanEq)
  calc
    _ = (EbnfValue.choice [
          .sequence [
            .atom (.terminal (.symbol .leftParen)),
            .atom (.terminal (.symbol .star)),
            .atom (.terminal (.symbol .rightParen))],
          .sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.terminal (.category .identifier))),
            .atom (.terminal (.symbol .rightParen))]]
          ⟨⟨1, by decide⟩,
            EbnfValue.sequence [
              .atom (.terminal (.symbol .leftParen)),
              .list1 (.atom (.terminal (.category .identifier))),
              .atom (.terminal (.symbol .rightParen))]
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom
                  (.symbol .leftParen) openParen)
                (EbnfValues.cons _ _
                  (EbnfValue.list1
                    (.atom (.terminal (.category .identifier))) {
                      head := EbnfValue.terminalAtom
                        (.category .identifier) names.head.matched
                      tail := names.tail.map fun name =>
                        EbnfValue.terminalAtom
                          (.category .identifier) name.matched
                    })
                  (EbnfValues.cons _ _
                    (EbnfValue.terminalAtom
                      (.symbol .rightParen) closeParen)
                    EbnfValues.nil)))⟩).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
    _ = (EbnfValue.sequence [
          .atom (.terminal (.symbol .leftParen)),
          .list1 (.atom (.terminal (.category .identifier))),
          .atom (.terminal (.symbol .rightParen))]
          (EbnfValues.cons _ _
            (EbnfValue.terminalAtom (.symbol .leftParen) openParen)
            (EbnfValues.cons _ _
              (EbnfValue.list1
                (.atom (.terminal (.category .identifier))) {
                  head := EbnfValue.terminalAtom
                    (.category .identifier) names.head.matched
                  tail := names.tail.map fun name =>
                    EbnfValue.terminalAtom
                      (.category .identifier) name.matched
                })
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom
                  (.symbol .rightParen) closeParen)
                EbnfValues.nil)))).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = _ := by
      rw [EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_list1,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValues.tokenPlan?_nil,
        matchedSymbol_physicalTokenPlan (.leftParen) openParen,
        matchedIdentifier_physicalTokenPlan names.head headProjects,
        matchedSymbol_physicalTokenPlan (.rightParen) closeParen]
      simp [Function.comp_def, EbnfValue.tokenPlan?_terminalAtom]
      rw [mappedPlansEq]
      simp [TokenPlan.append]

private theorem ruleTokenPlan?_constructorSelection
    (selection : ConstructorSelection) :
    ruleTokenPlan? .constructorSelection selection =
      constructorSelectionPlan? selection := by
  rfl

private theorem constructorSelectionPlan?_sourceLoc_all
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (star : MatchedTerminal file tokens (.symbol .star))
    (starMarker : RuleReduction.MarkerProjects file tokens
      star .wildcard)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    constructorSelectionPlan?
      (sourceLoc witness (.all
        (RuleReduction.marker star starMarker))) =
      some (TokenPlan.enclose witness.span
        (TokenPlan.parens
          (TokenPlan.exact (.symbol .star) star.span))) := by
  unfold constructorSelectionPlan?
  change (if (RuleReduction.marker star starMarker).payload =
      SyntaxMarker.wildcard then
        some (TokenPlan.exact (.symbol .star)
          (RuleReduction.marker star starMarker).span)
      else none).bind (fun inner =>
        some (TokenPlan.enclose witness.span
          (TokenPlan.parens inner))) = _
  rfl

private theorem constructorSelectionPlan?_sourceLoc_named
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (names : NonemptyList (RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    constructorSelectionPlan?
      (sourceLoc witness (.named (names.map fun name =>
        RuleReduction.terminalLoc name.matched name.parsed))) =
      some (TokenPlan.enclose witness.span
        (TokenPlan.parens (TokenPlan.commaSeparated
          (identifierPlan
              (RuleReduction.terminalLoc names.head.matched
                names.head.parsed) ::
            names.tail.map fun name => identifierPlan
              (RuleReduction.terminalLoc name.matched name.parsed))))) := by
  rcases names with ⟨head, tail⟩
  unfold constructorSelectionPlan?
  simp [sourceLoc, NonemptyList.map]
  unfold nonemptyIdentifierPlans identifierPlans
  simp [Function.comp_def]

theorem constructorSelection_tokenPlanSound :
    GrammarRuleTokenPlanSound .constructorSelection := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | constructorSelectionAll origin finish openParen star closeParen
      starMarker witness =>
      change EbnfValue file tokens
        (.choice constructorSelectionSourceBranches) at input
      rw [← inputEq] at inputEvidence
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          some (TokenPlan.concat [
            TokenPlan.exact (.symbol .leftParen) openParen.span,
            TokenPlan.exact (.symbol .star) star.span,
            TokenPlan.exact (.symbol .rightParen) closeParen.span]) := by
        rw [inputEq]
        exact constructorSelectionAllInput_tokenPlan?
          openParen star closeParen
      have exactEvidence := inputEvidence.candidate_eq candidateEq
      rcases exactEvidence with ⟨inputPlan, planEq, relation⟩
      simp only [Option.some.injEq] at planEq
      subst inputPlan
      have innerRelation :=
        TokenSlot.ListMatches.twoFixedToParens relation
      have innerEvidence : TokenPlanEvidence
          (some (TokenPlan.parens
            (TokenPlan.exact (.symbol .star) star.span)))
          (PhysicalTokens tokens origin finish) :=
        TokenPlanEvidence.some innerRelation
      have enclosed := innerEvidence.enclose
        (fun plan success => by
          injection success with planEq
          subst plan
          change (TokenPlan.concat [
            TokenPlan.plain (.symbol .leftParen),
            TokenPlan.exact (.symbol .star) star.span,
            TokenPlan.plain (.symbol .rightParen)]).WellAnchored
          exact TokenPlan.WellAnchored.concatPlainBookended
            (.symbol .leftParen) (.symbol .rightParen)
            [TokenPlan.exact (.symbol .star) star.span])
        witness.consumed
      apply TokenPlanEvidence.candidate_eq enclosed
      rw [ruleTokenPlan?_constructorSelection]
      simpa using (constructorSelectionPlan?_sourceLoc_all
        star starMarker witness).symm
  | constructorSelectionNamed origin finish openParen names closeParen
      headProjects tailProjects witness =>
      change EbnfValue file tokens
        (.choice constructorSelectionSourceBranches) at input
      rw [← inputEq] at inputEvidence
      let namesPlan := TokenPlan.commaSeparated
        (identifierPlan
            (RuleReduction.terminalLoc names.head.matched
              names.head.parsed) ::
          names.tail.map fun name => identifierPlan
            (RuleReduction.terminalLoc name.matched name.parsed))
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          some (TokenPlan.concat [
            TokenPlan.exact (.symbol .leftParen) openParen.span,
            namesPlan,
            TokenPlan.exact (.symbol .rightParen) closeParen.span]) := by
        rw [inputEq]
        exact constructorSelectionNamedInput_tokenPlan?
          openParen names closeParen headProjects tailProjects
      have exactEvidence := inputEvidence.candidate_eq candidateEq
      rcases exactEvidence with ⟨inputPlan, planEq, relation⟩
      simp only [Option.some.injEq] at planEq
      subst inputPlan
      have innerRelation :=
        TokenSlot.ListMatches.twoFixedToParens relation
      have innerEvidence : TokenPlanEvidence
          (some (TokenPlan.parens namesPlan))
          (PhysicalTokens tokens origin finish) :=
        TokenPlanEvidence.some innerRelation
      have enclosed := innerEvidence.enclose
        (fun plan success => by
          injection success with planEq
          subst plan
          change (TokenPlan.concat [
            TokenPlan.plain (.symbol .leftParen),
            namesPlan,
            TokenPlan.plain (.symbol .rightParen)]).WellAnchored
          exact TokenPlan.WellAnchored.concatPlainBookended
            (.symbol .leftParen) (.symbol .rightParen) [namesPlan])
        witness.consumed
      apply TokenPlanEvidence.candidate_eq enclosed
      rw [ruleTokenPlan?_constructorSelection]
      simpa [namesPlan] using
        (constructorSelectionPlan?_sourceLoc_named names witness).symm

local syntax "importEntryAliasChildren!" : term
local macro_rules
  | `(importEntryAliasChildren!) =>
      `([.atom (.terminal (.hardKeyword .asKw)),
        .atom (.terminal (.category .identifier))])

local syntax "importEntryNamedChildren!" : term
local macro_rules
  | `(importEntryNamedChildren!) =>
      `([.atom (.terminal (.category .identifier)),
        .optional (.sequence importEntryAliasChildren!)])

local syntax "importEntryBranches!" : term
local macro_rules
  | `(importEntryBranches!) =>
      `([.atom (.terminal (.symbol .star)),
        .sequence importEntryNamedChildren!])

private abbrev importEntrySourceBranches : List EbnfExpr :=
  importEntryBranches!

private theorem importEntryWildcardInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (star : MatchedTerminal file tokens (.symbol .star)) :
    (EbnfValue.transport (file := file) (tokens := tokens) (by rfl)
      (EbnfValue.choice importEntryBranches!
        ⟨⟨0, by decide⟩,
          EbnfValue.terminalAtom (.symbol .star) star⟩)).tokenPlan?
        sourceRuleTokenPlanLayout =
      some (TokenPlan.exact (.symbol .star) star.span) := by
  calc
    _ = (EbnfValue.choice importEntryBranches!
          ⟨⟨0, by decide⟩,
            EbnfValue.terminalAtom (.symbol .star) star⟩).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
    _ = (EbnfValue.terminalAtom
          (.symbol .star) star).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = some (TokenPlan.exact (.symbol .star) star.span) := by
      rw [EbnfValue.tokenPlan?_terminalAtom,
        matchedSymbol_physicalTokenPlan]

private theorem importEntryNamedInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (nameProjects : IdentifierProjects name.matched
      name.spelling name.parsed) :
    (EbnfValue.transport (file := file) (tokens := tokens) (by rfl)
      (EbnfValue.choice importEntryBranches!
        ⟨⟨1, by decide⟩,
          EbnfValue.sequence importEntryNamedChildren!
            (EbnfValues.cons _ _
              (EbnfValue.terminalAtom
                (.category .identifier) name.matched)
              (EbnfValues.cons _ _
                (EbnfValue.optional
                  (.sequence importEntryAliasChildren!) none)
                EbnfValues.nil))⟩)).tokenPlan?
        sourceRuleTokenPlanLayout =
      some (identifierPlan
        (RuleReduction.terminalLoc name.matched name.parsed)) := by
  calc
    _ = (EbnfValue.choice importEntryBranches!
          ⟨⟨1, by decide⟩,
            EbnfValue.sequence importEntryNamedChildren!
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom
                  (.category .identifier) name.matched)
                (EbnfValues.cons _ _
                  (EbnfValue.optional
                    (.sequence importEntryAliasChildren!) none)
                  EbnfValues.nil))⟩).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
    _ = (EbnfValue.sequence importEntryNamedChildren!
          (EbnfValues.cons _ _
            (EbnfValue.terminalAtom
              (.category .identifier) name.matched)
            (EbnfValues.cons _ _
              (EbnfValue.optional
                (.sequence importEntryAliasChildren!) none)
              EbnfValues.nil))).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = _ := by
      simp only [EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_optional_none,
        EbnfValues.tokenPlan?_nil]
      rw [matchedIdentifier_physicalTokenPlan name nameProjects]
      exact congrArg some (TokenPlan.append_empty _)

private theorem importEntryAliasedInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (name alias : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (asKw : MatchedTerminal file tokens (.hardKeyword .asKw))
    (nameProjects : IdentifierProjects name.matched
      name.spelling name.parsed)
    (aliasProjects : IdentifierProjects alias.matched
      alias.spelling alias.parsed) :
    (EbnfValue.transport (file := file) (tokens := tokens) (by rfl)
      (EbnfValue.choice importEntryBranches!
        ⟨⟨1, by decide⟩,
          EbnfValue.sequence importEntryNamedChildren!
            (EbnfValues.cons _ _
              (EbnfValue.terminalAtom
                (.category .identifier) name.matched)
              (EbnfValues.cons _ _
                (EbnfValue.optional
                  (.sequence importEntryAliasChildren!)
                  (some (EbnfValue.sequence importEntryAliasChildren!
                    (EbnfValues.cons _ _
                      (EbnfValue.terminalAtom
                        (.hardKeyword .asKw) asKw)
                      (EbnfValues.cons _ _
                        (EbnfValue.terminalAtom
                          (.category .identifier) alias.matched)
                        EbnfValues.nil)))))
                EbnfValues.nil))⟩)).tokenPlan?
        sourceRuleTokenPlanLayout =
      some (((identifierPlan
          (RuleReduction.terminalLoc name.matched name.parsed)).append
        (TokenPlan.exact (.hardKeyword .asKw) asKw.span)).append
          (identifierPlan
            (RuleReduction.terminalLoc alias.matched alias.parsed))) := by
  calc
    _ = (EbnfValue.choice importEntryBranches!
          ⟨⟨1, by decide⟩,
            EbnfValue.sequence importEntryNamedChildren!
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom
                  (.category .identifier) name.matched)
                (EbnfValues.cons _ _
                  (EbnfValue.optional
                    (.sequence importEntryAliasChildren!)
                    (some (EbnfValue.sequence importEntryAliasChildren!
                      (EbnfValues.cons _ _
                        (EbnfValue.terminalAtom
                          (.hardKeyword .asKw) asKw)
                        (EbnfValues.cons _ _
                          (EbnfValue.terminalAtom
                            (.category .identifier) alias.matched)
                          EbnfValues.nil)))))
                  EbnfValues.nil))⟩).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
    _ = (EbnfValue.sequence importEntryNamedChildren!
          (EbnfValues.cons _ _
            (EbnfValue.terminalAtom
              (.category .identifier) name.matched)
            (EbnfValues.cons _ _
              (EbnfValue.optional
                (.sequence importEntryAliasChildren!)
                (some (EbnfValue.sequence importEntryAliasChildren!
                  (EbnfValues.cons _ _
                    (EbnfValue.terminalAtom
                      (.hardKeyword .asKw) asKw)
                    (EbnfValues.cons _ _
                      (EbnfValue.terminalAtom
                        (.category .identifier) alias.matched)
                      EbnfValues.nil)))))
              EbnfValues.nil))).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = _ := by
      simp only [EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_optional_some,
        EbnfValues.tokenPlan?_nil]
      rw [matchedIdentifier_physicalTokenPlan name nameProjects,
        matchedHardKeyword_physicalTokenPlan .asKw asKw,
        matchedIdentifier_physicalTokenPlan alias aliasProjects]
      simp [TokenPlan.append_assoc]

private theorem ruleTokenPlan?_importEntry
    (entry : ImportSelectorEntry) :
    ruleTokenPlan? .importEntry entry = importSelectorEntryPlan? entry := by
  rfl

private theorem importSelectorEntryPlan?_sourceLoc_wildcard
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (star : MatchedTerminal file tokens (.symbol .star))
    (starMarker : RuleReduction.MarkerProjects file tokens
      star .wildcard)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    importSelectorEntryPlan?
      (sourceLoc witness (.wildcard
        (RuleReduction.marker star starMarker))) =
      some (TokenPlan.enclose witness.span
        (TokenPlan.exact (.symbol .star) star.span)) := by
  unfold importSelectorEntryPlan?
  change (if (RuleReduction.marker star starMarker).payload =
      SyntaxMarker.wildcard then
        some (TokenPlan.exact (.symbol .star)
          (RuleReduction.marker star starMarker).span)
      else none).bind (fun inner =>
        some (TokenPlan.enclose witness.span inner)) = _
  rfl

private theorem importSelectorEntryPlan?_sourceLoc_named
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (name : IdentifierOccurrence)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    importSelectorEntryPlan?
      (sourceLoc witness (.named name none)) =
      some (TokenPlan.enclose witness.span (identifierPlan name)) := by
  unfold importSelectorEntryPlan?
  change (some ((identifierPlan name).append TokenPlan.empty)).bind
    (fun inner => some (TokenPlan.enclose witness.span inner)) = _
  simp

private theorem importSelectorEntryPlan?_sourceLoc_aliased
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (name alias : IdentifierOccurrence)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    importSelectorEntryPlan?
      (sourceLoc witness (.named name (some alias))) =
      some (TokenPlan.enclose witness.span
        ((identifierPlan name).append (TokenPlan.concat [
          TokenPlan.plain (.hardKeyword .asKw),
          identifierPlan alias]))) := by
  unfold importSelectorEntryPlan?
  change (some ((identifierPlan name).append (TokenPlan.concat [
      TokenPlan.plain (.hardKeyword .asKw),
      identifierPlan alias]))).bind
    (fun inner => some (TokenPlan.enclose witness.span inner)) = _
  rfl

theorem importEntry_tokenPlanSound :
    GrammarRuleTokenPlanSound .importEntry := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | importEntryWildcard origin finish star starMarker witness =>
      change EbnfValue file tokens
        (.choice importEntrySourceBranches) at input
      rw [← inputEq] at inputEvidence
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          some (TokenPlan.exact (.symbol .star) star.span) := by
        rw [inputEq]
        exact importEntryWildcardInput_tokenPlan? star
      have innerEvidence := inputEvidence.candidate_eq candidateEq
      have enclosed := innerEvidence.enclose
        (fun plan success => by
          injection success with planEq
          subst plan
          exact TokenPlan.WellAnchored.exact _ _)
        witness.consumed
      apply TokenPlanEvidence.candidate_eq enclosed
      rw [ruleTokenPlan?_importEntry]
      simpa using (importSelectorEntryPlan?_sourceLoc_wildcard
        star starMarker witness).symm
  | importEntryNamed origin finish name nameProjects witness =>
      change EbnfValue file tokens
        (.choice importEntrySourceBranches) at input
      rw [← inputEq] at inputEvidence
      let nameLoc := RuleReduction.terminalLoc name.matched name.parsed
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          some (identifierPlan nameLoc) := by
        rw [inputEq]
        exact importEntryNamedInput_tokenPlan? name nameProjects
      have innerEvidence := inputEvidence.candidate_eq candidateEq
      have enclosed := innerEvidence.enclose
        (fun plan success => by
          injection success with planEq
          subst plan
          exact identifierPlan_wellAnchored nameLoc)
        witness.consumed
      apply TokenPlanEvidence.candidate_eq enclosed
      rw [ruleTokenPlan?_importEntry]
      simpa [nameLoc] using
        (importSelectorEntryPlan?_sourceLoc_named nameLoc witness).symm
  | importEntryAliased origin finish name alias asKw nameProjects
      aliasProjects witness =>
      change EbnfValue file tokens
        (.choice importEntrySourceBranches) at input
      rw [← inputEq] at inputEvidence
      let nameLoc := RuleReduction.terminalLoc name.matched name.parsed
      let aliasLoc := RuleReduction.terminalLoc alias.matched alias.parsed
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          some (((identifierPlan nameLoc).append
            (TokenPlan.exact (.hardKeyword .asKw) asKw.span)).append
              (identifierPlan aliasLoc)) := by
        rw [inputEq]
        exact importEntryAliasedInput_tokenPlan?
          name alias asKw nameProjects aliasProjects
      have exactEvidence := inputEvidence.candidate_eq candidateEq
      have innerEvidence := exactEvidence.exactMiddleToPlain
      have enclosed := innerEvidence.enclose
        (fun plan success => by
          injection success with planEq
          subst plan
          exact TokenPlan.WellAnchored.append
            (TokenPlan.WellAnchored.append
              (identifierPlan_wellAnchored nameLoc)
              (TokenPlan.WellAnchored.plain _))
            (identifierPlan_wellAnchored aliasLoc))
        witness.consumed
      apply TokenPlanEvidence.candidate_eq enclosed
      rw [ruleTokenPlan?_importEntry,
        importSelectorEntryPlan?_sourceLoc_aliased
          nameLoc aliasLoc witness]
      simp only [Option.map_some, Option.some.injEq]
      simp [TokenPlan.concat_cons, TokenPlan.append_assoc]

end Solcore.Surface.Multi
