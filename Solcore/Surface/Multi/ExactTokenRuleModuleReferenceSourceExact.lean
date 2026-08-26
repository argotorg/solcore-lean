import Solcore.Surface.Multi.ExactTokenAnchoring
import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenCoherentRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

private theorem TokensLexicallyExact.identifierPayload_notKeyword
    {file : WorkspaceFile} {tokens : List Token}
    (lexical : TokensLexicallyExact file tokens)
    {token : Token} (member : token ∈ tokens) {spelling : String}
    (payloadEq : token.payload = .identifier spelling) :
    HardKeyword.ofString? spelling = none := by
  have classification := (lexical token member).2
  rw [payloadEq] at classification
  exact classification

private theorem matchedPathComponent_physicalTokenPlan_of_lexicallyExact
    {file : WorkspaceFile} {tokens : List Token}
    (lexical : TokensLexicallyExact file tokens)
    (data : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (projects : PathSegmentProjects data.matched data.spelling data.parsed) :
    data.matched.physicalTokenPlan =
      pathComponentPlan
        (RuleReduction.terminalLoc data.matched data.parsed) := by
  rcases projects with ⟨token, valueEq, payloadShape, parseEq⟩
  rcases data.matched.retained_member_and_span valueEq with
    ⟨member, matchedSpanEq⟩
  have spellingEq : data.spelling = data.parsed.render :=
    (PathSegment.text_eq_of_parse_eq_some parseEq).symm
  rcases payloadShape with payloadEq | ⟨keyword, payloadEq, keywordEq⟩
  · have notKeyword := lexical.identifierPayload_notKeyword member payloadEq
    have parsedNotKeyword :
        HardKeyword.ofString? data.parsed.render = none := by
      simpa only [← spellingEq] using notKeyword
    simp [MatchedTerminal.physicalTokenPlan, pathComponentPlan,
      RuleReduction.terminalLoc, valueEq, payloadEq, spellingEq,
      tokenKindOfPathSpelling, parsedNotKeyword, matchedSpanEq]
  · have parsedKeywordEq : data.parsed.render = keyword.spelling :=
      spellingEq.symm.trans keywordEq
    simp [MatchedTerminal.physicalTokenPlan, pathComponentPlan,
      RuleReduction.terminalLoc, valueEq, payloadEq, parsedKeywordEq,
      tokenKindOfPathSpelling, matchedSpanEq]

private theorem matchedExternalLibrary_physicalTokenPlan_of_lexicallyExact
    {file : WorkspaceFile} {tokens : List Token}
    (lexical : TokensLexicallyExact file tokens)
    (data : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) ExternalLibraryName)
    (projects : ExternalLibraryProjects data.matched
      data.spelling data.parsed) :
    data.matched.physicalTokenPlan =
      externalLibraryPlan
        (RuleReduction.terminalLoc data.matched data.parsed) := by
  rcases projects with ⟨token, valueEq, payloadShape, parseEq⟩
  rcases data.matched.retained_member_and_span valueEq with
    ⟨member, matchedSpanEq⟩
  have spellingEq : data.spelling = data.parsed.render :=
    ExternalLibraryName.text_eq_render_of_parse_eq_some parseEq
  rcases payloadShape with payloadEq | ⟨keyword, payloadEq, keywordEq⟩
  · have notKeyword := lexical.identifierPayload_notKeyword member payloadEq
    have parsedNotKeyword :
        HardKeyword.ofString? data.parsed.render = none := by
      simpa only [← spellingEq] using notKeyword
    simp [MatchedTerminal.physicalTokenPlan, externalLibraryPlan,
      RuleReduction.terminalLoc, valueEq, payloadEq, spellingEq,
      tokenKindOfPathSpelling, parsedNotKeyword, matchedSpanEq]
  · have parsedKeywordEq : data.parsed.render = keyword.spelling :=
      spellingEq.symm.trans keywordEq
    simp [MatchedTerminal.physicalTokenPlan, externalLibraryPlan,
      RuleReduction.terminalLoc, valueEq, payloadEq, parsedKeywordEq,
      tokenKindOfPathSpelling, matchedSpanEq]

private abbrev ModuleRefSourceEntry
    (file : WorkspaceFile) (tokens : List Token) :=
  MatchedTerminal file tokens (.symbol .dot) ×
    RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment

private abbrev moduleRefTailExpression : EbnfExpr :=
  .group (.sequence [
    .atom (.terminal (.symbol .dot)),
    .atom (.terminal (.category .pathComponent))])

private abbrev moduleRefRelativeChildren : List EbnfExpr := [
  .atom (.terminal (.category .pathComponent)),
  .star moduleRefTailExpression]

private abbrev moduleRefExternalChildren : List EbnfExpr := [
  .atom (.terminal (.symbol .at)),
  .atom (.terminal (.category .pathComponent)),
  .atom (.terminal (.symbol .dot)),
  .atom (.terminal (.category .pathComponent)),
  .star moduleRefTailExpression]

private abbrev moduleRefSourceBranches : List EbnfExpr := [
  .sequence moduleRefExternalChildren,
  .sequence moduleRefRelativeChildren]

private def moduleRefTailValue
    {file : WorkspaceFile} {tokens : List Token}
    (entry : ModuleRefSourceEntry file tokens) :
    EbnfValue file tokens moduleRefTailExpression :=
  EbnfValue.group _ <| EbnfValue.sequence _ <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .dot) entry.1) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom
        (.category .pathComponent) entry.2.matched) <|
    EbnfValues.nil

private def moduleRefRelativeSequenceInput
    {file : WorkspaceFile} {tokens : List Token}
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens)) :
    EbnfValue file tokens (.sequence moduleRefRelativeChildren) :=
  EbnfValue.sequence moduleRefRelativeChildren <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom
        (.category .pathComponent) first.matched) <|
    EbnfValues.cons _ _
      (EbnfValue.star moduleRefTailExpression
        (rest.map moduleRefTailValue)) <|
    EbnfValues.nil

private def moduleRefRelativeSourceInput
    {file : WorkspaceFile} {tokens : List Token}
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens)) :
    EbnfValue file tokens (m2cV1.rhs .moduleRef) :=
  EbnfValue.transport (by rfl) <|
    EbnfValue.choice moduleRefSourceBranches
      ⟨⟨1, by decide⟩, moduleRefRelativeSequenceInput first rest⟩

private def moduleRefExternalSequenceInput
    {file : WorkspaceFile} {tokens : List Token}
    (atToken : MatchedTerminal file tokens (.symbol .at))
    (library : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) ExternalLibraryName)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (next : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens)) :
    EbnfValue file tokens (.sequence moduleRefExternalChildren) :=
  EbnfValue.sequence moduleRefExternalChildren <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .at) atToken) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom
        (.category .pathComponent) library.matched) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .dot) dot) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom
        (.category .pathComponent) next.matched) <|
    EbnfValues.cons _ _
      (EbnfValue.star moduleRefTailExpression
        (rest.map moduleRefTailValue)) <|
    EbnfValues.nil

private def moduleRefExternalSourceInput
    {file : WorkspaceFile} {tokens : List Token}
    (atToken : MatchedTerminal file tokens (.symbol .at))
    (library : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) ExternalLibraryName)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (next : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens)) :
    EbnfValue file tokens (m2cV1.rhs .moduleRef) :=
  EbnfValue.transport (by rfl) <|
    EbnfValue.choice moduleRefSourceBranches
      ⟨⟨0, by decide⟩,
        moduleRefExternalSequenceInput atToken library dot next rest⟩

private def moduleRefTailPhysicalPlan
    {file : WorkspaceFile} {tokens : List Token}
    (entry : ModuleRefSourceEntry file tokens) : TokenPlan :=
  entry.1.physicalTokenPlan.append entry.2.matched.physicalTokenPlan

@[simp] private theorem moduleRefTailValue_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (entry : ModuleRefSourceEntry file tokens) :
    (moduleRefTailValue entry).tokenPlan? sourceRuleTokenPlanLayout =
      some (moduleRefTailPhysicalPlan entry) := by
  simp [moduleRefTailValue, moduleRefTailPhysicalPlan]

@[simp] private theorem moduleRefTailValues_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (rest : List (ModuleRefSourceEntry file tokens)) :
    (rest.map moduleRefTailValue).mapM
        (fun value => value.tokenPlan? sourceRuleTokenPlanLayout) =
      some (rest.map moduleRefTailPhysicalPlan) := by
  induction rest with
  | nil => rfl
  | cons entry rest induction => simp [induction]

private def moduleRefRelativePhysicalPlan
    {file : WorkspaceFile} {tokens : List Token}
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens)) : TokenPlan :=
  first.matched.physicalTokenPlan.append
    (.concat (rest.map moduleRefTailPhysicalPlan))

private theorem moduleRefRelativeSourceInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens)) :
    (moduleRefRelativeSourceInput first rest).tokenPlan?
        sourceRuleTokenPlanLayout =
      some (moduleRefRelativePhysicalPlan first rest) := by
  unfold moduleRefRelativeSourceInput
  rw [EbnfValue.tokenPlan?_transport]
  rw [EbnfValue.tokenPlan?_choiceView]
  rw [EbnfValue.choiceView_choice]
  change (moduleRefRelativeSequenceInput first rest).tokenPlan?
    sourceRuleTokenPlanLayout = _
  unfold moduleRefRelativeSequenceInput
  rw [EbnfValue.tokenPlan?_sequence]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_terminalAtom]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_star]
  rw [moduleRefTailValues_tokenPlan?]
  rw [EbnfValues.tokenPlan?_nil]
  simp [moduleRefRelativePhysicalPlan]

private def moduleRefExternalPhysicalPlan
    {file : WorkspaceFile} {tokens : List Token}
    (atToken : MatchedTerminal file tokens (.symbol .at))
    (library : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) ExternalLibraryName)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (next : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens)) : TokenPlan :=
  .concat [atToken.physicalTokenPlan,
    library.matched.physicalTokenPlan,
    dot.physicalTokenPlan,
    next.matched.physicalTokenPlan,
    .concat (rest.map moduleRefTailPhysicalPlan)]

private theorem moduleRefExternalSourceInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (atToken : MatchedTerminal file tokens (.symbol .at))
    (library : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) ExternalLibraryName)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (next : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens)) :
    (moduleRefExternalSourceInput atToken library dot next rest).tokenPlan?
        sourceRuleTokenPlanLayout =
      some (moduleRefExternalPhysicalPlan atToken library dot next rest) := by
  unfold moduleRefExternalSourceInput
  rw [EbnfValue.tokenPlan?_transport]
  rw [EbnfValue.tokenPlan?_choiceView]
  rw [EbnfValue.choiceView_choice]
  change (moduleRefExternalSequenceInput atToken library dot next rest).tokenPlan?
    sourceRuleTokenPlanLayout = _
  unfold moduleRefExternalSequenceInput
  rw [EbnfValue.tokenPlan?_sequence]
  repeat' rw [EbnfValues.tokenPlan?_cons]
  repeat' first | rw [EbnfValue.tokenPlan?_terminalAtom]
  rw [EbnfValue.tokenPlan?_star]
  rw [moduleRefTailValues_tokenPlan?]
  rw [EbnfValues.tokenPlan?_nil]
  simp [moduleRefExternalPhysicalPlan, TokenPlan.concat_cons]

private def moduleRefTailPlainPlan
    {file : WorkspaceFile} {tokens : List Token}
    (entry : ModuleRefSourceEntry file tokens) : TokenPlan :=
  (TokenPlan.plain (.symbol .dot)).append
    entry.2.matched.physicalTokenPlan

private theorem moduleRefTailPhysicalPlan_listMatches_toPlain
    {file : WorkspaceFile} {tokens : List Token}
    (entry : ModuleRefSourceEntry file tokens)
    {actual : List Token}
    (relation : TokenSlot.ListMatches
      (moduleRefTailPhysicalPlan entry).slots actual) :
    TokenSlot.ListMatches
      (moduleRefTailPlainPlan entry).slots actual := by
  unfold moduleRefTailPhysicalPlan at relation
  unfold moduleRefTailPlainPlan
  rw [MatchedTerminal.physicalTokenPlan_symbol] at relation
  change TokenSlot.ListMatches
    (.required (ExpectedToken.exact (.symbol .dot) entry.1.span) ::
      entry.2.matched.physicalTokenPlan.slots) actual at relation
  change TokenSlot.ListMatches
    (.required (ExpectedToken.plain (.symbol .dot)) ::
      entry.2.matched.physicalTokenPlan.slots) actual
  exact relation.requiredHeadToPlain

private theorem moduleRefTailPlans_listMatches_toPlain
    {file : WorkspaceFile} {tokens : List Token}
    (rest : List (ModuleRefSourceEntry file tokens))
    {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat
        (rest.map moduleRefTailPhysicalPlan)).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.concat
        (rest.map moduleRefTailPlainPlan)).slots actual := by
  induction rest generalizing actual with
  | nil => exact relation
  | cons entry rest induction =>
      change TokenSlot.ListMatches
        ((moduleRefTailPhysicalPlan entry).slots ++
          (TokenPlan.concat
            (rest.map moduleRefTailPhysicalPlan)).slots) actual
        at relation
      rcases relation.split_append with
        ⟨headActual, tailActual, actualEq, headRelation, tailRelation⟩
      change TokenSlot.ListMatches
        ((moduleRefTailPlainPlan entry).slots ++
          (TokenPlan.concat
            (rest.map moduleRefTailPlainPlan)).slots) actual
      rw [actualEq]
      exact (moduleRefTailPhysicalPlan_listMatches_toPlain
        entry headRelation).append (induction tailRelation)

private def moduleRefPathPhysicalCorePlan
    {file : WorkspaceFile} {tokens : List Token}
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens)) : TokenPlan :=
  first.matched.physicalTokenPlan.append
    (.concat (rest.map moduleRefTailPlainPlan))

private theorem moduleRefRelativePhysicalPlan_listMatches_toCore
    {file : WorkspaceFile} {tokens : List Token}
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens))
    {actual : List Token}
    (relation : TokenSlot.ListMatches
      (moduleRefRelativePhysicalPlan first rest).slots actual) :
    TokenSlot.ListMatches
      (moduleRefPathPhysicalCorePlan first rest).slots actual := by
  unfold moduleRefRelativePhysicalPlan at relation
  unfold moduleRefPathPhysicalCorePlan
  rcases relation.split_append with
    ⟨headActual, tailActual, actualEq, headRelation, tailRelation⟩
  rw [actualEq]
  exact headRelation.append
    (moduleRefTailPlans_listMatches_toPlain rest tailRelation)

private def moduleRefTailOutputPlan
    {file : WorkspaceFile} {tokens : List Token}
    (entry : ModuleRefSourceEntry file tokens) : TokenPlan :=
  (TokenPlan.plain (.symbol .dot)).append <|
    pathComponentPlan
      (RuleReduction.terminalLoc entry.2.matched entry.2.parsed)

private def moduleRefPathOutputCorePlan
    {file : WorkspaceFile} {tokens : List Token}
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens)) : TokenPlan :=
  (pathComponentPlan
    (RuleReduction.terminalLoc first.matched first.parsed)).append <|
      .concat (rest.map moduleRefTailOutputPlan)

private theorem moduleRefTailOutputPlans_eq
    {file : WorkspaceFile} {tokens : List Token}
    (rest : List (ModuleRefSourceEntry file tokens)) :
    rest.map (fun entry =>
        (TokenPlan.plain (.symbol .dot)).append <|
          pathComponentPlan
            (RuleReduction.terminalLoc
              entry.2.matched entry.2.parsed)) =
      rest.map moduleRefTailOutputPlan := by
  rfl

private theorem moduleRefTailPlainPlan_eq_outputPlan
    {file : WorkspaceFile} {tokens : List Token}
    (lexical : TokensLexicallyExact file tokens)
    (entry : ModuleRefSourceEntry file tokens)
    (projects : PathSegmentProjects entry.2.matched
      entry.2.spelling entry.2.parsed) :
    moduleRefTailPlainPlan entry = moduleRefTailOutputPlan entry := by
  unfold moduleRefTailPlainPlan moduleRefTailOutputPlan
  rw [matchedPathComponent_physicalTokenPlan_of_lexicallyExact
    lexical entry.2 projects]

private theorem moduleRefTailPlainPlans_eq_outputPlans
    {file : WorkspaceFile} {tokens : List Token}
    (lexical : TokensLexicallyExact file tokens)
    (rest : List (ModuleRefSourceEntry file tokens))
    (projects : ∀ entry, entry ∈ rest →
      PathSegmentProjects entry.2.matched
        entry.2.spelling entry.2.parsed) :
    rest.map moduleRefTailPlainPlan =
      rest.map moduleRefTailOutputPlan := by
  induction rest with
  | nil => rfl
  | cons entry rest induction =>
      simp only [List.map_cons]
      rw [moduleRefTailPlainPlan_eq_outputPlan lexical entry
        (projects entry (by simp))]
      rw [induction (by
        intro candidate member
        exact projects candidate (by simp [member]))]

private theorem moduleRefPathPhysicalCorePlan_eq_outputCorePlan
    {file : WorkspaceFile} {tokens : List Token}
    (lexical : TokensLexicallyExact file tokens)
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens))
    (firstProjects : PathSegmentProjects first.matched
      first.spelling first.parsed)
    (restProjects : ∀ entry, entry ∈ rest →
      PathSegmentProjects entry.2.matched
        entry.2.spelling entry.2.parsed) :
    moduleRefPathPhysicalCorePlan first rest =
      moduleRefPathOutputCorePlan first rest := by
  unfold moduleRefPathPhysicalCorePlan moduleRefPathOutputCorePlan
  rw [matchedPathComponent_physicalTokenPlan_of_lexicallyExact
    lexical first firstProjects]
  rw [moduleRefTailPlainPlans_eq_outputPlans
    lexical rest restProjects]

private theorem moduleRefPathOutputCorePlan_wellAnchored
    {file : WorkspaceFile} {tokens : List Token}
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens)) :
    (moduleRefPathOutputCorePlan first rest).WellAnchored := by
  unfold moduleRefPathOutputCorePlan
  apply TokenPlan.WellAnchored.append
  · unfold pathComponentPlan
    exact TokenPlan.WellAnchored.exact _ _
  · apply TokenPlan.WellAnchored.concat
    intro plan member
    simp only [List.mem_map] at member
    rcases member with ⟨entry, _entryMember, rfl⟩
    unfold moduleRefTailOutputPlan pathComponentPlan
    exact TokenPlan.WellAnchored.append
      (TokenPlan.WellAnchored.plain _)
      (TokenPlan.WellAnchored.exact _ _)

private def moduleRefExternalPhysicalCorePlan
    {file : WorkspaceFile} {tokens : List Token}
    (atToken : MatchedTerminal file tokens (.symbol .at))
    (library : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) ExternalLibraryName)
    (next : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens)) : TokenPlan :=
  .concat [atToken.physicalTokenPlan,
    library.matched.physicalTokenPlan,
    .plain (.symbol .dot),
    next.matched.physicalTokenPlan,
    .concat (rest.map moduleRefTailPlainPlan)]

private theorem moduleRefExternalPhysicalPlan_listMatches_toCore
    {file : WorkspaceFile} {tokens : List Token}
    (atToken : MatchedTerminal file tokens (.symbol .at))
    (library : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) ExternalLibraryName)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (next : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens))
    {actual : List Token}
    (relation : TokenSlot.ListMatches
      (moduleRefExternalPhysicalPlan atToken library dot next rest).slots
      actual) :
    TokenSlot.ListMatches
      (moduleRefExternalPhysicalCorePlan atToken library next rest).slots
      actual := by
  have normalized : TokenSlot.ListMatches
      ((TokenPlan.concat [atToken.physicalTokenPlan,
        library.matched.physicalTokenPlan,
        dot.physicalTokenPlan,
        next.matched.physicalTokenPlan]).append
          (TokenPlan.concat
            (rest.map moduleRefTailPhysicalPlan))).slots actual := by
    simpa [moduleRefExternalPhysicalPlan, TokenPlan.concat_cons,
      TokenPlan.append_assoc] using relation
  rcases normalized.split_append with
    ⟨headActual, tailActual, actualEq, headRelation, tailRelation⟩
  have shapedHead : TokenSlot.ListMatches
      ((TokenPlan.concat [atToken.physicalTokenPlan,
        library.matched.physicalTokenPlan]).append
          ((TokenPlan.exact (.symbol .dot) dot.span).append
            next.matched.physicalTokenPlan)).slots headActual := by
    simpa [MatchedTerminal.physicalTokenPlan_symbol,
      TokenPlan.concat_cons, TokenPlan.append_assoc] using headRelation
  have headPlain : TokenSlot.ListMatches
      (TokenPlan.concat [atToken.physicalTokenPlan,
        library.matched.physicalTokenPlan,
        .plain (.symbol .dot),
        next.matched.physicalTokenPlan]).slots headActual := by
    have converted := shapedHead.exactBetweenToPlain
    simpa [TokenPlan.concat_cons, TokenPlan.append_assoc] using converted
  rw [actualEq]
  have combined := headPlain.append
    (moduleRefTailPlans_listMatches_toPlain rest tailRelation)
  simpa [moduleRefExternalPhysicalCorePlan, TokenPlan.concat_cons,
    TokenPlan.append_assoc, TokenPlan.append, TokenPlan.empty,
    List.append_assoc] using combined

private def moduleRefExternalOutputCorePlan
    {file : WorkspaceFile} {tokens : List Token}
    (atToken : MatchedTerminal file tokens (.symbol .at))
    (library : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) ExternalLibraryName)
    (next : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens)) : TokenPlan :=
  .concat [.exact (.symbol .at) atToken.span,
    externalLibraryPlan
      (RuleReduction.terminalLoc library.matched library.parsed),
    .plain (.symbol .dot),
    pathComponentPlan
      (RuleReduction.terminalLoc next.matched next.parsed),
    .concat (rest.map moduleRefTailOutputPlan)]

private theorem moduleRefExternalPhysicalCorePlan_eq_outputCorePlan
    {file : WorkspaceFile} {tokens : List Token}
    (lexical : TokensLexicallyExact file tokens)
    (atToken : MatchedTerminal file tokens (.symbol .at))
    (library : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) ExternalLibraryName)
    (next : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens))
    (libraryProjects : ExternalLibraryProjects library.matched
      library.spelling library.parsed)
    (nextProjects : PathSegmentProjects next.matched
      next.spelling next.parsed)
    (restProjects : ∀ entry, entry ∈ rest →
      PathSegmentProjects entry.2.matched
        entry.2.spelling entry.2.parsed) :
    moduleRefExternalPhysicalCorePlan atToken library next rest =
      moduleRefExternalOutputCorePlan atToken library next rest := by
  unfold moduleRefExternalPhysicalCorePlan
  unfold moduleRefExternalOutputCorePlan
  rw [MatchedTerminal.physicalTokenPlan_symbol]
  rw [matchedExternalLibrary_physicalTokenPlan_of_lexicallyExact
    lexical library libraryProjects]
  rw [matchedPathComponent_physicalTokenPlan_of_lexicallyExact
    lexical next nextProjects]
  rw [moduleRefTailPlainPlans_eq_outputPlans
    lexical rest restProjects]

private theorem moduleRefExternalOutputCorePlan_wellAnchored
    {file : WorkspaceFile} {tokens : List Token}
    (atToken : MatchedTerminal file tokens (.symbol .at))
    (library : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) ExternalLibraryName)
    (next : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens)) :
    (moduleRefExternalOutputCorePlan atToken library next rest).WellAnchored := by
  unfold moduleRefExternalOutputCorePlan
  apply TokenPlan.WellAnchored.concat
  intro plan member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact TokenPlan.WellAnchored.exact _ _
  · unfold externalLibraryPlan
    exact TokenPlan.WellAnchored.exact _ _
  · exact TokenPlan.WellAnchored.plain _
  · unfold pathComponentPlan
    exact TokenPlan.WellAnchored.exact _ _
  · apply TokenPlan.WellAnchored.concat
    intro tailPlan tailMember
    simp only [List.mem_map] at tailMember
    rcases tailMember with ⟨entry, _entryMember, rfl⟩
    unfold moduleRefTailOutputPlan pathComponentPlan
    exact TokenPlan.WellAnchored.append
      (TokenPlan.WellAnchored.plain _)
      (TokenPlan.WellAnchored.exact _ _)

private theorem moduleRefRelativeOutput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens))
    (witness : ConsumedSpanWitness file tokens origin finish)
    (shapeExact : relativeModuleReferenceShapeExactBool {
      head := RuleReduction.terminalLoc first.matched first.parsed
      tail := rest.map fun entry =>
        RuleReduction.terminalLoc entry.2.matched entry.2.parsed
    } = true) :
    ruleTokenPlan? .moduleRef
        (sourceLoc witness (.relative {
          head := RuleReduction.terminalLoc first.matched first.parsed
          tail := rest.map fun entry =>
            RuleReduction.terminalLoc entry.2.matched entry.2.parsed
        })) =
      some (TokenPlan.enclose witness.span
        (moduleRefPathOutputCorePlan first rest)) := by
  simp [ruleTokenPlan?, moduleReferencePlan?, sourceLoc, shapeExact,
    moduleRefPathOutputCorePlan, moduleRefTailOutputPlans_eq,
    List.map_map, Function.comp_def]

private theorem moduleRefExternalOutput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (atToken : MatchedTerminal file tokens (.symbol .at))
    (library : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) ExternalLibraryName)
    (next : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens))
    (atMarker : RuleReduction.MarkerProjects file tokens
      atToken .externalSigil)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    ruleTokenPlan? .moduleRef
        (sourceLoc witness (.external
          (RuleReduction.marker atToken atMarker)
          (RuleReduction.terminalLoc library.matched library.parsed)
          { head := RuleReduction.terminalLoc next.matched next.parsed
            tail := rest.map fun entry =>
              RuleReduction.terminalLoc entry.2.matched entry.2.parsed })) =
      some (TokenPlan.enclose witness.span
        (moduleRefExternalOutputCorePlan atToken library next rest)) := by
  simp [ruleTokenPlan?, moduleReferencePlan?, sourceLoc,
    RuleReduction.marker, RuleReduction.terminalLoc,
    moduleRefExternalOutputCorePlan,
    List.map_map, Function.comp_def, TokenPlan.concat_cons]
  have tailEq := moduleRefTailOutputPlans_eq rest
  simp only [RuleReduction.terminalLoc] at tailEq
  rw [tailEq]

private def moduleRefMarkerData
    {file : WorkspaceFile} {tokens : List Token}
    (matched : MatchedTerminal file tokens (.category .pathComponent))
    (spelling : String) (parsed : PathSegment) :
    RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment := {
  matched := matched
  spelling := spelling
  parsed := parsed
}

private theorem moduleRefStandardOutput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (first : MatchedTerminal file tokens (.category .pathComponent))
    (parsed : PathSegment)
    (projects : PathSegmentProjects first "std" parsed)
    (rest : List (ModuleRefSourceEntry file tokens))
    (rootMarker : RuleReduction.MarkerProjects file tokens
      first .standardRoot)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    ruleTokenPlan? .moduleRef
        (sourceLoc witness (.standard
          (RuleReduction.marker first rootMarker)
          (rest.map fun entry =>
            RuleReduction.terminalLoc entry.2.matched entry.2.parsed))) =
      some (TokenPlan.enclose witness.span
        (moduleRefPathOutputCorePlan
          (moduleRefMarkerData first "std" parsed) rest)) := by
  rcases projects with ⟨token, valueEq, payloadShape, parseEq⟩
  have renderEq : parsed.render = "std" :=
    PathSegment.text_eq_of_parse_eq_some parseEq
  have headPlanEq : pathComponentPlan {
      span := first.span
      payload := parsed
    } = TokenPlan.exact (.identifier "std") first.span := by
    simp [pathComponentPlan, tokenKindOfPathSpelling, renderEq,
      HardKeyword.ofString?]
  have tailEq := moduleRefTailOutputPlans_eq rest
  simp only [RuleReduction.terminalLoc] at tailEq
  simp [ruleTokenPlan?, moduleReferencePlan?, sourceLoc,
    RuleReduction.marker, RuleReduction.terminalLoc,
    moduleRefPathOutputCorePlan, moduleRefMarkerData,
    List.map_map, Function.comp_def]
  rw [headPlanEq, tailEq]

private theorem moduleRefLibraryRootOutput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (first : MatchedTerminal file tokens (.category .pathComponent))
    (parsed : PathSegment)
    (projects : PathSegmentProjects first "lib" parsed)
    (nextDot : MatchedTerminal file tokens (.symbol .dot))
    (next : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (remaining : List (ModuleRefSourceEntry file tokens))
    (rootMarker : RuleReduction.MarkerProjects file tokens
      first .libraryRoot)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    ruleTokenPlan? .moduleRef
        (sourceLoc witness (.libraryRoot
          (RuleReduction.marker first rootMarker)
          { head := RuleReduction.terminalLoc next.matched next.parsed
            tail := remaining.map fun entry =>
              RuleReduction.terminalLoc entry.2.matched entry.2.parsed })) =
      some (TokenPlan.enclose witness.span
        (moduleRefPathOutputCorePlan
          (moduleRefMarkerData first "lib" parsed)
          ((nextDot, next) :: remaining))) := by
  rcases projects with ⟨token, valueEq, payloadShape, parseEq⟩
  have renderEq : parsed.render = "lib" :=
    PathSegment.text_eq_of_parse_eq_some parseEq
  have headPlanEq : pathComponentPlan {
      span := first.span
      payload := parsed
    } = TokenPlan.exact (.identifier "lib") first.span := by
    simp [pathComponentPlan, tokenKindOfPathSpelling, renderEq,
      HardKeyword.ofString?]
  have tailEq := moduleRefTailOutputPlans_eq remaining
  simp only [RuleReduction.terminalLoc] at tailEq
  simp [ruleTokenPlan?, moduleReferencePlan?, sourceLoc,
    RuleReduction.marker, RuleReduction.terminalLoc,
    moduleRefPathOutputCorePlan, moduleRefMarkerData,
    moduleRefTailOutputPlan, List.map_map, Function.comp_def,
    TokenPlan.concat_cons, TokenPlan.append_assoc]
  rw [headPlanEq, tailEq]

private theorem moduleRefRelative_shapeExact
    {file : WorkspaceFile} {tokens : List Token}
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens))
    (renderEq : first.parsed.render = first.spelling)
    (notStandard : first.spelling ≠ "std")
    (notLibraryOrEmpty : first.spelling ≠ "lib" ∨ rest = []) :
    relativeModuleReferenceShapeExactBool {
      head := RuleReduction.terminalLoc first.matched first.parsed
      tail := rest.map fun entry =>
        RuleReduction.terminalLoc entry.2.matched entry.2.parsed
    } = true := by
  simp [relativeModuleReferenceShapeExactBool,
    RuleReduction.terminalLoc, renderEq, notStandard,
    notLibraryOrEmpty]

private theorem moduleRefPathEvidence
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (lexicallyExact : TokensLexicallyExact file tokens)
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens))
    (firstProjects : PathSegmentProjects first.matched
      first.spelling first.parsed)
    (restProjects : ∀ entry, entry ∈ rest →
      PathSegmentProjects entry.2.matched
        entry.2.spelling entry.2.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish)
    {candidate : Option TokenPlan}
    (inputEvidence : TokenPlanEvidence
      ((moduleRefRelativeSourceInput first rest).tokenPlan?
        sourceRuleTokenPlanLayout)
      (PhysicalTokens tokens origin finish))
    (outputEq : candidate = some (TokenPlan.enclose witness.span
      (moduleRefPathOutputCorePlan first rest))) :
    TokenPlanEvidence candidate
      (PhysicalTokens tokens origin finish) := by
  have physicalEvidence := inputEvidence.candidate_eq
    (moduleRefRelativeSourceInput_tokenPlan? first rest)
  rcases physicalEvidence with ⟨plan, candidateEq, relation⟩
  simp only [Option.some.injEq] at candidateEq
  subst plan
  have coreRelation :=
    moduleRefRelativePhysicalPlan_listMatches_toCore first rest relation
  rw [moduleRefPathPhysicalCorePlan_eq_outputCorePlan
    lexicallyExact first rest firstProjects restProjects] at coreRelation
  have coreEvidence := TokenPlanEvidence.some coreRelation
  have enclosed := TokenPlanEvidence.enclose coreEvidence
    (by
      intro plan success
      simp only [Option.some.injEq] at success
      subst plan
      exact moduleRefPathOutputCorePlan_wellAnchored first rest)
    witness.consumed
  exact enclosed.candidate_eq outputEq.symm

private theorem moduleRefExternalEvidence
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (lexicallyExact : TokensLexicallyExact file tokens)
    (atToken : MatchedTerminal file tokens (.symbol .at))
    (library : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) ExternalLibraryName)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (next : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (rest : List (ModuleRefSourceEntry file tokens))
    (libraryProjects : ExternalLibraryProjects library.matched
      library.spelling library.parsed)
    (nextProjects : PathSegmentProjects next.matched
      next.spelling next.parsed)
    (restProjects : ∀ entry, entry ∈ rest →
      PathSegmentProjects entry.2.matched
        entry.2.spelling entry.2.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish)
    {candidate : Option TokenPlan}
    (inputEvidence : TokenPlanEvidence
      ((moduleRefExternalSourceInput
        atToken library dot next rest).tokenPlan?
          sourceRuleTokenPlanLayout)
      (PhysicalTokens tokens origin finish))
    (outputEq : candidate = some (TokenPlan.enclose witness.span
      (moduleRefExternalOutputCorePlan atToken library next rest))) :
    TokenPlanEvidence candidate
      (PhysicalTokens tokens origin finish) := by
  have physicalEvidence := inputEvidence.candidate_eq
    (moduleRefExternalSourceInput_tokenPlan?
      atToken library dot next rest)
  rcases physicalEvidence with ⟨plan, candidateEq, relation⟩
  simp only [Option.some.injEq] at candidateEq
  subst plan
  have coreRelation :=
    moduleRefExternalPhysicalPlan_listMatches_toCore
      atToken library dot next rest relation
  rw [moduleRefExternalPhysicalCorePlan_eq_outputCorePlan
    lexicallyExact atToken library next rest libraryProjects
      nextProjects restProjects] at coreRelation
  have coreEvidence := TokenPlanEvidence.some coreRelation
  have enclosed := TokenPlanEvidence.enclose coreEvidence
    (by
      intro plan success
      simp only [Option.some.injEq] at success
      subst plan
      exact moduleRefExternalOutputCorePlan_wellAnchored
        atToken library next rest)
    witness.consumed
  exact enclosed.candidate_eq outputEq.symm

private theorem PathSegmentProjects.render_eq_spelling
    {file : WorkspaceFile} {tokens : List Token}
    {matched : MatchedTerminal file tokens (.category .pathComponent)}
    {spelling : String} {parsed : PathSegment}
    (projects : PathSegmentProjects matched spelling parsed) :
    parsed.render = spelling := by
  rcases projects with ⟨token, valueEq, payloadShape, parseEq⟩
  exact PathSegment.text_eq_of_parse_eq_some parseEq

private theorem RuleReduction.MarkerProjects.standardRoot_projects
    {file : WorkspaceFile} {tokens : List Token}
    {matched : MatchedTerminal file tokens (.category .pathComponent)}
    (projects : RuleReduction.MarkerProjects file tokens
      matched .standardRoot) :
    ∃ parsed, PathSegmentProjects matched "std" parsed := by
  cases projects with
  | standardRoot _ parsed pathProjects => exact ⟨parsed, pathProjects⟩

private theorem RuleReduction.MarkerProjects.libraryRoot_projects
    {file : WorkspaceFile} {tokens : List Token}
    {matched : MatchedTerminal file tokens (.category .pathComponent)}
    (projects : RuleReduction.MarkerProjects file tokens
      matched .libraryRoot) :
    ∃ parsed, PathSegmentProjects matched "lib" parsed := by
  cases projects with
  | libraryRoot _ parsed pathProjects => exact ⟨parsed, pathProjects⟩

/-- Module-reference reductions preserve exact tokens when the retained token
stream includes canonical lexical classification. -/
theorem moduleRef_tokenPlanSound_of_tokensLexicallyExact
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .moduleRef)}
    {output : RuleValue .moduleRef}
    (lexicallyExact : TokensLexicallyExact file tokens)
    (reduces : RuleReduction file tokens .moduleRef
      origin finish input output)
    (inputEvidence : TokenPlanEvidence
      (input.tokenPlan? sourceRuleTokenPlanLayout)
      (PhysicalTokens tokens origin finish)) :
    TokenPlanEvidence
      (ruleTokenPlan? .moduleRef output)
      (PhysicalTokens tokens origin finish) := by
  cases reduces with
  | moduleRefExternal origin finish atToken library dot next rest
      atMarker libraryProjects nextProjects restProjects witness =>
      change TokenPlanEvidence
        ((moduleRefExternalSourceInput atToken library dot next rest).tokenPlan?
          sourceRuleTokenPlanLayout)
        (PhysicalTokens tokens origin finish) at inputEvidence
      exact moduleRefExternalEvidence lexicallyExact atToken library dot next
        rest libraryProjects nextProjects restProjects witness inputEvidence
        (moduleRefExternalOutput_tokenPlan?
          atToken library next rest atMarker witness)
  | moduleRefStandard origin finish first rest rootMarker restProjects
      witness =>
      rcases rootMarker.standardRoot_projects with
        ⟨parsed, firstProjects⟩
      change TokenPlanEvidence
        ((moduleRefRelativeSourceInput
          (moduleRefMarkerData first "std" parsed) rest).tokenPlan?
            sourceRuleTokenPlanLayout)
        (PhysicalTokens tokens origin finish) at inputEvidence
      exact moduleRefPathEvidence lexicallyExact
        (moduleRefMarkerData first "std" parsed) rest firstProjects
        restProjects witness inputEvidence
        (moduleRefStandardOutput_tokenPlan?
          first parsed firstProjects rest rootMarker witness)
  | moduleRefLibraryRoot origin finish first nextDot next remaining
      rootMarker nextProjects remainingProjects witness =>
      rcases rootMarker.libraryRoot_projects with
        ⟨parsed, firstProjects⟩
      have allProjects : ∀ entry,
          entry ∈ ((nextDot, next) :: remaining) →
          PathSegmentProjects entry.2.matched
            entry.2.spelling entry.2.parsed := by
        intro entry member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact nextProjects
        · exact remainingProjects entry member
      change TokenPlanEvidence
        ((moduleRefRelativeSourceInput
          (moduleRefMarkerData first "lib" parsed)
          ((nextDot, next) :: remaining)).tokenPlan?
            sourceRuleTokenPlanLayout)
        (PhysicalTokens tokens origin finish) at inputEvidence
      exact moduleRefPathEvidence lexicallyExact
        (moduleRefMarkerData first "lib" parsed)
        ((nextDot, next) :: remaining) firstProjects allProjects witness
        inputEvidence (moduleRefLibraryRootOutput_tokenPlan?
          first parsed firstProjects nextDot next remaining rootMarker witness)
  | moduleRefRelativeLibraryEmpty origin finish first firstProjects
      libraryMarker witness =>
      have renderEq := firstProjects.render_eq_spelling
      rcases libraryMarker.libraryRoot_projects with
        ⟨parsed, markerProjects⟩
      have spellingEq : first.spelling = "lib" :=
        (PathSegmentProjects.functional firstProjects markerProjects).1
      have notStandard : first.spelling ≠ "std" := by
        rw [spellingEq]
        decide
      have shapeExact := moduleRefRelative_shapeExact first [] renderEq
        notStandard (Or.inr rfl)
      change TokenPlanEvidence
        ((moduleRefRelativeSourceInput first []).tokenPlan?
          sourceRuleTokenPlanLayout)
        (PhysicalTokens tokens origin finish) at inputEvidence
      exact moduleRefPathEvidence lexicallyExact first [] firstProjects
        (by simp) witness inputEvidence
        (moduleRefRelativeOutput_tokenPlan?
          first [] witness shapeExact)
  | moduleRefRelativeOther origin finish first rest firstProjects
      restProjects notStandard notLibrary witness =>
      have renderEq := firstProjects.render_eq_spelling
      have shapeExact := moduleRefRelative_shapeExact first rest renderEq
        notStandard (Or.inl notLibrary)
      change TokenPlanEvidence
        ((moduleRefRelativeSourceInput first rest).tokenPlan?
          sourceRuleTokenPlanLayout)
        (PhysicalTokens tokens origin finish) at inputEvidence
      exact moduleRefPathEvidence lexicallyExact first rest firstProjects
        restProjects witness inputEvidence
        (moduleRefRelativeOutput_tokenPlan?
          first rest witness shapeExact)

/-- Coherent complete module-reference roots receive lexical exactness from
the parser callback and therefore satisfy the source token plan. -/
theorem moduleRef_coherentTokenPlanSound :
    CoherentGrammarRuleTokenPlanSound sourceRuleTokenPlanLayout
      .moduleRef := by
  intro file tokens memo correct final origin finish context priorValues output
    complete _owned lexicallyExact _coherentPrefix reduces inputEvidence
  apply moduleRef_tokenPlanSound_of_tokensLexicallyExact
    lexicallyExact reduces
  apply inputEvidence.candidate_eq
  symm
  rw [RootAction.unpack_tokenPlan?]
  simpa only [CanonicalCompleteRootItem] using
    (PrefixValues.tokenPlan?_fullValue sourceRuleTokenPlanLayout
      (CanonicalCompleteRootItem tokens .moduleRef origin finish context)
      complete priorValues)

end Solcore.Surface.Multi
