import Solcore.Surface.Multi.ExactTokenEvidence
import Solcore.Surface.Multi.ExactTokenRuleLayout

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- Viewing a freshly built choice recovers its dependent branch value. -/
@[simp] theorem EbnfValue.choiceView_choice
    {file : WorkspaceFile} {tokens : List Token}
    (branches : List EbnfExpr)
    (value : (branch : Fin branches.length) ×
      EbnfValue file tokens (branches.get branch)) :
    EbnfValue.choiceView branches (EbnfValue.choice branches value) =
      value := by
  simp [EbnfValue.choiceView, EbnfValue.choice, cast_cast]

/-- Choice plans can be reduced through the canonical dependent view without
mentioning the proof carried by the selected finite index. -/
theorem EbnfValue.tokenPlan?_choiceView
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (branches : List EbnfExpr)
    (value : EbnfValue file tokens (.choice branches)) :
    value.tokenPlan? layout =
      (EbnfValue.choiceView branches value).2.tokenPlan? layout := by
  calc
    value.tokenPlan? layout =
        (EbnfValue.choice branches
          (EbnfValue.choiceView branches value)).tokenPlan? layout := by
      rw [EbnfValue.choice_of_view branches value]
    _ = (EbnfValue.choiceView branches value).2.tokenPlan? layout :=
      EbnfValue.tokenPlan?_choice layout branches
        (EbnfValue.choiceView branches value)

/-- A checked symbol scan contributes its exact retained spelling and span. -/
@[simp] theorem MatchedTerminal.physicalTokenPlan_symbol
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

/-- Literal source reductions preserve complete token-plan evidence. -/
theorem RuleReduction.literal_tokenPlanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .literal)}
    {output : RuleValue .literal}
    (reduces : RuleReduction file tokens .literal
      origin finish input output)
    (inputEvidence : TokenPlanEvidence
      (input.tokenPlan? sourceRuleTokenPlanLayout)
      (PhysicalTokens tokens origin finish)) :
    TokenPlanEvidence
      (ruleTokenPlan? .literal output)
      (PhysicalTokens tokens origin finish) := by
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | literalDecimal origin finish terminal payload projects =>
      change EbnfValue file tokens (.choice [
        .atom (.terminal (.category .decimalLiteral)),
        .atom (.terminal (.category .hexadecimalLiteral)),
        .atom (.terminal (.category .stringLiteral))]) at input
      rw [← inputEq] at inputEvidence
      apply inputEvidence.candidate_eq
      change TokenPlanFamily sourceRuleTokenPlanLayout file tokens
        (.expression (.choice [
          .atom (.terminal (.category .decimalLiteral)),
          .atom (.terminal (.category .hexadecimalLiteral)),
          .atom (.terminal (.category .stringLiteral))])) input = _
      rcases projects with ⟨token, valueEq, branch⟩
      rcases branch with branch | branch | branch
      · rcases branch with ⟨_, spelling, digits, payloadEq, literalEq⟩
        subst payload
        calc
          _ = (EbnfValue.choiceView _ input).2.tokenPlan?
                sourceRuleTokenPlanLayout :=
              EbnfValue.tokenPlan?_choiceView
                sourceRuleTokenPlanLayout _ input
          _ = _ := by
              rw [inputEq]
              simp only [EbnfExpr.children]
              rw [EbnfValue.choiceView_choice]
              simp [ruleTokenPlan?, literalTokenPlan,
                RuleReduction.terminalLoc,
                MatchedTerminal.physicalTokenPlan, valueEq, payloadEq]
      · simp at branch
      · simp at branch
  | literalHexadecimal origin finish terminal payload projects =>
      change EbnfValue file tokens (.choice [
        .atom (.terminal (.category .decimalLiteral)),
        .atom (.terminal (.category .hexadecimalLiteral)),
        .atom (.terminal (.category .stringLiteral))]) at input
      rw [← inputEq] at inputEvidence
      apply inputEvidence.candidate_eq
      change TokenPlanFamily sourceRuleTokenPlanLayout file tokens
        (.expression (.choice [
          .atom (.terminal (.category .decimalLiteral)),
          .atom (.terminal (.category .hexadecimalLiteral)),
          .atom (.terminal (.category .stringLiteral))])) input = _
      rcases projects with ⟨token, valueEq, branch⟩
      rcases branch with branch | branch | branch
      · simp at branch
      · rcases branch with ⟨_, spelling, digits, payloadEq, literalEq⟩
        subst payload
        calc
          _ = (EbnfValue.choiceView _ input).2.tokenPlan?
                sourceRuleTokenPlanLayout :=
              EbnfValue.tokenPlan?_choiceView
                sourceRuleTokenPlanLayout _ input
          _ = _ := by
              rw [inputEq]
              simp only [EbnfExpr.children]
              rw [EbnfValue.choiceView_choice]
              simp [ruleTokenPlan?, literalTokenPlan,
                RuleReduction.terminalLoc,
                MatchedTerminal.physicalTokenPlan, valueEq, payloadEq]
      · simp at branch
  | literalString origin finish terminal payload projects =>
      change EbnfValue file tokens (.choice [
        .atom (.terminal (.category .decimalLiteral)),
        .atom (.terminal (.category .hexadecimalLiteral)),
        .atom (.terminal (.category .stringLiteral))]) at input
      rw [← inputEq] at inputEvidence
      apply inputEvidence.candidate_eq
      change TokenPlanFamily sourceRuleTokenPlanLayout file tokens
        (.expression (.choice [
          .atom (.terminal (.category .decimalLiteral)),
          .atom (.terminal (.category .hexadecimalLiteral)),
          .atom (.terminal (.category .stringLiteral))])) input = _
      rcases projects with ⟨token, valueEq, branch⟩
      rcases branch with branch | branch | branch
      · simp at branch
      · simp at branch
      · rcases branch with ⟨_, spelling, decoded, payloadEq, literalEq⟩
        subst payload
        calc
          _ = (EbnfValue.choiceView _ input).2.tokenPlan?
                sourceRuleTokenPlanLayout :=
              EbnfValue.tokenPlan?_choiceView
                sourceRuleTokenPlanLayout _ input
          _ = _ := by
              rw [inputEq]
              simp only [EbnfExpr.children]
              rw [EbnfValue.choiceView_choice]
              simp [ruleTokenPlan?, literalTokenPlan,
                RuleReduction.terminalLoc,
                MatchedTerminal.physicalTokenPlan, valueEq, payloadEq]

private theorem assignmentOperatorChoiceInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (value : (branch : Fin
      (EbnfExpr.children (m2cV1.rhs .assignmentOperator)).length) ×
      EbnfValue file tokens
        ((EbnfExpr.children
          (m2cV1.rhs .assignmentOperator)).get branch))
    {plan : TokenPlan}
    (childEq : value.2.tokenPlan? sourceRuleTokenPlanLayout = some plan) :
    (EbnfValue.choice
      (EbnfExpr.children (m2cV1.rhs .assignmentOperator))
      value).tokenPlan? sourceRuleTokenPlanLayout = some plan :=
  (EbnfValue.tokenPlan?_choice
    sourceRuleTokenPlanLayout _ value).trans childEq

/-- Assignment-operator source reductions preserve complete token-plan
evidence for all seven retained symbols. -/
theorem RuleReduction.assignmentOperator_tokenPlanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .assignmentOperator)}
    {output : RuleValue .assignmentOperator}
    (reduces : RuleReduction file tokens .assignmentOperator
      origin finish input output)
    (inputEvidence : TokenPlanEvidence
      (input.tokenPlan? sourceRuleTokenPlanLayout)
      (PhysicalTokens tokens origin finish)) :
    TokenPlanEvidence
      (ruleTokenPlan? .assignmentOperator output)
      (PhysicalTokens tokens origin finish) := by
  cases reduces with
  | assignmentOperatorEqual _ _ terminal =>
      have candidateEq := assignmentOperatorChoiceInput_tokenPlan?
        (value := ⟨⟨0, by decide⟩,
          EbnfValue.terminalAtom (.symbol .equal) terminal⟩)
        (EbnfValue.tokenPlan?_terminalAtom
          sourceRuleTokenPlanLayout _ _)
      have evidence := inputEvidence.candidate_eq
        candidateEq
      simpa [ruleTokenPlan?, assignmentOperatorTokenPlan,
        RuleReduction.assignmentOperator, RuleReduction.terminalLoc]
        using evidence
  | assignmentOperatorAddEqual _ _ terminal =>
      have candidateEq := assignmentOperatorChoiceInput_tokenPlan?
        (value := ⟨⟨1, by decide⟩,
          EbnfValue.terminalAtom (.symbol .plusEqual) terminal⟩)
        (EbnfValue.tokenPlan?_terminalAtom
          sourceRuleTokenPlanLayout _ _)
      have evidence := inputEvidence.candidate_eq candidateEq
      simpa [ruleTokenPlan?, assignmentOperatorTokenPlan,
        RuleReduction.assignmentOperator, RuleReduction.terminalLoc]
        using evidence
  | assignmentOperatorSubtractEqual _ _ terminal =>
      have candidateEq := assignmentOperatorChoiceInput_tokenPlan?
        (value := ⟨⟨2, by decide⟩,
          EbnfValue.terminalAtom (.symbol .minusEqual) terminal⟩)
        (EbnfValue.tokenPlan?_terminalAtom
          sourceRuleTokenPlanLayout _ _)
      have evidence := inputEvidence.candidate_eq candidateEq
      simpa [ruleTokenPlan?, assignmentOperatorTokenPlan,
        RuleReduction.assignmentOperator, RuleReduction.terminalLoc]
        using evidence
  | assignmentOperatorBitXorEqual _ _ terminal =>
      have candidateEq := assignmentOperatorChoiceInput_tokenPlan?
        (value := ⟨⟨3, by decide⟩,
          EbnfValue.terminalAtom (.symbol .caretEqual) terminal⟩)
        (EbnfValue.tokenPlan?_terminalAtom
          sourceRuleTokenPlanLayout _ _)
      have evidence := inputEvidence.candidate_eq candidateEq
      simpa [ruleTokenPlan?, assignmentOperatorTokenPlan,
        RuleReduction.assignmentOperator, RuleReduction.terminalLoc]
        using evidence
  | assignmentOperatorBitAndEqual _ _ terminal =>
      have candidateEq := assignmentOperatorChoiceInput_tokenPlan?
        (value := ⟨⟨4, by decide⟩,
          EbnfValue.terminalAtom (.symbol .ampEqual) terminal⟩)
        (EbnfValue.tokenPlan?_terminalAtom
          sourceRuleTokenPlanLayout _ _)
      have evidence := inputEvidence.candidate_eq candidateEq
      simpa [ruleTokenPlan?, assignmentOperatorTokenPlan,
        RuleReduction.assignmentOperator, RuleReduction.terminalLoc]
        using evidence
  | assignmentOperatorBitOrEqual _ _ terminal =>
      have candidateEq := assignmentOperatorChoiceInput_tokenPlan?
        (value := ⟨⟨5, by decide⟩,
          EbnfValue.terminalAtom (.symbol .pipeEqual) terminal⟩)
        (EbnfValue.tokenPlan?_terminalAtom
          sourceRuleTokenPlanLayout _ _)
      have evidence := inputEvidence.candidate_eq candidateEq
      simpa [ruleTokenPlan?, assignmentOperatorTokenPlan,
        RuleReduction.assignmentOperator, RuleReduction.terminalLoc]
        using evidence
  | assignmentOperatorModuloEqual _ _ terminal =>
      have candidateEq := assignmentOperatorChoiceInput_tokenPlan?
        (value := ⟨⟨6, by decide⟩,
          EbnfValue.terminalAtom (.symbol .percentEqual) terminal⟩)
        (EbnfValue.tokenPlan?_terminalAtom
          sourceRuleTokenPlanLayout _ _)
      have evidence := inputEvidence.candidate_eq candidateEq
      simpa [ruleTokenPlan?, assignmentOperatorTokenPlan,
        RuleReduction.assignmentOperator, RuleReduction.terminalLoc]
        using evidence

private abbrev QualifiedNameSourceEntry
    (file : WorkspaceFile) (tokens : List Token) :=
  MatchedTerminal file tokens (.symbol .dot) ×
    RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier

private abbrev qualifiedNameTailExpression : EbnfExpr :=
  .group (.sequence [
    .atom (.terminal (.symbol .dot)),
    .atom (.terminal (.category .identifier))
  ])

private def qualifiedNameTailValue
    {file : WorkspaceFile} {tokens : List Token}
    (entry : QualifiedNameSourceEntry file tokens) :
    EbnfValue file tokens qualifiedNameTailExpression :=
  EbnfValue.group _ <| EbnfValue.sequence _ <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .dot) entry.1) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom
        (.category .identifier) entry.2.matched) <|
    EbnfValues.nil

private def qualifiedNameSequenceInput
    {file : WorkspaceFile} {tokens : List Token}
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (rest : List (QualifiedNameSourceEntry file tokens)) :=
  EbnfValue.sequence [
      .atom (.terminal (.category .identifier)),
      .star qualifiedNameTailExpression
    ] <|
    EbnfValues.cons
      (.atom (.terminal (.category .identifier)))
      [.star qualifiedNameTailExpression]
      (EbnfValue.terminalAtom
        (.category .identifier) first.matched) <|
    EbnfValues.cons (.star qualifiedNameTailExpression) []
      (EbnfValue.star qualifiedNameTailExpression
        (rest.map qualifiedNameTailValue)) <|
    EbnfValues.nil

private def qualifiedNameSourceInput
    {file : WorkspaceFile} {tokens : List Token}
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (rest : List (QualifiedNameSourceEntry file tokens)) :
    EbnfValue file tokens (m2cV1.rhs .qualifiedName) :=
  EbnfValue.transport (by rfl) <|
    qualifiedNameSequenceInput first rest

private def qualifiedNameTailPhysicalPlan
    {file : WorkspaceFile} {tokens : List Token}
    (entry : QualifiedNameSourceEntry file tokens) : TokenPlan :=
  entry.1.physicalTokenPlan.append entry.2.matched.physicalTokenPlan

private def qualifiedNamePhysicalPlan
    {file : WorkspaceFile} {tokens : List Token}
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (rest : List (QualifiedNameSourceEntry file tokens)) : TokenPlan :=
  first.matched.physicalTokenPlan.append <|
    .concat (rest.map qualifiedNameTailPhysicalPlan)

@[simp] private theorem qualifiedNameTailValue_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (entry : QualifiedNameSourceEntry file tokens) :
    (qualifiedNameTailValue entry).tokenPlan?
        sourceRuleTokenPlanLayout =
      some (qualifiedNameTailPhysicalPlan entry) := by
  simp [qualifiedNameTailValue, qualifiedNameTailPhysicalPlan]

@[simp] private theorem qualifiedNameTailValues_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (rest : List (QualifiedNameSourceEntry file tokens)) :
    (rest.map qualifiedNameTailValue).mapM
        (fun value => value.tokenPlan? sourceRuleTokenPlanLayout) =
      some (rest.map qualifiedNameTailPhysicalPlan) := by
  induction rest with
  | nil => rfl
  | cons entry rest induction =>
      simp [induction]

private theorem qualifiedNameSourceInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (rest : List (QualifiedNameSourceEntry file tokens)) :
    (qualifiedNameSourceInput first rest).tokenPlan?
        sourceRuleTokenPlanLayout =
      some (qualifiedNamePhysicalPlan first rest) := by
  unfold qualifiedNameSourceInput
  rw [EbnfValue.tokenPlan?_transport]
  unfold qualifiedNameSequenceInput
  rw [EbnfValue.tokenPlan?_sequence]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_terminalAtom]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_star]
  rw [qualifiedNameTailValues_tokenPlan?]
  rw [EbnfValues.tokenPlan?_nil]
  simp [qualifiedNamePhysicalPlan]

private theorem identifierPhysicalTokenPlan_eq_identifierPlan
    {file : WorkspaceFile} {tokens : List Token}
    (matched : MatchedTerminal file tokens (.category .identifier))
    (spelling : String) (parsed : Identifier)
    (projects : IdentifierProjects matched spelling parsed) :
    matched.physicalTokenPlan =
      identifierPlan (RuleReduction.terminalLoc matched parsed) := by
  rcases projects with ⟨token, valueEq, payloadEq, parseEq⟩
  have spellingEq : spelling = parsed.render := by
    unfold Identifier.parse at parseEq
    split at parseEq
    · have parsedEq :
          ({ text := spelling, valid := by assumption } : Identifier) =
            parsed :=
        Option.some.inj parseEq
      simpa [Identifier.render] using congrArg Identifier.render parsedEq
    · simp at parseEq
  simp [MatchedTerminal.physicalTokenPlan, identifierPlan,
    RuleReduction.terminalLoc, valueEq, payloadEq, spellingEq]

private def qualifiedNameTailPlainPlan
    {file : WorkspaceFile} {tokens : List Token}
    (entry : QualifiedNameSourceEntry file tokens) : TokenPlan :=
  (TokenPlan.plain (.symbol .dot)).append
    entry.2.matched.physicalTokenPlan

private def qualifiedNamePhysicalCorePlan
    {file : WorkspaceFile} {tokens : List Token}
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (rest : List (QualifiedNameSourceEntry file tokens)) : TokenPlan :=
  first.matched.physicalTokenPlan.append <|
    .concat (rest.map qualifiedNameTailPlainPlan)

private theorem qualifiedNameTailPhysicalPlan_listMatches_toPlain
    {file : WorkspaceFile} {tokens : List Token}
    (entry : QualifiedNameSourceEntry file tokens)
    {actual : List Token}
    (relation : TokenSlot.ListMatches
      (qualifiedNameTailPhysicalPlan entry).slots actual) :
    TokenSlot.ListMatches
      (qualifiedNameTailPlainPlan entry).slots actual := by
  unfold qualifiedNameTailPhysicalPlan at relation
  unfold qualifiedNameTailPlainPlan
  rw [MatchedTerminal.physicalTokenPlan_symbol] at relation
  change TokenSlot.ListMatches
    (.required (ExpectedToken.exact (.symbol .dot) entry.1.span) ::
      entry.2.matched.physicalTokenPlan.slots) actual at relation
  change TokenSlot.ListMatches
    (.required (ExpectedToken.plain (.symbol .dot)) ::
      entry.2.matched.physicalTokenPlan.slots) actual
  exact relation.requiredHeadToPlain

private theorem qualifiedNameTailPlans_listMatches_toPlain
    {file : WorkspaceFile} {tokens : List Token}
    (rest : List (QualifiedNameSourceEntry file tokens))
    {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat
        (rest.map qualifiedNameTailPhysicalPlan)).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.concat
        (rest.map qualifiedNameTailPlainPlan)).slots actual := by
  induction rest generalizing actual with
  | nil => exact relation
  | cons entry rest induction =>
      change TokenSlot.ListMatches
        ((qualifiedNameTailPhysicalPlan entry).slots ++
          (TokenPlan.concat
            (rest.map qualifiedNameTailPhysicalPlan)).slots) actual
        at relation
      rcases relation.split_append with
        ⟨headActual, tailActual, actualEq, headRelation, tailRelation⟩
      change TokenSlot.ListMatches
        ((qualifiedNameTailPlainPlan entry).slots ++
          (TokenPlan.concat
            (rest.map qualifiedNameTailPlainPlan)).slots) actual
      rw [actualEq]
      exact (qualifiedNameTailPhysicalPlan_listMatches_toPlain
        entry headRelation).append (induction tailRelation)

private theorem qualifiedNamePhysicalPlan_listMatches_toCore
    {file : WorkspaceFile} {tokens : List Token}
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (rest : List (QualifiedNameSourceEntry file tokens))
    {actual : List Token}
    (relation : TokenSlot.ListMatches
      (qualifiedNamePhysicalPlan first rest).slots actual) :
    TokenSlot.ListMatches
      (qualifiedNamePhysicalCorePlan first rest).slots actual := by
  unfold qualifiedNamePhysicalPlan at relation
  unfold qualifiedNamePhysicalCorePlan
  rcases relation.split_append with
    ⟨headActual, tailActual, actualEq, headRelation, tailRelation⟩
  rw [actualEq]
  exact headRelation.append
    (qualifiedNameTailPlans_listMatches_toPlain rest tailRelation)

private def qualifiedNameTailOutputPlan
    {file : WorkspaceFile} {tokens : List Token}
    (entry : QualifiedNameSourceEntry file tokens) : TokenPlan :=
  (TokenPlan.plain (.symbol .dot)).append <|
    identifierPlan
      (RuleReduction.terminalLoc entry.2.matched entry.2.parsed)

private def qualifiedNameOutputCorePlan
    {file : WorkspaceFile} {tokens : List Token}
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (rest : List (QualifiedNameSourceEntry file tokens)) : TokenPlan :=
  (identifierPlan
    (RuleReduction.terminalLoc first.matched first.parsed)).append <|
      .concat (rest.map qualifiedNameTailOutputPlan)

private theorem qualifiedNameTailPlainPlan_eq_outputPlan
    {file : WorkspaceFile} {tokens : List Token}
    (entry : QualifiedNameSourceEntry file tokens)
    (projects : IdentifierProjects entry.2.matched
      entry.2.spelling entry.2.parsed) :
    qualifiedNameTailPlainPlan entry =
      qualifiedNameTailOutputPlan entry := by
  unfold qualifiedNameTailPlainPlan qualifiedNameTailOutputPlan
  rw [identifierPhysicalTokenPlan_eq_identifierPlan
    entry.2.matched entry.2.spelling entry.2.parsed projects]

private theorem qualifiedNameTailPlainPlans_eq_outputPlans
    {file : WorkspaceFile} {tokens : List Token}
    (rest : List (QualifiedNameSourceEntry file tokens)) :
    (∀ entry, entry ∈ rest →
      IdentifierProjects entry.2.matched
        entry.2.spelling entry.2.parsed) →
    rest.map qualifiedNameTailPlainPlan =
      rest.map qualifiedNameTailOutputPlan := by
  induction rest with
  | nil => intro _projects; rfl
  | cons entry rest induction =>
      intro projects
      simp only [List.map_cons]
      rw [qualifiedNameTailPlainPlan_eq_outputPlan entry
        (projects entry (by simp))]
      rw [induction (by
        intro candidate member
        exact projects candidate (by simp [member]))]

private theorem qualifiedNamePhysicalCorePlan_eq_outputCorePlan
    {file : WorkspaceFile} {tokens : List Token}
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (rest : List (QualifiedNameSourceEntry file tokens))
    (firstProjects : IdentifierProjects first.matched
      first.spelling first.parsed)
    (restProjects : ∀ entry, entry ∈ rest →
      IdentifierProjects entry.2.matched
        entry.2.spelling entry.2.parsed) :
    qualifiedNamePhysicalCorePlan first rest =
      qualifiedNameOutputCorePlan first rest := by
  unfold qualifiedNamePhysicalCorePlan qualifiedNameOutputCorePlan
  rw [identifierPhysicalTokenPlan_eq_identifierPlan
    first.matched first.spelling first.parsed firstProjects]
  rw [qualifiedNameTailPlainPlans_eq_outputPlans rest restProjects]

private theorem qualifiedNameOutputCorePlan_wellAnchored
    {file : WorkspaceFile} {tokens : List Token}
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (rest : List (QualifiedNameSourceEntry file tokens)) :
    (qualifiedNameOutputCorePlan first rest).WellAnchored := by
  unfold qualifiedNameOutputCorePlan
  apply TokenPlan.WellAnchored.append
  · unfold identifierPlan
    exact TokenPlan.WellAnchored.exact _ _
  · apply TokenPlan.WellAnchored.concat
    intro plan member
    simp only [List.mem_map] at member
    rcases member with ⟨entry, _entryMember, rfl⟩
    unfold qualifiedNameTailOutputPlan
    apply TokenPlan.WellAnchored.append
    · exact TokenPlan.WellAnchored.plain _
    · unfold identifierPlan
      exact TokenPlan.WellAnchored.exact _ _

private theorem qualifiedNameTailOutputPlans_eq
    {file : WorkspaceFile} {tokens : List Token}
    (rest : List (QualifiedNameSourceEntry file tokens)) :
    rest.map qualifiedNameTailOutputPlan =
      rest.map fun entry =>
        (TokenPlan.plain (.symbol .dot)).append <|
          identifierPlan (RuleReduction.terminalLoc
            entry.2.matched entry.2.parsed) := by
  induction rest with
  | nil => rfl
  | cons entry rest induction =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨rfl, induction⟩

private theorem qualifiedNameOutput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (rest : List (QualifiedNameSourceEntry file tokens))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    ruleTokenPlan? .qualifiedName
        (sourceLoc witness ({
          components := {
            head := RuleReduction.terminalLoc
              first.matched first.parsed
            tail := rest.map fun entry =>
              RuleReduction.terminalLoc
                entry.2.matched entry.2.parsed
          }
        } : QualifiedNamePayload)) =
      some (TokenPlan.enclose witness.span
        (qualifiedNameOutputCorePlan first rest)) := by
  calc
    _ = some (TokenPlan.enclose witness.span <|
          (identifierPlan (RuleReduction.terminalLoc
            first.matched first.parsed)).append <|
          .concat <| rest.map fun entry =>
            (TokenPlan.plain (.symbol .dot)).append <|
              identifierPlan (RuleReduction.terminalLoc
                entry.2.matched entry.2.parsed)) := by
        simp [ruleTokenPlan?, qualifiedNamePlan,
          sourceLoc, List.map_map, Function.comp_def]
    _ = _ := by
      unfold qualifiedNameOutputCorePlan
      rw [qualifiedNameTailOutputPlans_eq rest]

/-- Qualified-name reductions retain exact identifier tokens and safely
forget only the endpoint constraints of separating dots. -/
theorem RuleReduction.qualifiedName_tokenPlanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .qualifiedName)}
    {output : RuleValue .qualifiedName}
    (reduces : RuleReduction file tokens .qualifiedName
      origin finish input output)
    (inputEvidence : TokenPlanEvidence
      (input.tokenPlan? sourceRuleTokenPlanLayout)
      (PhysicalTokens tokens origin finish)) :
    TokenPlanEvidence
      (ruleTokenPlan? .qualifiedName output)
      (PhysicalTokens tokens origin finish) := by
  cases reduces with
  | qualifiedName origin finish first rest firstProjects restProjects witness =>
      change TokenPlanEvidence
        ((qualifiedNameSourceInput first rest).tokenPlan?
          sourceRuleTokenPlanLayout)
        (PhysicalTokens tokens origin finish) at inputEvidence
      have physicalEvidence := inputEvidence.candidate_eq
        (qualifiedNameSourceInput_tokenPlan? first rest)
      rcases physicalEvidence with ⟨plan, candidateEq, relation⟩
      simp only [Option.some.injEq] at candidateEq
      subst plan
      have coreRelation :=
        qualifiedNamePhysicalPlan_listMatches_toCore first rest relation
      rw [qualifiedNamePhysicalCorePlan_eq_outputCorePlan
        first rest firstProjects restProjects] at coreRelation
      have coreEvidence := TokenPlanEvidence.some coreRelation
      have enclosed := TokenPlanEvidence.enclose coreEvidence
        (by
          intro plan candidateEq
          simp only [Option.some.injEq] at candidateEq
          subst plan
          exact qualifiedNameOutputCorePlan_wellAnchored first rest)
        witness.consumed
      exact enclosed.candidate_eq
        (qualifiedNameOutput_tokenPlan? first rest witness).symm

end Solcore.Surface.Multi
