import Solcore.Surface.Multi.ExactTokenAnchoring
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

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

private theorem matchedPragmaName_physicalTokenPlan
    {file : WorkspaceFile} {tokens : List Token} (kind : PragmaKind)
    (matched : MatchedTerminal file tokens (.pragmaName kind)) :
    matched.physicalTokenPlan =
      TokenPlan.exact (.pragmaName kind) matched.span := by
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

private theorem TokenSlot.ListMatches.fixedBookendsToPlain
    {firstKind retainedKind lastKind : TokenKind}
    {firstSpan retainedSpan lastSpan : SourceSpan}
    {middle : TokenPlan} {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat [
        TokenPlan.exact firstKind firstSpan,
        TokenPlan.exact retainedKind retainedSpan,
        middle,
        TokenPlan.exact lastKind lastSpan]).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.concat [
        TokenPlan.plain firstKind,
        TokenPlan.exact retainedKind retainedSpan,
        middle,
        TokenPlan.plain lastKind]).slots actual := by
  change TokenSlot.ListMatches
    (.required (ExpectedToken.exact firstKind firstSpan) ::
      .required (ExpectedToken.exact retainedKind retainedSpan) ::
      middle.slots ++
        [.required (ExpectedToken.exact lastKind lastSpan)]) actual
    at relation
  change TokenSlot.ListMatches
    (.required (ExpectedToken.plain firstKind) ::
      .required (ExpectedToken.exact retainedKind retainedSpan) ::
      middle.slots ++
        [.required (ExpectedToken.plain lastKind)]) actual
  cases relation with
  | required firstMatch rest =>
      cases rest with
      | required retainedMatch remaining =>
          rcases remaining.split_append with
            ⟨middleActual, lastActual, actualEq,
              middleRelation, lastRelation⟩
          rw [actualEq]
          exact .required firstMatch.toPlain <|
            .required retainedMatch <|
              middleRelation.append lastRelation.requiredHeadToPlain

local syntax "pragmaTargetsAtom!" : term
local macro_rules
  | `(pragmaTargetsAtom!) =>
      `(.optional (.list1
        (.atom (.terminal (.category .identifier)))))

local syntax "pragmaBranchChildren![" term "]" : term
local macro_rules
  | `(pragmaBranchChildren![$kind:term]) =>
      `([.atom (.terminal (.hardKeyword .pragmaKw)),
        .atom (.terminal (.pragmaName $kind)),
        pragmaTargetsAtom!,
        .atom (.terminal (.symbol .semicolon))])

local syntax "pragmaBranches!" : term
local macro_rules
  | `(pragmaBranches!) =>
      `([.sequence pragmaBranchChildren![.noCoverageCondition],
        .sequence pragmaBranchChildren![.noPattersonCondition],
        .sequence pragmaBranchChildren![.noBoundedVariableCondition],
        .sequence pragmaBranchChildren![.noGenericInstanceFor]])

private abbrev pragmaSourceBranches : List EbnfExpr := pragmaBranches!

local syntax "pragmaTargetsValue![" term "]" : term
local macro_rules
  | `(pragmaTargetsValue![$targets:term]) =>
      `(EbnfValue.optional
        (.list1 (.atom (.terminal (.category .identifier))))
        (($targets).map fun values =>
          EbnfValue.list1
            (.atom (.terminal (.category .identifier))) {
              head := EbnfValue.terminalAtom
                (.category .identifier) values.head.matched
              tail := values.tail.map fun name =>
                EbnfValue.terminalAtom
                  (.category .identifier) name.matched
            }))

local syntax "pragmaSequenceValue![" term "," term "," term "," term
  "," term "]" : term
local macro_rules
  | `(pragmaSequenceValue![$kind:term, $pragmaKw:term, $kindToken:term,
      $targets:term, $semicolon:term]) =>
      `(EbnfValue.sequence pragmaBranchChildren![$kind]
        (EbnfValues.cons _ _
          (EbnfValue.terminalAtom (.hardKeyword .pragmaKw) $pragmaKw)
          (EbnfValues.cons _ _
            (EbnfValue.terminalAtom (.pragmaName $kind) $kindToken)
            (EbnfValues.cons _ _
              pragmaTargetsValue![$targets]
              (EbnfValues.cons _ _
                (EbnfValue.terminalAtom (.symbol .semicolon) $semicolon)
                EbnfValues.nil)))))

private def pragmaTargetsPlan
    {file : WorkspaceFile} {tokens : List Token}
    (targets : Option (NonemptyList
      (RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier))) : TokenPlan :=
  match targets with
  | none => TokenPlan.empty
  | some values => TokenPlan.commaSeparated
      (identifierPlan
          (RuleReduction.terminalLoc values.head.matched
            values.head.parsed) ::
        values.tail.map fun name => identifierPlan
          (RuleReduction.terminalLoc name.matched name.parsed))

private theorem pragmaSequenceInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (kind : PragmaKind)
    (pragmaKw : MatchedTerminal file tokens (.hardKeyword .pragmaKw))
    (kindToken : MatchedTerminal file tokens (.pragmaName kind))
    (targets : Option (NonemptyList
      (RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (targetProjects : ∀ values, targets = some values →
      IdentifierProjects values.head.matched
        values.head.spelling values.head.parsed ∧
      ∀ name, name ∈ values.tail →
        IdentifierProjects name.matched name.spelling name.parsed) :
    (pragmaSequenceValue![kind, pragmaKw, kindToken,
      targets, semicolon]).tokenPlan? sourceRuleTokenPlanLayout =
      some (TokenPlan.concat [
        TokenPlan.exact (.hardKeyword .pragmaKw) pragmaKw.span,
        TokenPlan.exact (.pragmaName kind) kindToken.span,
        pragmaTargetsPlan targets,
        TokenPlan.exact (.symbol .semicolon) semicolon.span]) := by
  rw [EbnfValue.tokenPlan?_sequence,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValues.tokenPlan?_cons,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValues.tokenPlan?_nil,
    matchedHardKeyword_physicalTokenPlan .pragmaKw pragmaKw,
    matchedPragmaName_physicalTokenPlan kind kindToken,
    matchedSymbol_physicalTokenPlan .semicolon semicolon]
  cases targets with
  | none =>
      simp [pragmaTargetsPlan, TokenPlan.append]
  | some values =>
      have projects := targetProjects values rfl
      have headPlanEq := matchedIdentifier_physicalTokenPlan
        values.head projects.1
      have tailPlanEq : ∀ name ∈ values.tail,
          name.matched.physicalTokenPlan = identifierPlan
            (RuleReduction.terminalLoc name.matched name.parsed) := by
        intro name member
        exact matchedIdentifier_physicalTokenPlan name
          (projects.2 name member)
      have mappedPlansEq :
          List.mapM (fun name => some name.matched.physicalTokenPlan)
              values.tail =
            some (values.tail.map fun name => identifierPlan
              (RuleReduction.terminalLoc name.matched name.parsed)) := by
        change List.mapM
          (fun name =>
            (pure name.matched.physicalTokenPlan : Option TokenPlan))
          values.tail = _
        rw [List.mapM_pure]
        exact congrArg some (List.map_congr_left tailPlanEq)
      simp only [Option.map_some,
        EbnfValue.tokenPlan?_optional_some,
        EbnfValue.tokenPlan?_list1,
        EbnfValue.tokenPlan?_terminalAtom]
      simp [Function.comp_def, EbnfValue.tokenPlan?_terminalAtom]
      rw [mappedPlansEq, headPlanEq]
      simp [pragmaTargetsPlan, TokenPlan.append]

local syntax "pragmaChoiceValue![" term "," term "," term "," term ","
  term "," term "]" : term
local macro_rules
  | `(pragmaChoiceValue![$branch:term, $kind:term, $pragmaKw:term,
      $kindToken:term, $targets:term, $semicolon:term]) =>
      `(EbnfValue.choice pragmaBranches!
        ⟨⟨$branch, by decide⟩,
          pragmaSequenceValue![$kind, $pragmaKw, $kindToken,
            $targets, $semicolon]⟩)

local syntax "pragmaRootValue![" term "," term "," term "," term ","
  term "," term "]" : term
local macro_rules
  | `(pragmaRootValue![$branch:term, $kind:term, $pragmaKw:term,
      $kindToken:term, $targets:term, $semicolon:term]) =>
      `(EbnfValue.transport (by rfl)
        pragmaChoiceValue![$branch, $kind, $pragmaKw, $kindToken,
          $targets, $semicolon])

private theorem pragmaNoCoverageInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (pragmaKw : MatchedTerminal file tokens (.hardKeyword .pragmaKw))
    (kindToken : MatchedTerminal file tokens
      (.pragmaName .noCoverageCondition))
    (targets : Option (NonemptyList
      (RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (targetProjects : ∀ values, targets = some values →
      IdentifierProjects values.head.matched
        values.head.spelling values.head.parsed ∧
      ∀ name, name ∈ values.tail →
        IdentifierProjects name.matched name.spelling name.parsed) :
    (pragmaRootValue![0, .noCoverageCondition, pragmaKw,
      kindToken, targets, semicolon]).tokenPlan?
        sourceRuleTokenPlanLayout =
      some (TokenPlan.concat [
        TokenPlan.exact (.hardKeyword .pragmaKw) pragmaKw.span,
        TokenPlan.exact (.pragmaName .noCoverageCondition)
          kindToken.span,
        pragmaTargetsPlan targets,
        TokenPlan.exact (.symbol .semicolon) semicolon.span]) := by
  calc
    _ = (pragmaChoiceValue![0, .noCoverageCondition, pragmaKw,
          kindToken, targets, semicolon]).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
    _ = (pragmaSequenceValue![.noCoverageCondition, pragmaKw,
          kindToken, targets, semicolon]).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = _ := pragmaSequenceInput_tokenPlan?
      .noCoverageCondition pragmaKw kindToken targets semicolon
        targetProjects

private theorem pragmaNoPattersonInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (pragmaKw : MatchedTerminal file tokens (.hardKeyword .pragmaKw))
    (kindToken : MatchedTerminal file tokens
      (.pragmaName .noPattersonCondition))
    (targets : Option (NonemptyList
      (RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (targetProjects : ∀ values, targets = some values →
      IdentifierProjects values.head.matched
        values.head.spelling values.head.parsed ∧
      ∀ name, name ∈ values.tail →
        IdentifierProjects name.matched name.spelling name.parsed) :
    (pragmaRootValue![1, .noPattersonCondition, pragmaKw,
      kindToken, targets, semicolon]).tokenPlan?
        sourceRuleTokenPlanLayout =
      some (TokenPlan.concat [
        TokenPlan.exact (.hardKeyword .pragmaKw) pragmaKw.span,
        TokenPlan.exact (.pragmaName .noPattersonCondition)
          kindToken.span,
        pragmaTargetsPlan targets,
        TokenPlan.exact (.symbol .semicolon) semicolon.span]) := by
  calc
    _ = (pragmaChoiceValue![1, .noPattersonCondition, pragmaKw,
          kindToken, targets, semicolon]).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
    _ = (pragmaSequenceValue![.noPattersonCondition, pragmaKw,
          kindToken, targets, semicolon]).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = _ := pragmaSequenceInput_tokenPlan?
      .noPattersonCondition pragmaKw kindToken targets semicolon
        targetProjects

private theorem pragmaNoBoundedVariableInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (pragmaKw : MatchedTerminal file tokens (.hardKeyword .pragmaKw))
    (kindToken : MatchedTerminal file tokens
      (.pragmaName .noBoundedVariableCondition))
    (targets : Option (NonemptyList
      (RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (targetProjects : ∀ values, targets = some values →
      IdentifierProjects values.head.matched
        values.head.spelling values.head.parsed ∧
      ∀ name, name ∈ values.tail →
        IdentifierProjects name.matched name.spelling name.parsed) :
    (pragmaRootValue![2, .noBoundedVariableCondition, pragmaKw,
      kindToken, targets, semicolon]).tokenPlan?
        sourceRuleTokenPlanLayout =
      some (TokenPlan.concat [
        TokenPlan.exact (.hardKeyword .pragmaKw) pragmaKw.span,
        TokenPlan.exact (.pragmaName .noBoundedVariableCondition)
          kindToken.span,
        pragmaTargetsPlan targets,
        TokenPlan.exact (.symbol .semicolon) semicolon.span]) := by
  calc
    _ = (pragmaChoiceValue![2, .noBoundedVariableCondition, pragmaKw,
          kindToken, targets, semicolon]).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
    _ = (pragmaSequenceValue![.noBoundedVariableCondition, pragmaKw,
          kindToken, targets, semicolon]).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = _ := pragmaSequenceInput_tokenPlan?
      .noBoundedVariableCondition pragmaKw kindToken targets semicolon
        targetProjects

private theorem pragmaNoGenericInstanceInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (pragmaKw : MatchedTerminal file tokens (.hardKeyword .pragmaKw))
    (kindToken : MatchedTerminal file tokens
      (.pragmaName .noGenericInstanceFor))
    (targets : Option (NonemptyList
      (RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (targetProjects : ∀ values, targets = some values →
      IdentifierProjects values.head.matched
        values.head.spelling values.head.parsed ∧
      ∀ name, name ∈ values.tail →
        IdentifierProjects name.matched name.spelling name.parsed) :
    (pragmaRootValue![3, .noGenericInstanceFor, pragmaKw,
      kindToken, targets, semicolon]).tokenPlan?
        sourceRuleTokenPlanLayout =
      some (TokenPlan.concat [
        TokenPlan.exact (.hardKeyword .pragmaKw) pragmaKw.span,
        TokenPlan.exact (.pragmaName .noGenericInstanceFor)
          kindToken.span,
        pragmaTargetsPlan targets,
        TokenPlan.exact (.symbol .semicolon) semicolon.span]) := by
  calc
    _ = (pragmaChoiceValue![3, .noGenericInstanceFor, pragmaKw,
          kindToken, targets, semicolon]).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
    _ = (pragmaSequenceValue![.noGenericInstanceFor, pragmaKw,
          kindToken, targets, semicolon]).tokenPlan?
            sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_choice sourceRuleTokenPlanLayout _ _
    _ = _ := pragmaSequenceInput_tokenPlan?
      .noGenericInstanceFor pragmaKw kindToken targets semicolon
        targetProjects

private theorem ruleTokenPlan?_pragmaDecl (declaration : PragmaDecl) :
    ruleTokenPlan? .pragmaDecl declaration =
      pragmaDeclPlan? declaration := by
  rfl

private theorem pragmaDeclPlan?_sourceLoc
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (kind : PragmaKind)
    (kindToken : MatchedTerminal file tokens (.pragmaName kind))
    (targets : Option (NonemptyList
      (RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    pragmaDeclPlan? (sourceLoc witness {
      kind := RuleReduction.terminalLoc kindToken kind
      targets := targets.elim [] fun values =>
        RuleReduction.firstRest (values.map fun name =>
          RuleReduction.terminalLoc name.matched name.parsed)
    }) = some (TokenPlan.enclose witness.span (TokenPlan.concat [
      TokenPlan.plain (.hardKeyword .pragmaKw),
      TokenPlan.exact (.pragmaName kind) kindToken.span,
      pragmaTargetsPlan targets,
      TokenPlan.plain (.symbol .semicolon)])) := by
  cases targets with
  | none =>
      simp [pragmaDeclPlan?, sourceLoc, pragmaTargetsPlan,
        RuleReduction.terminalLoc]
  | some values =>
      unfold pragmaDeclPlan?
      simp [sourceLoc, pragmaTargetsPlan,
        RuleReduction.firstRest, RuleReduction.terminalLoc,
        NonemptyList.map]
      unfold identifierPlans
      simp [Function.comp_def]

private theorem pragmaBranch_tokenPlanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (kind : PragmaKind)
    (pragmaKw : MatchedTerminal file tokens (.hardKeyword .pragmaKw))
    (kindToken : MatchedTerminal file tokens (.pragmaName kind))
    (targets : Option (NonemptyList
      (RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish)
    (inputEvidence : TokenPlanEvidence
      (some (TokenPlan.concat [
        TokenPlan.exact (.hardKeyword .pragmaKw) pragmaKw.span,
        TokenPlan.exact (.pragmaName kind) kindToken.span,
        pragmaTargetsPlan targets,
        TokenPlan.exact (.symbol .semicolon) semicolon.span]))
      (PhysicalTokens tokens origin finish)) :
    TokenPlanEvidence
      (ruleTokenPlan? .pragmaDecl (sourceLoc witness {
        kind := RuleReduction.terminalLoc kindToken kind
        targets := targets.elim [] fun values =>
          RuleReduction.firstRest (values.map fun name =>
            RuleReduction.terminalLoc name.matched name.parsed)
      }))
      (PhysicalTokens tokens origin finish) := by
  rcases inputEvidence with ⟨inputPlan, planEq, relation⟩
  simp only [Option.some.injEq] at planEq
  subst inputPlan
  have innerRelation :=
    TokenSlot.ListMatches.fixedBookendsToPlain relation
  let innerPlan := TokenPlan.concat [
    TokenPlan.plain (.hardKeyword .pragmaKw),
    TokenPlan.exact (.pragmaName kind) kindToken.span,
    pragmaTargetsPlan targets,
    TokenPlan.plain (.symbol .semicolon)]
  have innerEvidence : TokenPlanEvidence (some innerPlan)
      (PhysicalTokens tokens origin finish) :=
    TokenPlanEvidence.some innerRelation
  have enclosed := innerEvidence.enclose
    (fun plan success => by
      injection success with planEq
      subst plan
      change (TokenPlan.concat [
        TokenPlan.plain (.hardKeyword .pragmaKw),
        TokenPlan.exact (.pragmaName kind) kindToken.span,
        pragmaTargetsPlan targets,
        TokenPlan.plain (.symbol .semicolon)]).WellAnchored
      exact TokenPlan.WellAnchored.concatPlainBookended
        (.hardKeyword .pragmaKw) (.symbol .semicolon)
        [TokenPlan.exact (.pragmaName kind) kindToken.span,
          pragmaTargetsPlan targets])
    witness.consumed
  apply TokenPlanEvidence.candidate_eq enclosed
  rw [ruleTokenPlan?_pragmaDecl]
  simpa [innerPlan] using
    (pragmaDeclPlan?_sourceLoc kind kindToken targets witness).symm

theorem pragmaDecl_tokenPlanSound :
    GrammarRuleTokenPlanSound .pragmaDecl := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | pragmaDeclNoCoverageCondition origin finish pragmaKw kindToken
      targets semicolon targetProjects witness =>
      change EbnfValue file tokens (.choice pragmaSourceBranches) at input
      rw [← inputEq] at inputEvidence
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          some (TokenPlan.concat [
            TokenPlan.exact (.hardKeyword .pragmaKw) pragmaKw.span,
            TokenPlan.exact (.pragmaName .noCoverageCondition)
              kindToken.span,
            pragmaTargetsPlan targets,
            TokenPlan.exact (.symbol .semicolon) semicolon.span]) := by
        rw [inputEq]
        exact pragmaNoCoverageInput_tokenPlan? pragmaKw kindToken
          targets semicolon targetProjects
      exact pragmaBranch_tokenPlanEvidence .noCoverageCondition
        pragmaKw kindToken targets semicolon witness
          (inputEvidence.candidate_eq candidateEq)
  | pragmaDeclNoPattersonCondition origin finish pragmaKw kindToken
      targets semicolon targetProjects witness =>
      change EbnfValue file tokens (.choice pragmaSourceBranches) at input
      rw [← inputEq] at inputEvidence
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          some (TokenPlan.concat [
            TokenPlan.exact (.hardKeyword .pragmaKw) pragmaKw.span,
            TokenPlan.exact (.pragmaName .noPattersonCondition)
              kindToken.span,
            pragmaTargetsPlan targets,
            TokenPlan.exact (.symbol .semicolon) semicolon.span]) := by
        rw [inputEq]
        exact pragmaNoPattersonInput_tokenPlan? pragmaKw kindToken
          targets semicolon targetProjects
      exact pragmaBranch_tokenPlanEvidence .noPattersonCondition
        pragmaKw kindToken targets semicolon witness
          (inputEvidence.candidate_eq candidateEq)
  | pragmaDeclNoBoundedVariableCondition origin finish pragmaKw kindToken
      targets semicolon targetProjects witness =>
      change EbnfValue file tokens (.choice pragmaSourceBranches) at input
      rw [← inputEq] at inputEvidence
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          some (TokenPlan.concat [
            TokenPlan.exact (.hardKeyword .pragmaKw) pragmaKw.span,
            TokenPlan.exact (.pragmaName .noBoundedVariableCondition)
              kindToken.span,
            pragmaTargetsPlan targets,
            TokenPlan.exact (.symbol .semicolon) semicolon.span]) := by
        rw [inputEq]
        exact pragmaNoBoundedVariableInput_tokenPlan? pragmaKw kindToken
          targets semicolon targetProjects
      exact pragmaBranch_tokenPlanEvidence .noBoundedVariableCondition
        pragmaKw kindToken targets semicolon witness
          (inputEvidence.candidate_eq candidateEq)
  | pragmaDeclNoGenericInstanceFor origin finish pragmaKw kindToken
      targets semicolon targetProjects witness =>
      change EbnfValue file tokens (.choice pragmaSourceBranches) at input
      rw [← inputEq] at inputEvidence
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          some (TokenPlan.concat [
            TokenPlan.exact (.hardKeyword .pragmaKw) pragmaKw.span,
            TokenPlan.exact (.pragmaName .noGenericInstanceFor)
              kindToken.span,
            pragmaTargetsPlan targets,
            TokenPlan.exact (.symbol .semicolon) semicolon.span]) := by
        rw [inputEq]
        exact pragmaNoGenericInstanceInput_tokenPlan? pragmaKw kindToken
          targets semicolon targetProjects
      exact pragmaBranch_tokenPlanEvidence .noGenericInstanceFor
        pragmaKw kindToken targets semicolon witness
          (inputEvidence.candidate_eq candidateEq)

theorem optionalComma_tokenPlanSound :
    GrammarRuleTokenPlanSound .optionalComma := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize actualEq : PhysicalTokens tokens origin finish = actual
    at inputEvidence ⊢
  cases reduces with
  | optionalCommaAbsent origin finish =>
      rw [EbnfValue.tokenPlan?_transport,
        EbnfValue.tokenPlan?_optional_none] at inputEvidence
      rcases inputEvidence with ⟨plan, candidateEq, relation⟩
      simp only [Option.some.injEq] at candidateEq
      subst plan
      cases relation
      exact TokenPlanEvidence.some
        (TokenSlot.ListMatches.optional_absent
          (ExpectedToken.plain (.symbol .comma)))
  | optionalCommaPresent origin finish comma =>
      rw [EbnfValue.tokenPlan?_transport,
        EbnfValue.tokenPlan?_optional_some,
        EbnfValue.tokenPlan?_terminalAtom,
        matchedSymbol_physicalTokenPlan .comma comma] at inputEvidence
      rcases inputEvidence with ⟨plan, candidateEq, relation⟩
      simp only [Option.some.injEq] at candidateEq
      subst plan
      change TokenSlot.ListMatches
        [.required (ExpectedToken.exact (.symbol .comma) comma.span)] _
        at relation
      cases relation with
      | required head tail =>
          cases tail
          exact TokenPlanEvidence.some
            (.optionalPresent head.toPlain .nil)

end Solcore.Surface.Multi
