import Solcore.Surface.Multi.ExactTokenRuleDeclarations

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace
open Lean Lean.Elab Lean.Elab.Tactic

elab "unfoldDataDeclNonemptyPlansCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.nonemptyPlans?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] => unfoldTarget declaration
  | _ => throwError "the data declaration visitor has an unknown list helper"

elab "unfoldDataDeclPipeSeparatedCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.pipeSeparated
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] => unfoldTarget declaration
  | _ => throwError "the data declaration visitor has an unknown separator helper"

private abbrev DataDeclParameters
    (file : WorkspaceFile) (tokens : List Token) :=
  Option
    (MatchedTerminal file tokens (.symbol .leftParen) ×
      (NonemptyList (RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier) ×
        (MatchedTerminal file tokens (.symbol .rightParen) × Unit)))

private abbrev DataDeclConstructors
    (file : WorkspaceFile) (tokens : List Token) :=
  Option
    (MatchedTerminal file tokens (.symbol .equal) ×
      (DataConstructor ×
        (List
          (MatchedTerminal file tokens (.symbol .pipe) ×
            DataConstructor) × Unit)))

private abbrev dataDeclParameterChildren : List EbnfExpr := [
  .atom (.terminal (.symbol .leftParen)),
  .list1 (.atom (.terminal (.category .identifier))),
  .atom (.terminal (.symbol .rightParen))]

private abbrev dataDeclConstructorTailExpr : EbnfExpr :=
  .group (.sequence [
    .atom (.terminal (.symbol .pipe)),
    .atom (.nonterminal .dataConstructor)])

private abbrev dataDeclConstructorChildren : List EbnfExpr := [
  .atom (.terminal (.symbol .equal)),
  .atom (.nonterminal .dataConstructor),
  .star dataDeclConstructorTailExpr]

private abbrev dataDeclChildren : List EbnfExpr := [
  .atom (.terminal (.hardKeyword .dataKw)),
  .atom (.terminal (.category .identifier)),
  .optional (.sequence dataDeclParameterChildren),
  .optional (.sequence dataDeclConstructorChildren),
  .atom (.terminal (.symbol .semicolon))]

private def dataDeclParameterInput
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : DataDeclParameters file tokens) :
    EbnfValue file tokens
      (.optional (.sequence dataDeclParameterChildren)) :=
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

private def dataDeclConstructorTailInput
    {file : WorkspaceFile} {tokens : List Token}
    (entry : MatchedTerminal file tokens (.symbol .pipe) ×
      DataConstructor) :
    EbnfValue file tokens dataDeclConstructorTailExpr :=
  EbnfValue.group _ <| EbnfValue.sequence _ <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .pipe) entry.1) <|
    EbnfValues.cons _ _
      (EbnfValue.ruleAtom .dataConstructor entry.2)
      EbnfValues.nil

private def dataDeclConstructorInput
    {file : WorkspaceFile} {tokens : List Token}
    (constructors : DataDeclConstructors file tokens) :
    EbnfValue file tokens
      (.optional (.sequence dataDeclConstructorChildren)) :=
  EbnfValue.optional _ <| constructors.map fun value =>
    EbnfValue.sequence _ <|
      EbnfValues.cons _ _
        (EbnfValue.terminalAtom (.symbol .equal) value.1) <|
      EbnfValues.cons _ _
        (EbnfValue.ruleAtom .dataConstructor value.2.1) <|
      EbnfValues.cons _ _
        (EbnfValue.star dataDeclConstructorTailExpr
          (value.2.2.1.map dataDeclConstructorTailInput))
        EbnfValues.nil

private def dataDeclInput
    {file : WorkspaceFile} {tokens : List Token}
    (dataKw : MatchedTerminal file tokens (.hardKeyword .dataKw))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (parameters : DataDeclParameters file tokens)
    (constructors : DataDeclConstructors file tokens)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon)) :
    EbnfValue file tokens (.sequence dataDeclChildren) :=
  EbnfValue.sequence _ <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.hardKeyword .dataKw) dataKw) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.category .identifier) name.matched) <|
    EbnfValues.cons _ _
      (dataDeclParameterInput parameters) <|
    EbnfValues.cons _ _
      (dataDeclConstructorInput constructors) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .semicolon) semicolon)
      EbnfValues.nil

private def dataDeclParameterSourcePlan
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : DataDeclParameters file tokens) : TokenPlan :=
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

private def dataDeclParameterPlainPlan
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : DataDeclParameters file tokens) : TokenPlan :=
  match parameters with
  | none => .empty
  | some value => .parens (.commaSeparated
      (identifierPlan
          (RuleReduction.terminalLoc value.2.1.head.matched
            value.2.1.head.parsed) ::
        value.2.1.tail.map fun parameter => identifierPlan
          (RuleReduction.terminalLoc parameter.matched
            parameter.parsed)))

private def dataDeclConstructorTailSourcePlan?
    {file : WorkspaceFile} {tokens : List Token} :
    List (MatchedTerminal file tokens (.symbol .pipe) ×
      DataConstructor) → Option TokenPlan
  | [] => some .empty
  | entry :: rest => do
      let constructorPlan ← dataConstructorPlan? entry.2
      let restPlan ← dataDeclConstructorTailSourcePlan? rest
      pure (((TokenPlan.exact (.symbol .pipe) entry.1.span).append
        constructorPlan).append restPlan)

private def dataDeclConstructorTailPlainPlan?
    {file : WorkspaceFile} {tokens : List Token} :
    List (MatchedTerminal file tokens (.symbol .pipe) ×
      DataConstructor) → Option TokenPlan
  | [] => some .empty
  | entry :: rest => do
      let constructorPlan ← dataConstructorPlan? entry.2
      let restPlan ← dataDeclConstructorTailPlainPlan? rest
      pure (((TokenPlan.plain (.symbol .pipe)).append
        constructorPlan).append restPlan)

private def dataDeclConstructorSourcePlan?
    {file : WorkspaceFile} {tokens : List Token}
    (constructors : DataDeclConstructors file tokens) : Option TokenPlan :=
  match constructors with
  | none => some .empty
  | some value => do
      let headPlan ← dataConstructorPlan? value.2.1
      let tailPlan ← dataDeclConstructorTailSourcePlan? value.2.2.1
      pure (.concat [
        .exact (.symbol .equal) value.1.span,
        headPlan,
        tailPlan])

private def dataDeclConstructorPlainPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (constructors : DataDeclConstructors file tokens) : Option TokenPlan :=
  match constructors with
  | none => some .empty
  | some value => do
      let headPlan ← dataConstructorPlan? value.2.1
      let tailPlan ← dataDeclConstructorTailPlainPlan? value.2.2.1
      pure (.concat [
        .plain (.symbol .equal),
        headPlan,
        tailPlan])

private theorem dataDeclConstructorTailPlainPlan?_eq
    {file : WorkspaceFile} {tokens : List Token}
    (entries : List
      (MatchedTerminal file tokens (.symbol .pipe) × DataConstructor)) :
    dataDeclConstructorTailPlainPlan? entries = (do
      let plans ← (entries.map Prod.snd).mapM dataConstructorPlan?
      pure (TokenPlan.concat (plans.map fun plan =>
        (TokenPlan.plain (.symbol .pipe)).append plan))) := by
  induction entries with
  | nil => rfl
  | cons entry rest induction =>
      rw [dataDeclConstructorTailPlainPlan?, List.map_cons,
        List.mapM_cons, induction]
      cases constructorEq : dataConstructorPlan? entry.2 <;>
        cases tailPlansEq :
          (rest.map Prod.snd).mapM dataConstructorPlan? <;>
        simp [TokenPlan.concat_cons,
          TokenPlan.append_assoc]

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

private theorem dataDeclParameterInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : DataDeclParameters file tokens)
    (parameterProjects : ∀ value, parameters = some value →
      IdentifierProjects value.2.1.head.matched
        value.2.1.head.spelling value.2.1.head.parsed ∧
      ∀ parameter, parameter ∈ value.2.1.tail →
        IdentifierProjects parameter.matched
          parameter.spelling parameter.parsed) :
    (dataDeclParameterInput parameters).tokenPlan?
        sourceRuleTokenPlanLayout =
      some (dataDeclParameterSourcePlan parameters) := by
  cases parameters with
  | none =>
      simp [dataDeclParameterInput, dataDeclParameterSourcePlan]
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
      simp only [dataDeclParameterInput, Option.map_some,
        EbnfValue.tokenPlan?_optional_some,
        EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_list1,
        EbnfValues.tokenPlan?_nil]
      simp [Function.comp_def, EbnfValue.tokenPlan?_terminalAtom]
      rw [mappedPlansEq, headPlanEq,
        matchedSymbol_physicalTokenPlan,
        matchedSymbol_physicalTokenPlan]
      simp [dataDeclParameterSourcePlan, TokenPlan.concat_cons]

private theorem dataDeclConstructorTailInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (entry : MatchedTerminal file tokens (.symbol .pipe) ×
      DataConstructor) :
    (dataDeclConstructorTailInput entry).tokenPlan?
      sourceRuleTokenPlanLayout = (do
      let constructorPlan ← dataConstructorPlan? entry.2
      pure ((TokenPlan.exact (.symbol .pipe) entry.1.span).append
        constructorPlan)) := by
  cases constructorEq : dataConstructorPlan? entry.2 <;>
    simp [dataDeclConstructorTailInput, dataDeclConstructorTailExpr,
      sourceRuleTokenPlanLayout, ruleTokenPlan?, constructorEq,
      matchedSymbol_physicalTokenPlan,
      TokenPlan.append, TokenPlan.empty]

private theorem dataDeclConstructorTailInputs_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (entries : List
      (MatchedTerminal file tokens (.symbol .pipe) × DataConstructor)) :
    (do
      let plans ← (entries.map dataDeclConstructorTailInput).mapM
        (fun value => value.tokenPlan? sourceRuleTokenPlanLayout)
      pure (TokenPlan.concat plans)) =
      dataDeclConstructorTailSourcePlan? entries := by
  induction entries with
  | nil =>
      rfl
  | cons entry rest induction =>
      rw [List.map_cons, List.mapM_cons,
        dataDeclConstructorTailInput_tokenPlan?]
      cases constructorEq : dataConstructorPlan? entry.2 with
      | none => simp [constructorEq, dataDeclConstructorTailSourcePlan?]
      | some constructorPlan =>
          cases tailInputsEq :
              (rest.map dataDeclConstructorTailInput).mapM
                (fun value => value.tokenPlan?
                  sourceRuleTokenPlanLayout) with
          | none =>
              have tailNone :
                  dataDeclConstructorTailSourcePlan? rest = none := by
                rw [← induction, tailInputsEq]
                rfl
              simp [constructorEq,
                dataDeclConstructorTailSourcePlan?, tailNone]
          | some tailPlans =>
              have tailSome :
                  dataDeclConstructorTailSourcePlan? rest =
                    some (TokenPlan.concat tailPlans) := by
                rw [← induction, tailInputsEq]
                rfl
              simp [constructorEq,
                dataDeclConstructorTailSourcePlan?, tailSome,
                TokenPlan.concat_cons, TokenPlan.append_assoc]

private theorem dataDeclConstructorTailInputList_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (entries : List
      (MatchedTerminal file tokens (.symbol .pipe) × DataConstructor)) :
    (EbnfValue.star dataDeclConstructorTailExpr
      (entries.map dataDeclConstructorTailInput)).tokenPlan?
        sourceRuleTokenPlanLayout =
      dataDeclConstructorTailSourcePlan? entries := by
  rw [EbnfValue.tokenPlan?_star]
  exact dataDeclConstructorTailInputs_tokenPlan? entries

private theorem dataDeclConstructorInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (constructors : DataDeclConstructors file tokens) :
    (dataDeclConstructorInput constructors).tokenPlan?
        sourceRuleTokenPlanLayout =
      dataDeclConstructorSourcePlan? constructors := by
  cases constructors with
  | none =>
      simp [dataDeclConstructorInput, dataDeclConstructorSourcePlan?]
  | some value =>
      simp only [dataDeclConstructorInput, Option.map_some,
        EbnfValue.tokenPlan?_optional_some,
        EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValues.tokenPlan?_nil,
        matchedSymbol_physicalTokenPlan]
      rw [dataDeclConstructorTailInputList_tokenPlan?]
      simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?]
      cases headEq : dataConstructorPlan? value.2.1 <;>
        cases tailEq :
          dataDeclConstructorTailSourcePlan? value.2.2.1 <;>
        simp [dataDeclConstructorSourcePlan?, headEq, tailEq,
          TokenPlan.concat_cons]

private theorem dataDeclInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (dataKw : MatchedTerminal file tokens (.hardKeyword .dataKw))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (parameters : DataDeclParameters file tokens)
    (constructors : DataDeclConstructors file tokens)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (nameProjects : IdentifierProjects name.matched
      name.spelling name.parsed)
    (parameterProjects : ∀ value, parameters = some value →
      IdentifierProjects value.2.1.head.matched
        value.2.1.head.spelling value.2.1.head.parsed ∧
      ∀ parameter, parameter ∈ value.2.1.tail →
        IdentifierProjects parameter.matched
          parameter.spelling parameter.parsed) :
    (dataDeclInput dataKw name parameters constructors semicolon).tokenPlan?
        sourceRuleTokenPlanLayout = (do
      let constructorPlan ← dataDeclConstructorSourcePlan? constructors
      pure (TokenPlan.concat [
        TokenPlan.exact (.hardKeyword .dataKw) dataKw.span,
        identifierPlan
          (RuleReduction.terminalLoc name.matched name.parsed),
        dataDeclParameterSourcePlan parameters,
        constructorPlan,
        TokenPlan.exact (.symbol .semicolon) semicolon.span])) := by
  unfold dataDeclInput
  rw [EbnfValue.tokenPlan?_sequence,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValues.tokenPlan?_cons,
    EbnfValues.tokenPlan?_cons,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValues.tokenPlan?_nil,
    matchedHardKeyword_physicalTokenPlan,
    matchedIdentifier_physicalTokenPlan name nameProjects,
    dataDeclParameterInput_tokenPlan? parameters parameterProjects,
    dataDeclConstructorInput_tokenPlan? constructors,
    matchedSymbol_physicalTokenPlan]
  cases dataDeclConstructorSourcePlan? constructors <;>
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

private theorem dataDeclParameterSourcePlan_weakens
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : DataDeclParameters file tokens) :
    (dataDeclParameterSourcePlan parameters).WeakensTo
      (dataDeclParameterPlainPlan parameters) := by
  cases parameters with
  | none => exact TokenPlan.WeakensTo.refl _
  | some value =>
      intro actual relation
      exact TokenSlot.ListMatches.exactParensToPlain relation

private theorem dataDeclConstructorTailSourcePlan?_weakens
    {file : WorkspaceFile} {tokens : List Token}
    (entries : List
      (MatchedTerminal file tokens (.symbol .pipe) × DataConstructor))
    {sourcePlan : TokenPlan}
    (sourceEq : dataDeclConstructorTailSourcePlan? entries =
      some sourcePlan) :
    ∃ targetPlan,
      dataDeclConstructorTailPlainPlan? entries = some targetPlan ∧
      sourcePlan.WeakensTo targetPlan := by
  induction entries generalizing sourcePlan with
  | nil =>
      simp [dataDeclConstructorTailSourcePlan?,
        dataDeclConstructorTailPlainPlan?] at sourceEq ⊢
      subst sourcePlan
      exact TokenPlan.WeakensTo.refl _
  | cons entry rest induction =>
      simp only [dataDeclConstructorTailSourcePlan?] at sourceEq
      cases constructorEq : dataConstructorPlan? entry.2 with
      | none => simp [constructorEq] at sourceEq
      | some constructorPlan =>
          cases restSourceEq :
              dataDeclConstructorTailSourcePlan? rest with
          | none => simp [constructorEq, restSourceEq] at sourceEq
          | some restSourcePlan =>
              simp [constructorEq, restSourceEq] at sourceEq
              subst sourcePlan
              rcases induction restSourceEq with
                ⟨restTargetPlan, restTargetEq, restWeakens⟩
              refine ⟨((TokenPlan.plain (.symbol .pipe)).append
                  constructorPlan).append restTargetPlan,
                ?_, ?_⟩
              · simp [dataDeclConstructorTailPlainPlan?, constructorEq,
                  restTargetEq]
              · exact TokenPlan.WeakensTo.append
                  (TokenPlan.WeakensTo.append
                    (TokenPlan.WeakensTo.exactToPlain _ _)
                    (TokenPlan.WeakensTo.refl _))
                  restWeakens

private theorem dataDeclConstructorSourcePlan?_weakens
    {file : WorkspaceFile} {tokens : List Token}
    (constructors : DataDeclConstructors file tokens)
    {sourcePlan : TokenPlan}
    (sourceEq : dataDeclConstructorSourcePlan? constructors =
      some sourcePlan) :
    ∃ targetPlan,
      dataDeclConstructorPlainPlan? constructors = some targetPlan ∧
      sourcePlan.WeakensTo targetPlan := by
  cases constructors with
  | none =>
      simp [dataDeclConstructorSourcePlan?,
        dataDeclConstructorPlainPlan?] at sourceEq ⊢
      subst sourcePlan
      exact TokenPlan.WeakensTo.refl _
  | some value =>
      simp only [dataDeclConstructorSourcePlan?] at sourceEq
      cases headEq : dataConstructorPlan? value.2.1 with
      | none => simp [headEq] at sourceEq
      | some headPlan =>
          cases tailSourceEq :
              dataDeclConstructorTailSourcePlan? value.2.2.1 with
          | none => simp [headEq, tailSourceEq] at sourceEq
          | some tailSourcePlan =>
              simp [headEq, tailSourceEq] at sourceEq
              subst sourcePlan
              rcases dataDeclConstructorTailSourcePlan?_weakens
                  value.2.2.1 tailSourceEq with
                ⟨tailTargetPlan, tailTargetEq, tailWeakens⟩
              refine ⟨TokenPlan.concat [
                .plain (.symbol .equal), headPlan, tailTargetPlan],
                ?_, ?_⟩
              · simp [dataDeclConstructorPlainPlan?, headEq,
                  tailTargetEq]
              · intro actual relation
                have weakened := (TokenPlan.WeakensTo.append
                    (TokenPlan.WeakensTo.exactToPlain
                      (.symbol .equal) value.1.span)
                    (TokenPlan.WeakensTo.append
                      (TokenPlan.WeakensTo.refl headPlan)
                      tailWeakens)) relation
                simpa [TokenPlan.concat_cons] using weakened

private theorem dataDeclPlan?_sourceLoc
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (_dataKw : MatchedTerminal file tokens (.hardKeyword .dataKw))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (parameters : DataDeclParameters file tokens)
    (constructors : DataDeclConstructors file tokens)
    (_semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    dataDeclPlan? (sourceLoc witness {
      name := RuleReduction.terminalLoc name.matched name.parsed
      parameters := parameters.map fun value =>
        value.2.1.map fun parameter =>
          RuleReduction.terminalLoc parameter.matched parameter.parsed
      constructors := constructors.map fun value => {
        head := value.2.1
        tail := value.2.2.1.map Prod.snd
      }
    } : DataDecl) = (do
      let constructorPlan ←
        dataDeclConstructorPlainPlan? constructors
      pure (TokenPlan.enclose witness.span (TokenPlan.concat [
        TokenPlan.plain (.hardKeyword .dataKw),
        identifierPlan
          (RuleReduction.terminalLoc name.matched name.parsed),
        dataDeclParameterPlainPlan parameters,
        constructorPlan,
        TokenPlan.plain (.symbol .semicolon)]))) := by
  unfold dataDeclPlan?
  simp only [sourceLoc]
  unfoldOptionalIdentifierPlanCore
  cases parameters <;> cases constructors with
  | none =>
      simp [dataDeclParameterPlainPlan,
        dataDeclConstructorPlainPlan?, NonemptyList.map,
        nonemptyIdentifierPlans, identifierPlans,
        TokenPlan.concat_cons, Function.comp_def]
  | some value =>
      simp only [Option.map_none, Option.map_some]
      unfoldDataDeclNonemptyPlansCore
      rwDeclarationPlansMapM
      simp only [dataDeclConstructorPlainPlan?]
      rw [dataDeclConstructorTailPlainPlan?_eq]
      cases headEq : dataConstructorPlan? value.2.1 <;>
        cases tailPlansEq :
          (value.2.2.1.map Prod.snd).mapM
            dataConstructorPlan? <;>
        simp [dataDeclParameterPlainPlan,
          NonemptyList.map,
          nonemptyIdentifierPlans, identifierPlans,
          TokenPlan.concat_cons, TokenPlan.append_assoc,
          Function.comp_def]
      unfoldDataDeclPipeSeparatedCore
      simp [TokenPlan.append_assoc]

/-- Data declarations preserve names, parameters, and constructor plans while
weakening only punctuation fixed by the declaration grammar. -/
theorem dataDecl_tokenPlanSound :
    GrammarRuleTokenPlanSound .dataDecl := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | dataDecl origin finish dataKw name parameters constructors semicolon
      nameProjects parameterProjects witness =>
      rw [← inputEq] at inputEvidence
      change TokenPlanEvidence
        (dataDeclPlan? (sourceLoc witness {
          name := RuleReduction.terminalLoc name.matched name.parsed
          parameters := parameters.map fun value =>
            value.2.1.map fun parameter =>
              RuleReduction.terminalLoc parameter.matched parameter.parsed
          constructors := constructors.map fun value => {
            head := value.2.1
            tail := value.2.2.1.map Prod.snd
          }
        } : DataDecl)) _
      let namePlan := identifierPlan
        (RuleReduction.terminalLoc name.matched name.parsed)
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout = (do
          let constructorPlan ←
            dataDeclConstructorSourcePlan? constructors
          pure (TokenPlan.concat [
            TokenPlan.exact (.hardKeyword .dataKw) dataKw.span,
            namePlan,
            dataDeclParameterSourcePlan parameters,
            constructorPlan,
            TokenPlan.exact (.symbol .semicolon) semicolon.span])) := by
        rw [inputEq]
        simp only [m2cV1, m2cV1Rhs, Grammar.hardKeyword,
          Grammar.identifier, Grammar.category, Grammar.terminal,
          Grammar.sequence, Grammar.symbol, Grammar.nonterminal,
          Grammar.optional, Grammar.list1, Grammar.star, Grammar.group]
        rw [EbnfValue.tokenPlan?_transport]
        change (dataDeclInput dataKw name parameters constructors
          semicolon).tokenPlan? sourceRuleTokenPlanLayout = _
        simpa [namePlan] using dataDeclInput_tokenPlan?
          dataKw name parameters constructors semicolon
            nameProjects parameterProjects
      have physicalEvidence := inputEvidence.candidate_eq candidateEq
      cases sourceConstructorEq :
          dataDeclConstructorSourcePlan? constructors with
      | none =>
          simp [sourceConstructorEq, TokenPlanEvidence]
            at physicalEvidence
      | some sourceConstructorPlan =>
          simp only [sourceConstructorEq] at physicalEvidence
          rcases dataDeclConstructorSourcePlan?_weakens
              constructors sourceConstructorEq with
            ⟨targetConstructorPlan, targetConstructorEq,
              constructorWeakens⟩
          let sourceCore := TokenPlan.concat [
            TokenPlan.exact (.hardKeyword .dataKw) dataKw.span,
            namePlan,
            dataDeclParameterSourcePlan parameters,
            sourceConstructorPlan,
            TokenPlan.exact (.symbol .semicolon) semicolon.span]
          let targetCore := TokenPlan.concat [
            TokenPlan.plain (.hardKeyword .dataKw),
            namePlan,
            dataDeclParameterPlainPlan parameters,
            targetConstructorPlan,
            TokenPlan.plain (.symbol .semicolon)]
          rcases physicalEvidence with ⟨plan, planEq, relation⟩
          change some sourceCore = some plan at planEq
          injection planEq with planEq
          subst plan
          have coreWeakens : sourceCore.WeakensTo targetCore := by
            intro actual sourceRelation
            have weakened := (TokenPlan.WeakensTo.append
              (TokenPlan.WeakensTo.exactToPlain
                (.hardKeyword .dataKw) dataKw.span)
              (TokenPlan.WeakensTo.append
                (TokenPlan.WeakensTo.refl namePlan)
                (TokenPlan.WeakensTo.append
                  (dataDeclParameterSourcePlan_weakens parameters)
                  (TokenPlan.WeakensTo.append constructorWeakens
                    (TokenPlan.WeakensTo.exactToPlain
                      (.symbol .semicolon) semicolon.span)))))
                sourceRelation
            simpa [sourceCore, targetCore, TokenPlan.concat_cons,
              TokenPlan.append_assoc] using weakened
          have targetRelation : TokenSlot.ListMatches targetCore.slots
              (PhysicalTokens tokens origin finish) :=
            coreWeakens relation
          have targetAnchored : targetCore.WellAnchored := by
            exact TokenPlan.WellAnchored.concat_plain_bookended_three
              (.hardKeyword .dataKw) (.symbol .semicolon)
              namePlan (dataDeclParameterPlainPlan parameters)
              targetConstructorPlan
          have enclosed := TokenPlanEvidence.enclose
            (TokenPlanEvidence.some targetRelation)
            (fun candidate success => by
              simp only [Option.some.injEq] at success
              subst candidate
              exact targetAnchored)
            witness.consumed
          apply enclosed.candidate_eq
          rw [dataDeclPlan?_sourceLoc dataKw name parameters constructors
            semicolon witness]
          rw [targetConstructorEq]
          simp [targetCore, namePlan]

end Solcore.Surface.Multi
