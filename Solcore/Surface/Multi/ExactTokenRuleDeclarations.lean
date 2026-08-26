import Solcore.Surface.Multi.ExactTokenAnchoring
import Solcore.Surface.Multi.ExactTokenRulePassThrough
import Solcore.Surface.Multi.ExactTokenRuleSoundness
import Solcore.Surface.Multi.ExactTokenTypeAnchoring

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace
open Lean Lean.Elab Lean.Elab.Tactic

elab "unfoldOptionalNonemptyTypePlanCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.optionalNonemptyTypePlans?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] =>
      unfoldTarget declaration
  | _ =>
      throwError "the declaration visitor has an unknown optional type helper"

elab "unfoldNonemptyTypePlanCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.nonemptyTypePlans?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] =>
      unfoldTarget declaration
  | _ =>
      throwError "the declaration visitor has an unknown type-list helper"

elab "unfoldOptionalIdentifierPlanCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.optionalNonemptyIdentifierPlan
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] =>
      unfoldTarget declaration
  | _ =>
      throwError "the declaration visitor has an unknown identifier helper"

elab "unfoldSignatureOptionalPlanCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.optionalPlan?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] => unfoldTarget declaration
  | _ => throwError "the signature visitor has an unknown optional helper"

elab "unfoldSignatureOptionalMarkerCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.optionalMarkerPlan?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] => unfoldTarget declaration
  | _ => throwError "the signature visitor has an unknown marker helper"

elab "unfoldSignatureMarkerCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.markerPlan?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] => unfoldTarget declaration
  | _ => throwError "the signature visitor has an unknown marker plan"

elab "unfoldSignatureReturnCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.optionalReturnTypePlan?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] => unfoldTarget declaration
  | _ => throwError "the signature visitor has an unknown return helper"

elab "rwDeclarationPlansMapM" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.plans?_eq_mapM
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] =>
      let identifier := mkIdent declaration
      rewriteTarget identifier.raw false
  | _ => throwError "the declaration visitor has an unknown list theorem"

private abbrev dataConstructorArgumentChildren : List EbnfExpr := [
  .atom (.terminal (.symbol .leftParen)),
  .list1 (.atom (.nonterminal .type)),
  .atom (.terminal (.symbol .rightParen))]

private abbrev dataConstructorChildren : List EbnfExpr := [
  .atom (.terminal (.category .identifier)),
  .optional (.sequence dataConstructorArgumentChildren)]

private def dataConstructorWithArgumentsInput
    {file : WorkspaceFile} {tokens : List Token}
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (fields : NonemptyList TypeExpr)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen)) :
    EbnfValue file tokens (.sequence dataConstructorChildren) :=
  EbnfValue.sequence _ <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.category .identifier) name.matched) <|
    EbnfValues.cons _ _
      (EbnfValue.optional _ (some <|
        EbnfValue.sequence _ <|
          EbnfValues.cons _ _
            (EbnfValue.terminalAtom (.symbol .leftParen) openParen) <|
          EbnfValues.cons _ _
            (EbnfValue.list1 _
              (fields.map (EbnfValue.ruleAtom .type))) <|
          EbnfValues.cons _ _
            (EbnfValue.terminalAtom (.symbol .rightParen) closeParen)
            EbnfValues.nil))
      EbnfValues.nil

private abbrev typeAliasParameterChildren : List EbnfExpr := [
  .atom (.terminal (.symbol .leftParen)),
  .list1 (.atom (.terminal (.category .identifier))),
  .atom (.terminal (.symbol .rightParen))]

private abbrev typeAliasChildren : List EbnfExpr := [
  .atom (.terminal (.hardKeyword .typeKw)),
  .atom (.terminal (.category .identifier)),
  .optional (.sequence typeAliasParameterChildren),
  .atom (.terminal (.symbol .equal)),
  .atom (.nonterminal .type),
  .atom (.terminal (.symbol .semicolon))]

private abbrev functionSignatureReturnChildren : List EbnfExpr := [
  .atom (.terminal (.symbol .arrow)),
  .atom (.nonterminal .type)]

private abbrev functionSignatureChildren : List EbnfExpr := [
  .optional (.atom (.nonterminal .genericPrefix)),
  .optional (.atom (.terminal (.hardKeyword .publicKw))),
  .optional (.atom (.terminal (.hardKeyword .payableKw))),
  .atom (.terminal (.hardKeyword .functionKw)),
  .atom (.terminal (.category .identifier)),
  .atom (.terminal (.symbol .leftParen)),
  .list0 (.atom (.nonterminal .parameter)),
  .atom (.terminal (.symbol .rightParen)),
  .optional (.sequence functionSignatureReturnChildren)]

private def functionSignatureInput
    {file : WorkspaceFile} {tokens : List Token}
    (genericPrefix : Option GenericPrefix)
    (publicToken : Option (MatchedTerminal file tokens
      (.hardKeyword .publicKw)))
    (payableToken : Option (MatchedTerminal file tokens
      (.hardKeyword .payableKw)))
    (functionKw : MatchedTerminal file tokens (.hardKeyword .functionKw))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (parameters : List Parameter)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (returnValue : Option
      (MatchedTerminal file tokens (.symbol .arrow) ×
        (TypeExpr × Unit))) :
    EbnfValue file tokens (.sequence functionSignatureChildren) :=
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
      (EbnfValue.terminalAtom (.hardKeyword .functionKw) functionKw) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.category .identifier) name.matched) <|
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
            EbnfValues.nil))
      EbnfValues.nil

private def optionalGenericPlan? :
    Option GenericPrefix → Option TokenPlan
  | none => some .empty
  | some value => genericPrefixPlan? value

private def optionalKeywordPlan
    {file : WorkspaceFile} {tokens : List Token} (keyword : HardKeyword) :
    Option (MatchedTerminal file tokens (.hardKeyword keyword)) → TokenPlan
  | none => .empty
  | some terminal => .exact (.hardKeyword keyword) terminal.span

private def signatureReturnSourcePlan?
    {file : WorkspaceFile} {tokens : List Token} :
    Option (MatchedTerminal file tokens (.symbol .arrow) ×
      (TypeExpr × Unit)) → Option TokenPlan
  | none => some .empty
  | some value => do
      let typePlan ← typeExprPlan? value.2.1
      pure ((TokenPlan.exact (.symbol .arrow) value.1.span).append typePlan)

private def signatureReturnPlainPlan?
    {file : WorkspaceFile} {tokens : List Token} :
    Option (MatchedTerminal file tokens (.symbol .arrow) ×
      (TypeExpr × Unit)) → Option TokenPlan
  | none => some .empty
  | some value => do
      let typePlan ← typeExprPlan? value.2.1
      pure ((TokenPlan.plain (.symbol .arrow)).append typePlan)

private def typeAliasInput
    {file : WorkspaceFile} {tokens : List Token}
    (typeKw : MatchedTerminal file tokens (.hardKeyword .typeKw))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (parameters : Option
      (MatchedTerminal file tokens (.symbol .leftParen) ×
        (NonemptyList (RuleReduction.SpelledTerminalData file tokens
          (.category .identifier) Identifier) ×
          (MatchedTerminal file tokens (.symbol .rightParen) × Unit))))
    (equal : MatchedTerminal file tokens (.symbol .equal))
    (body : TypeExpr)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon)) :
    EbnfValue file tokens (.sequence typeAliasChildren) :=
  EbnfValue.sequence _ <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.hardKeyword .typeKw) typeKw) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.category .identifier) name.matched) <|
    EbnfValues.cons _ _
      (EbnfValue.optional _ (parameters.map fun value =>
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
            EbnfValues.nil)) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .equal) equal) <|
    EbnfValues.cons _ _
      (EbnfValue.ruleAtom .type body) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .semicolon) semicolon)
      EbnfValues.nil

private def typeAliasParameterSourcePlan
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : Option
      (MatchedTerminal file tokens (.symbol .leftParen) ×
        (NonemptyList (RuleReduction.SpelledTerminalData file tokens
          (.category .identifier) Identifier) ×
          (MatchedTerminal file tokens (.symbol .rightParen) × Unit)))) :
    TokenPlan :=
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

private def typeAliasParameterPlainPlan
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : Option
      (MatchedTerminal file tokens (.symbol .leftParen) ×
        (NonemptyList (RuleReduction.SpelledTerminalData file tokens
          (.category .identifier) Identifier) ×
          (MatchedTerminal file tokens (.symbol .rightParen) × Unit)))) :
    TokenPlan :=
  match parameters with
  | none => .empty
  | some value => .parens (.commaSeparated
      (identifierPlan
          (RuleReduction.terminalLoc value.2.1.head.matched
            value.2.1.head.parsed) ::
        value.2.1.tail.map fun parameter => identifierPlan
          (RuleReduction.terminalLoc parameter.matched
            parameter.parsed)))

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

private theorem typeAliasParameterSourcePlan_toPlain
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : Option
      (MatchedTerminal file tokens (.symbol .leftParen) ×
        (NonemptyList (RuleReduction.SpelledTerminalData file tokens
          (.category .identifier) Identifier) ×
          (MatchedTerminal file tokens (.symbol .rightParen) × Unit))))
    {actual : List Token}
    (relation : TokenSlot.ListMatches
      (typeAliasParameterSourcePlan parameters).slots actual) :
    TokenSlot.ListMatches
      (typeAliasParameterPlainPlan parameters).slots actual := by
  cases parameters with
  | none => exact relation
  | some value =>
      exact TokenSlot.ListMatches.exactParensToPlain relation

private theorem typeExprPlans_eq_mapM (values : List TypeExpr) :
    typeExprPlans? values = values.mapM typeExprPlan? := by
  induction values with
  | nil => simp [typeExprPlans?]
  | cons head tail induction =>
      simp [typeExprPlans?, List.mapM_cons, typeExprPlan?, induction]

private theorem nonemptyTypeExprPlans_eq_mapM
    (values : NonemptyList TypeExpr) :
    nonemptyTypeExprPlans? values = (do
      let headPlan ← typeExprPlan? values.head
      let tailPlans ← values.tail.mapM typeExprPlan?
      pure (headPlan :: tailPlans)) := by
  unfold nonemptyTypeExprPlans?
  rw [typeExprPlans_eq_mapM]
  rfl

private theorem dataConstructorWithArgumentsInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (fields : NonemptyList TypeExpr)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (nameProjects : IdentifierProjects name.matched
      name.spelling name.parsed) :
    (dataConstructorWithArgumentsInput name openParen fields closeParen).tokenPlan?
        sourceRuleTokenPlanLayout = (do
      let headPlan ← ruleTokenPlan? .type fields.head
      let tailPlans ← fields.tail.mapM (ruleTokenPlan? .type)
      pure ((identifierPlan
        (RuleReduction.terminalLoc name.matched name.parsed)).append
          ((TokenPlan.exact (.symbol .leftParen) openParen.span).append
            ((TokenPlan.commaSeparated (headPlan :: tailPlans)).append
              (TokenPlan.exact (.symbol .rightParen)
                closeParen.span))))) := by
  unfold dataConstructorWithArgumentsInput
  rw [EbnfValue.tokenPlan?_sequence]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_terminalAtom]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_optional_some]
  rw [EbnfValue.tokenPlan?_sequence]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_terminalAtom]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_list1]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_terminalAtom]
  rw [EbnfValues.tokenPlan?_nil]
  rw [matchedIdentifier_physicalTokenPlan name nameProjects]
  rw [matchedSymbol_physicalTokenPlan,
    matchedSymbol_physicalTokenPlan]
  simp [NonemptyList.map, Function.comp_def, sourceRuleTokenPlanLayout,
    TokenPlan.append_assoc] <;>
    cases headEq : ruleTokenPlan? .type fields.head <;>
    cases tailEq : fields.tail.mapM (ruleTokenPlan? .type) <;>
    simp [TokenPlan.append_assoc]

private theorem typeAliasInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (typeKw : MatchedTerminal file tokens (.hardKeyword .typeKw))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (parameters : Option
      (MatchedTerminal file tokens (.symbol .leftParen) ×
        (NonemptyList (RuleReduction.SpelledTerminalData file tokens
          (.category .identifier) Identifier) ×
          (MatchedTerminal file tokens (.symbol .rightParen) × Unit))))
    (equal : MatchedTerminal file tokens (.symbol .equal))
    (body : TypeExpr)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (nameProjects : IdentifierProjects name.matched
      name.spelling name.parsed)
    (parameterProjects : ∀ value, parameters = some value →
      IdentifierProjects value.2.1.head.matched
        value.2.1.head.spelling value.2.1.head.parsed ∧
      ∀ parameter, parameter ∈ value.2.1.tail →
        IdentifierProjects parameter.matched
          parameter.spelling parameter.parsed) :
    (typeAliasInput typeKw name parameters equal body semicolon).tokenPlan?
        sourceRuleTokenPlanLayout = (do
      let bodyPlan ← ruleTokenPlan? .type body
      pure (TokenPlan.concat [
        TokenPlan.exact (.hardKeyword .typeKw) typeKw.span,
        identifierPlan
          (RuleReduction.terminalLoc name.matched name.parsed),
        typeAliasParameterSourcePlan parameters,
        TokenPlan.exact (.symbol .equal) equal.span,
        bodyPlan,
        TokenPlan.exact (.symbol .semicolon) semicolon.span])) := by
  unfold typeAliasInput
  rw [EbnfValue.tokenPlan?_sequence]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_terminalAtom]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_terminalAtom]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_terminalAtom]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_ruleAtom]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_terminalAtom]
  rw [EbnfValues.tokenPlan?_nil]
  rw [matchedHardKeyword_physicalTokenPlan,
    matchedIdentifier_physicalTokenPlan name nameProjects,
    matchedSymbol_physicalTokenPlan,
    matchedSymbol_physicalTokenPlan]
  cases parameters with
  | none =>
      cases bodyEq : ruleTokenPlan? .type body <;>
        simp [bodyEq, typeAliasParameterSourcePlan,
          sourceRuleTokenPlanLayout, TokenPlan.concat_cons]

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
      simp only [Option.map_some,
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
      cases bodyEq : ruleTokenPlan? .type body <;>
        simp [bodyEq, typeAliasParameterSourcePlan,
          sourceRuleTokenPlanLayout, TokenPlan.concat_cons]

private theorem typeAliasDeclPlan?_sourceLoc
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (_typeKw : MatchedTerminal file tokens (.hardKeyword .typeKw))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (parameters : Option
      (MatchedTerminal file tokens (.symbol .leftParen) ×
        (NonemptyList (RuleReduction.SpelledTerminalData file tokens
          (.category .identifier) Identifier) ×
          (MatchedTerminal file tokens (.symbol .rightParen) × Unit))))
    (_equal : MatchedTerminal file tokens (.symbol .equal))
    (body : TypeExpr)
    (_semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    typeAliasDeclPlan? (sourceLoc witness {
      name := RuleReduction.terminalLoc name.matched name.parsed
      parameters := parameters.map fun value =>
        value.2.1.map fun parameter =>
          RuleReduction.terminalLoc parameter.matched parameter.parsed
      body := body
    } : TypeAliasDecl) = (do
      let bodyPlan ← typeExprPlan? body
      pure (TokenPlan.enclose witness.span (TokenPlan.concat [
        TokenPlan.plain (.hardKeyword .typeKw),
        identifierPlan
          (RuleReduction.terminalLoc name.matched name.parsed),
        typeAliasParameterPlainPlan parameters,
        TokenPlan.plain (.symbol .equal),
        bodyPlan,
        TokenPlan.plain (.symbol .semicolon)]))) := by
  unfold typeAliasDeclPlan?
  simp only [sourceLoc]
  unfoldOptionalIdentifierPlanCore
  cases parameters with
  | none =>
      simp [typeAliasParameterPlainPlan, TokenPlan.concat_cons]
  | some value =>
      simp [typeAliasParameterPlainPlan, NonemptyList.map,
        nonemptyIdentifierPlans, identifierPlans,
        TokenPlan.concat_cons, Function.comp_def]

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

private theorem parameterRuleValues_mapM_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : List Parameter) :
    (parameters.map (EbnfValue.ruleAtom
      (file := file) (tokens := tokens) .parameter)).mapM
        (fun value => value.tokenPlan? sourceRuleTokenPlanLayout) =
      parameters.mapM parameterTokenPlan? := by
  rw [List.mapM_map]
  simp [Function.comp_def, sourceRuleTokenPlanLayout, ruleTokenPlan?]
  congr 1

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
  rw [parameterRuleValues_mapM_tokenPlan?]

private theorem signatureReturnInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (returnValue : Option
      (MatchedTerminal file tokens (.symbol .arrow) ×
        (TypeExpr × Unit))) :
    (EbnfValue.optional
      (.sequence functionSignatureReturnChildren)
      (returnValue.map fun value =>
        EbnfValue.sequence _ <|
          EbnfValues.cons _ _
            (EbnfValue.terminalAtom (.symbol .arrow) value.1) <|
          EbnfValues.cons _ _
            (EbnfValue.ruleAtom .type value.2.1)
            EbnfValues.nil)).tokenPlan? sourceRuleTokenPlanLayout =
      signatureReturnSourcePlan? returnValue := by
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
        simp [signatureReturnSourcePlan?, typePlanEq,
          sourceRuleTokenPlanLayout, ruleTokenPlan?]

private theorem functionSignatureInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (genericPrefix : Option GenericPrefix)
    (publicToken : Option (MatchedTerminal file tokens
      (.hardKeyword .publicKw)))
    (payableToken : Option (MatchedTerminal file tokens
      (.hardKeyword .payableKw)))
    (functionKw : MatchedTerminal file tokens (.hardKeyword .functionKw))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (parameters : List Parameter)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (returnValue : Option
      (MatchedTerminal file tokens (.symbol .arrow) ×
        (TypeExpr × Unit)))
    (nameProjects : IdentifierProjects name.matched
      name.spelling name.parsed) :
    (functionSignatureInput genericPrefix publicToken payableToken
      functionKw name openParen parameters closeParen returnValue).tokenPlan?
        sourceRuleTokenPlanLayout = (do
      let genericPlan ← optionalGenericPlan? genericPrefix
      let parameterPlans ← parameters.mapM parameterTokenPlan?
      let returnPlan ← signatureReturnSourcePlan? returnValue
      pure (TokenPlan.concat [
        genericPlan,
        optionalKeywordPlan .publicKw publicToken,
        optionalKeywordPlan .payableKw payableToken,
        TokenPlan.exact (.hardKeyword .functionKw) functionKw.span,
        identifierPlan
          (RuleReduction.terminalLoc name.matched name.parsed),
        TokenPlan.concat [
          TokenPlan.exact (.symbol .leftParen) openParen.span,
          TokenPlan.commaSeparated parameterPlans,
          TokenPlan.exact (.symbol .rightParen) closeParen.span],
        returnPlan])) := by
  unfold functionSignatureInput
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
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValues.tokenPlan?_cons,
    parameterListInput_tokenPlan? parameters,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValues.tokenPlan?_cons,
    signatureReturnInput_tokenPlan? returnValue,
    EbnfValues.tokenPlan?_nil,
    matchedHardKeyword_physicalTokenPlan,
    matchedIdentifier_physicalTokenPlan name nameProjects,
    matchedSymbol_physicalTokenPlan,
    matchedSymbol_physicalTokenPlan]
  cases genericEq : optionalGenericPlan? genericPrefix <;>
    cases parametersEq : parameters.mapM parameterTokenPlan? <;>
    cases returnEq : signatureReturnSourcePlan? returnValue <;>
    simp [TokenPlan.concat_cons, TokenPlan.append_assoc]

private theorem functionSignaturePlan?_sourceLoc
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (genericPrefix : Option GenericPrefix)
    (publicToken : Option (MatchedTerminal file tokens
      (.hardKeyword .publicKw)))
    (payableToken : Option (MatchedTerminal file tokens
      (.hardKeyword .payableKw)))
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (parameters : List Parameter)
    (returnValue : Option
      (MatchedTerminal file tokens (.symbol .arrow) ×
        (TypeExpr × Unit)))
    (publicProjects : ∀ terminal, publicToken = some terminal →
      RuleReduction.MarkerProjects file tokens terminal .publicModifier)
    (payableProjects : ∀ terminal, payableToken = some terminal →
      RuleReduction.MarkerProjects file tokens terminal .payableModifier)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    functionSignaturePlan? (sourceLoc witness {
      genericPrefix := genericPrefix
      «public» := match publicToken with
        | none => none
        | some terminal => some (RuleReduction.marker terminal
            (publicProjects terminal rfl))
      payable := match payableToken with
        | none => none
        | some terminal => some (RuleReduction.marker terminal
            (payableProjects terminal rfl))
      name := RuleReduction.terminalLoc name.matched name.parsed
      parameters := parameters
      returnType := returnValue.map fun value => value.2.1
    } : FunctionSignature) = (do
      let genericPlan ← optionalGenericPlan? genericPrefix
      let parameterPlans ← parameters.mapM parameterTokenPlan?
      let returnPlan ← signatureReturnPlainPlan? returnValue
      pure (TokenPlan.enclose witness.span (TokenPlan.concat [
        genericPlan,
        optionalKeywordPlan .publicKw publicToken,
        optionalKeywordPlan .payableKw payableToken,
        TokenPlan.plain (.hardKeyword .functionKw),
        identifierPlan
          (RuleReduction.terminalLoc name.matched name.parsed),
        TokenPlan.parens (TokenPlan.commaSeparated parameterPlans),
        returnPlan]))) := by
  unfold functionSignaturePlan?
  simp only [sourceLoc]
  rwDeclarationPlansMapM
  unfoldSignatureOptionalPlanCore
  unfoldSignatureOptionalMarkerCore
  unfoldSignatureMarkerCore
  unfoldSignatureReturnCore
  cases genericPrefix <;>
    cases publicToken <;>
    cases payableToken <;>
    cases returnValue <;>
    simp [optionalGenericPlan?, optionalKeywordPlan,
      signatureReturnPlainPlan?, RuleReduction.marker,
      RuleReduction.terminalLoc, TokenPlan.concat_cons]

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

private theorem signatureReturnPlan_conversion
    {file : WorkspaceFile} {tokens : List Token}
    (returnValue : Option
      (MatchedTerminal file tokens (.symbol .arrow) ×
        (TypeExpr × Unit)))
    (sourcePlan : TokenPlan)
    (sourceSuccess : signatureReturnSourcePlan? returnValue =
      some sourcePlan) :
    ∃ plainPlan,
      signatureReturnPlainPlan? returnValue = some plainPlan ∧
      (∀ actual,
        TokenSlot.ListMatches sourcePlan.slots actual →
          TokenSlot.ListMatches plainPlan.slots actual) ∧
      plainPlan.WellAnchored := by
  cases returnValue with
  | none =>
      simp [signatureReturnSourcePlan?] at sourceSuccess
      subst sourcePlan
      refine ⟨TokenPlan.empty, rfl, ?_, TokenPlan.WellAnchored.empty⟩
      intro actual relation
      exact relation
  | some value =>
      cases typeEq : typeExprPlan? value.2.1 with
      | none =>
          simp [signatureReturnSourcePlan?, typeEq] at sourceSuccess
      | some typePlan =>
          simp [signatureReturnSourcePlan?, typeEq] at sourceSuccess
          subst sourcePlan
          let plainPlan :=
            (TokenPlan.plain (.symbol .arrow)).append typePlan
          refine ⟨plainPlan, ?_, ?_, ?_⟩
          · simp [signatureReturnPlainPlan?, typeEq, plainPlan]
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

/-- Function signatures retain recursive child plans and exact modifier/name
locations while weakening only fixed grammar punctuation. -/
theorem functionSignature_tokenPlanSound :
    GrammarRuleTokenPlanSound .functionSignature := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  change TokenPlanEvidence (functionSignaturePlan? output)
    (PhysicalTokens tokens origin finish)
  cases reduces with
  | functionSignature origin finish genericPrefix publicToken payableToken
      functionKw name openParen parameters closeParen returnValue
      publicProjects payableProjects nameProjects witness =>
      let namePlan := identifierPlan
        (RuleReduction.terminalLoc name.matched name.parsed)
      let publicPlan := optionalKeywordPlan .publicKw publicToken
      let payablePlan := optionalKeywordPlan .payableKw payableToken
      rw [EbnfValue.tokenPlan?_transport] at inputEvidence
      change TokenPlanEvidence
        ((functionSignatureInput genericPrefix publicToken payableToken
          functionKw name openParen parameters closeParen
          returnValue).tokenPlan? sourceRuleTokenPlanLayout)
        (PhysicalTokens tokens origin finish) at inputEvidence
      have candidateEq :
          (functionSignatureInput genericPrefix publicToken payableToken
            functionKw name openParen parameters closeParen
            returnValue).tokenPlan? sourceRuleTokenPlanLayout = (do
          let genericPlan ← optionalGenericPlan? genericPrefix
          let parameterPlans ← parameters.mapM parameterTokenPlan?
          let returnPlan ← signatureReturnSourcePlan? returnValue
          pure (TokenPlan.concat [
            genericPlan,
            publicPlan,
            payablePlan,
            TokenPlan.exact (.hardKeyword .functionKw) functionKw.span,
            namePlan,
            TokenPlan.concat [
              TokenPlan.exact (.symbol .leftParen) openParen.span,
              TokenPlan.commaSeparated parameterPlans,
            TokenPlan.exact (.symbol .rightParen) closeParen.span],
            returnPlan])) := by
        simpa [namePlan, publicPlan, payablePlan] using
          functionSignatureInput_tokenPlan? genericPrefix publicToken
            payableToken functionKw name openParen parameters closeParen
            returnValue nameProjects
      have physicalEvidence := inputEvidence.candidate_eq candidateEq
      cases genericEq : optionalGenericPlan? genericPrefix with
      | none =>
          simp [genericEq, TokenPlanEvidence] at physicalEvidence
      | some genericPlan =>
          cases parametersEq : parameters.mapM parameterTokenPlan? with
          | none =>
              simp [genericEq, parametersEq, TokenPlanEvidence]
                at physicalEvidence
          | some parameterPlans =>
              cases returnSourceEq :
                  signatureReturnSourcePlan? returnValue with
              | none =>
                  simp [genericEq, parametersEq, returnSourceEq,
                    TokenPlanEvidence] at physicalEvidence
              | some sourceReturnPlan =>
                  simp only [genericEq, parametersEq, returnSourceEq]
                    at physicalEvidence
                  let sourceParameterPlan := TokenPlan.concat [
                    TokenPlan.exact (.symbol .leftParen) openParen.span,
                    TokenPlan.commaSeparated parameterPlans,
                    TokenPlan.exact (.symbol .rightParen) closeParen.span]
                  let plainParameterPlan :=
                    TokenPlan.parens
                      (TokenPlan.commaSeparated parameterPlans)
                  let sourceCore := TokenPlan.concat [
                    genericPlan,
                    publicPlan,
                    payablePlan,
                    TokenPlan.exact (.hardKeyword .functionKw)
                      functionKw.span,
                    namePlan,
                    sourceParameterPlan,
                    sourceReturnPlan]
                  rcases physicalEvidence with ⟨plan, planEq, relation⟩
                  change some sourceCore = some plan at planEq
                  injection planEq with planEq
                  subst plan
                  let beforeFunction := TokenPlan.concat [
                    genericPlan, publicPlan, payablePlan]
                  let afterFunction := TokenPlan.concat [
                    namePlan, sourceParameterPlan, sourceReturnPlan]
                  have functionShape : TokenSlot.ListMatches
                      (beforeFunction.append
                        ((TokenPlan.exact (.hardKeyword .functionKw)
                          functionKw.span).append afterFunction)).slots
                      (PhysicalTokens tokens origin finish) := by
                    simpa [sourceCore, beforeFunction, afterFunction,
                      TokenPlan.concat_cons, TokenPlan.append_assoc] using
                        relation
                  have functionConverted :=
                    TokenSlot.ListMatches.exactBetweenToPlain functionShape
                  let functionCore := TokenPlan.concat [
                    genericPlan,
                    publicPlan,
                    payablePlan,
                    TokenPlan.plain (.hardKeyword .functionKw),
                    namePlan,
                    sourceParameterPlan,
                    sourceReturnPlan]
                  have functionRelation : TokenSlot.ListMatches
                      functionCore.slots
                      (PhysicalTokens tokens origin finish) := by
                    simpa [functionCore, beforeFunction, afterFunction,
                      TokenPlan.concat_cons, TokenPlan.append_assoc] using
                        functionConverted
                  let beforeParameters := TokenPlan.concat [
                    genericPlan,
                    publicPlan,
                    payablePlan,
                    TokenPlan.plain (.hardKeyword .functionKw),
                    namePlan]
                  have parameterShape : TokenSlot.ListMatches
                      (beforeParameters.append
                        (sourceParameterPlan.append sourceReturnPlan)).slots
                      (PhysicalTokens tokens origin finish) := by
                    simpa [functionCore, beforeParameters,
                      TokenPlan.concat_cons, TokenPlan.append_assoc] using
                        functionRelation
                  have parameterConverted :=
                    TokenSlot.ListMatches.replaceMiddle
                      (before := beforeParameters)
                      (source := sourceParameterPlan)
                      (target := plainParameterPlan)
                      (after := sourceReturnPlan)
                      (fun part partRelation =>
                        TokenSlot.ListMatches.exactParensToPlain partRelation)
                      parameterShape
                  let parameterCore := TokenPlan.concat [
                    genericPlan,
                    publicPlan,
                    payablePlan,
                    TokenPlan.plain (.hardKeyword .functionKw),
                    namePlan,
                    plainParameterPlan,
                    sourceReturnPlan]
                  have parameterRelation : TokenSlot.ListMatches
                      parameterCore.slots
                      (PhysicalTokens tokens origin finish) := by
                    simpa [parameterCore, beforeParameters,
                      TokenPlan.concat_cons, TokenPlan.append_assoc] using
                        parameterConverted
                  rcases signatureReturnPlan_conversion returnValue
                      sourceReturnPlan returnSourceEq with
                    ⟨plainReturnPlan, plainReturnEq,
                      convertReturn, returnAnchored⟩
                  let beforeReturn := TokenPlan.concat [
                    genericPlan,
                    publicPlan,
                    payablePlan,
                    TokenPlan.plain (.hardKeyword .functionKw),
                    namePlan,
                    plainParameterPlan]
                  have returnShape : TokenSlot.ListMatches
                      (beforeReturn.append
                        (sourceReturnPlan.append TokenPlan.empty)).slots
                      (PhysicalTokens tokens origin finish) := by
                    simpa [parameterCore, beforeReturn,
                      TokenPlan.concat_cons, TokenPlan.append_assoc] using
                        parameterRelation
                  have returnConverted :=
                    TokenSlot.ListMatches.replaceMiddle
                      (before := beforeReturn)
                      (source := sourceReturnPlan)
                      (target := plainReturnPlan)
                      (after := TokenPlan.empty)
                      convertReturn
                      returnShape
                  let plainCore := TokenPlan.concat [
                    genericPlan,
                    publicPlan,
                    payablePlan,
                    TokenPlan.plain (.hardKeyword .functionKw),
                    namePlan,
                    plainParameterPlan,
                    plainReturnPlan]
                  have plainRelation : TokenSlot.ListMatches plainCore.slots
                      (PhysicalTokens tokens origin finish) := by
                    simpa [plainCore, beforeReturn,
                      TokenPlan.concat_cons, TokenPlan.append_assoc] using
                        returnConverted
                  have genericAnchored := optionalGenericPlan_wellAnchored
                    genericPrefix genericPlan genericEq
                  have plainAnchored : plainCore.WellAnchored := by
                    apply TokenPlan.WellAnchored.concat
                    intro candidate member
                    simp only [List.mem_cons, List.not_mem_nil, or_false]
                      at member
                    rcases member with
                      rfl | rfl | rfl | rfl | rfl | rfl | rfl
                    · exact genericAnchored
                    · exact optionalKeywordPlan_wellAnchored
                        .publicKw publicToken
                    · exact optionalKeywordPlan_wellAnchored
                        .payableKw payableToken
                    · exact TokenPlan.WellAnchored.plain _
                    · exact identifierPlan_wellAnchored _
                    · exact TokenPlan.WellAnchored.parens _
                    · exact returnAnchored
                  have enclosed := TokenPlanEvidence.enclose
                    (TokenPlanEvidence.some plainRelation)
                    (fun candidate success => by
                      simp only [Option.some.injEq] at success
                      subst candidate
                      exact plainAnchored)
                    witness.consumed
                  apply enclosed.candidate_eq
                  revert publicProjects payableProjects
                  cases publicToken <;> cases payableToken <;>
                    intro publicProjects payableProjects
                  all_goals
                    have outputEq := functionSignaturePlan?_sourceLoc
                      genericPrefix _ _ name parameters returnValue
                      publicProjects payableProjects witness
                    rw [genericEq, parametersEq, plainReturnEq] at outputEq
                    simpa [plainCore, namePlan, publicPlan, payablePlan,
                      plainParameterPlan, RuleReduction.marker,
                      RuleReduction.terminalLoc] using outputEq.symm

private theorem functionSignaturePlan_startsRequired
    (signature : FunctionSignature) (plan : TokenPlan)
    (success : functionSignaturePlan? signature = some plan) :
    TokenPlan.WellAnchored.StartsRequired plan := by
  unfold functionSignaturePlan? at success
  have genericResult := Option.bind_eq_some_iff.mp success
  rcases genericResult with ⟨generic, genericEq, success⟩
  have publicResult := Option.bind_eq_some_iff.mp success
  rcases publicResult with ⟨publicModifier, publicEq, success⟩
  have payableResult := Option.bind_eq_some_iff.mp success
  rcases payableResult with ⟨payableModifier, payableEq, success⟩
  have parametersResult := Option.bind_eq_some_iff.mp success
  rcases parametersResult with ⟨parameters, _parametersEq, success⟩
  have returnResult := Option.bind_eq_some_iff.mp success
  rcases returnResult with ⟨returnType, _returnEq, resultEq⟩
  injection resultEq with planEq
  subst plan
  have genericAnchored : generic.WellAnchored := by
    cases genericOptionEq : signature.payload.genericPrefix with
    | none =>
        rw [genericOptionEq] at genericEq
        change some TokenPlan.empty = some generic at genericEq
        injection genericEq with equality
        subst generic
        exact TokenPlan.WellAnchored.empty
    | some genericValue =>
        rw [genericOptionEq] at genericEq
        change genericPrefixPlan? genericValue = some generic at genericEq
        exact genericPrefixPlan?_wellAnchored _ _ genericEq
  have publicAnchored : publicModifier.WellAnchored := by
    cases publicOptionEq : signature.payload.public with
    | none =>
        rw [publicOptionEq] at publicEq
        change some TokenPlan.empty = some publicModifier at publicEq
        injection publicEq with equality
        subst publicModifier
        exact TokenPlan.WellAnchored.empty
    | some marker =>
        rw [publicOptionEq] at publicEq
        change (if marker.payload = .publicModifier then
            some (.exact (.hardKeyword .publicKw) marker.span)
          else none) = some publicModifier at publicEq
        by_cases markerRole : marker.payload = .publicModifier
        · simp [markerRole] at publicEq
          subst publicModifier
          exact TokenPlan.WellAnchored.exact _ _
        · simp [markerRole] at publicEq
  have payableAnchored : payableModifier.WellAnchored := by
    cases payableOptionEq : signature.payload.payable with
    | none =>
        rw [payableOptionEq] at payableEq
        change some TokenPlan.empty = some payableModifier at payableEq
        injection payableEq with equality
        subst payableModifier
        exact TokenPlan.WellAnchored.empty
    | some marker =>
        rw [payableOptionEq] at payableEq
        change (if marker.payload = .payableModifier then
            some (.exact (.hardKeyword .payableKw) marker.span)
          else none) = some payableModifier at payableEq
        by_cases markerRole : marker.payload = .payableModifier
        · simp [markerRole] at payableEq
          subst payableModifier
          exact TokenPlan.WellAnchored.exact _ _
        · simp [markerRole] at payableEq
  have suffixStarts :=
    TokenPlan.WellAnchored.StartsRequired.concat_plain_first
      (.hardKeyword .functionKw)
      [identifierPlan signature.payload.name,
        .parens (.commaSeparated parameters), returnType]
  apply TokenPlan.WellAnchored.StartsRequired.enclose
  simpa [TokenPlan.concat, TokenPlan.append] using
    TokenPlan.WellAnchored.StartsRequired.prepend_anchored genericAnchored
      (TokenPlan.WellAnchored.StartsRequired.prepend_anchored publicAnchored
        (TokenPlan.WellAnchored.StartsRequired.prepend_anchored
          payableAnchored suffixStarts))

private theorem bracedBodyPlan_endsRequired
    (body : Body) (plan : TokenPlan)
    (success : bodyTokenPlan? .braced body = some plan) :
    TokenPlan.WellAnchored.EndsRequired plan := by
  rcases body with ⟨bodySpan, bodyOrigin, statements⟩
  cases bodyOrigin with
  | braced openBrace closeBrace =>
      unfold bodyTokenPlan? at success
      have statementsResult := Option.bind_eq_some_iff.mp success
      rcases statementsResult with
        ⟨statementPlans, _statementPlansEq, resultEq⟩
      unfold bracedBodyPlanWith? at resultEq
      injection resultEq with planEq
      subst plan
      apply TokenPlan.WellAnchored.EndsRequired.enclose
      apply TokenPlan.WellAnchored.EndsRequired.concat_exact_last_two
  | matchArm fatArrow =>
      simp [bodyTokenPlan?] at success

/-- Constructor reductions preserve their name and optional field list while
weakening the two fixed parentheses supplied by the grammar. -/
theorem dataConstructor_tokenPlanSound :
    GrammarRuleTokenPlanSound .dataConstructor := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | dataConstructorWithoutArguments origin finish name nameProjects witness =>
      rw [← inputEq] at inputEvidence
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          some (identifierPlan
            (RuleReduction.terminalLoc name.matched name.parsed)) := by
        rw [inputEq]
        simp [m2cV1, m2cV1Rhs, Grammar.identifier, Grammar.category,
          Grammar.terminal, Grammar.sequence, Grammar.symbol,
          Grammar.nonterminal, Grammar.optional,
          sourceRuleTokenPlanLayout,
          matchedIdentifier_physicalTokenPlan name nameProjects]
      have coreEvidence := inputEvidence.candidate_eq candidateEq
      have enclosed := TokenPlanEvidence.enclose coreEvidence
        (fun plan success => by
          simp only [Option.some.injEq] at success
          subst plan
          exact identifierPlan_wellAnchored _)
        witness.consumed
      change TokenPlanEvidence
        (some (TokenPlan.enclose witness.span
          (identifierPlan
            (RuleReduction.terminalLoc name.matched name.parsed)))) _
      exact enclosed
  | dataConstructorWithArguments origin finish name openParen fields
      closeParen nameProjects witness =>
      rw [← inputEq] at inputEvidence
      change TokenPlanEvidence
        (dataConstructorPlan? (sourceLoc witness {
          name := RuleReduction.terminalLoc name.matched name.parsed
          fields := some fields
        } : DataConstructor)) _
      let namePlan := identifierPlan
        (RuleReduction.terminalLoc name.matched name.parsed)
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          (do
            let headPlan ← ruleTokenPlan? .type fields.head
            let tailPlans ← fields.tail.mapM (ruleTokenPlan? .type)
            pure (namePlan.append (TokenPlan.concat [
              TokenPlan.exact (.symbol .leftParen) openParen.span,
              TokenPlan.commaSeparated (headPlan :: tailPlans),
              TokenPlan.exact (.symbol .rightParen) closeParen.span]))) := by
        rw [inputEq]
        simp only [m2cV1, m2cV1Rhs, Grammar.identifier, Grammar.category,
          Grammar.terminal, Grammar.sequence, Grammar.symbol,
          Grammar.nonterminal, Grammar.optional, Grammar.list1]
        rw [EbnfValue.tokenPlan?_transport]
        change (dataConstructorWithArgumentsInput name openParen fields
          closeParen).tokenPlan? sourceRuleTokenPlanLayout = _
        simpa [namePlan, TokenPlan.concat_cons] using
          dataConstructorWithArgumentsInput_tokenPlan? name openParen fields
            closeParen nameProjects
      have physicalEvidence := inputEvidence.candidate_eq candidateEq
      cases headEq : ruleTokenPlan? .type fields.head with
      | none =>
          simp [headEq, TokenPlanEvidence] at physicalEvidence
      | some headPlan =>
          cases tailEq : fields.tail.mapM (ruleTokenPlan? .type) with
          | none =>
              simp [headEq, tailEq, TokenPlanEvidence] at physicalEvidence
          | some tailPlans =>
              simp only [headEq, tailEq] at physicalEvidence
              let middle :=
                TokenPlan.commaSeparated (headPlan :: tailPlans)
              rcases physicalEvidence with ⟨plan, planEq, relation⟩
              change some (namePlan.append (TokenPlan.concat [
                TokenPlan.exact (.symbol .leftParen) openParen.span,
                middle,
                TokenPlan.exact (.symbol .rightParen) closeParen.span])) =
                  some plan at planEq
              injection planEq with planEq
              subst plan
              rcases relation.split_append with
                ⟨nameActual, fieldsActual, actualEq,
                  nameRelation, fieldsRelation⟩
              have fieldsPlain :=
                TokenSlot.ListMatches.exactParensToPlain fieldsRelation
              have coreRelation : TokenSlot.ListMatches
                  (namePlan.append (TokenPlan.parens middle)).slots
                  (PhysicalTokens tokens origin finish) := by
                rw [actualEq]
                exact nameRelation.append fieldsPlain
              have coreAnchored :
                  (namePlan.append (TokenPlan.parens middle)).WellAnchored := by
                apply TokenPlan.WellAnchored.append
                  (identifierPlan_wellAnchored _)
                exact TokenPlan.WellAnchored.parens _
              have enclosed := TokenPlanEvidence.enclose
                (TokenPlanEvidence.some coreRelation)
                (fun candidate success => by
                  simp only [Option.some.injEq] at success
                  subst candidate
                  exact coreAnchored)
                witness.consumed
              have headTypeEq : typeExprPlan? fields.head =
                  some headPlan := by
                simpa only [ruleTokenPlan?] using headEq
              have tailTypeEq : fields.tail.mapM typeExprPlan? =
                  some tailPlans := by
                change fields.tail.mapM typeExprPlan? =
                  some tailPlans at tailEq
                exact tailEq
              have nonemptyPlansEq :
                  nonemptyTypeExprPlans? fields =
                    some (headPlan :: tailPlans) := by
                rw [nonemptyTypeExprPlans_eq_mapM,
                  headTypeEq, tailTypeEq]
                rfl
              apply enclosed.candidate_eq
              unfold dataConstructorPlan?
              simp only [sourceLoc]
              unfoldOptionalNonemptyTypePlanCore
              unfoldNonemptyTypePlanCore
              simp only
              rw [nonemptyPlansEq]
              simp [namePlan, middle]

/-- Type-alias reductions preserve all identifier and type evidence while
weakening only grammar-fixed punctuation and enclosing the checked span. -/
theorem typeAliasDecl_tokenPlanSound :
    GrammarRuleTokenPlanSound .typeAliasDecl := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | typeAliasDecl origin finish typeKw name parameters equal body semicolon
      nameProjects parameterProjects witness =>
      rw [← inputEq] at inputEvidence
      change TokenPlanEvidence
        (typeAliasDeclPlan? (sourceLoc witness {
          name := RuleReduction.terminalLoc name.matched name.parsed
          parameters := parameters.map fun value =>
            value.2.1.map fun parameter =>
              RuleReduction.terminalLoc parameter.matched parameter.parsed
          body := body
        } : TypeAliasDecl)) _
      let namePlan := identifierPlan
        (RuleReduction.terminalLoc name.matched name.parsed)
      let sourceParameters := typeAliasParameterSourcePlan parameters
      let plainParameters := typeAliasParameterPlainPlan parameters
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout = (do
          let bodyPlan ← ruleTokenPlan? .type body
          pure (TokenPlan.concat [
            TokenPlan.exact (.hardKeyword .typeKw) typeKw.span,
            namePlan,
            sourceParameters,
            TokenPlan.exact (.symbol .equal) equal.span,
            bodyPlan,
            TokenPlan.exact (.symbol .semicolon) semicolon.span])) := by
        rw [inputEq]
        simp only [m2cV1, m2cV1Rhs, Grammar.hardKeyword,
          Grammar.identifier, Grammar.category, Grammar.terminal,
          Grammar.sequence, Grammar.symbol, Grammar.nonterminal,
          Grammar.optional, Grammar.list1]
        rw [EbnfValue.tokenPlan?_transport]
        change (typeAliasInput typeKw name parameters equal body
          semicolon).tokenPlan? sourceRuleTokenPlanLayout = _
        simpa [namePlan, sourceParameters] using
          typeAliasInput_tokenPlan? typeKw name parameters equal body
            semicolon nameProjects parameterProjects
      have physicalEvidence := inputEvidence.candidate_eq candidateEq
      cases bodyEq : ruleTokenPlan? .type body with
      | none =>
          simp [bodyEq, TokenPlanEvidence] at physicalEvidence
      | some bodyPlan =>
          simp only [bodyEq] at physicalEvidence
          let sourceCore := TokenPlan.concat [
            TokenPlan.exact (.hardKeyword .typeKw) typeKw.span,
            namePlan,
            sourceParameters,
            TokenPlan.exact (.symbol .equal) equal.span,
            bodyPlan,
            TokenPlan.exact (.symbol .semicolon) semicolon.span]
          rcases physicalEvidence with ⟨plan, planEq, relation⟩
          change some sourceCore = some plan at planEq
          injection planEq with planEq
          subst plan
          let beforeParameters := TokenPlan.concat [
            TokenPlan.exact (.hardKeyword .typeKw) typeKw.span,
            namePlan]
          let afterParameters := TokenPlan.concat [
            TokenPlan.exact (.symbol .equal) equal.span,
            bodyPlan,
            TokenPlan.exact (.symbol .semicolon) semicolon.span]
          have parameterShape : TokenSlot.ListMatches
              (beforeParameters.append
                (sourceParameters.append afterParameters)).slots
              (PhysicalTokens tokens origin finish) := by
            simpa [sourceCore, beforeParameters, afterParameters,
              TokenPlan.concat_cons, TokenPlan.append_assoc] using relation
          have replacedParameters :=
            TokenSlot.ListMatches.replaceMiddle
              (before := beforeParameters)
              (source := sourceParameters)
              (target := plainParameters)
              (after := afterParameters)
              (fun part partRelation =>
                typeAliasParameterSourcePlan_toPlain parameters partRelation)
              parameterShape
          let parameterCore := TokenPlan.concat [
            TokenPlan.exact (.hardKeyword .typeKw) typeKw.span,
            namePlan,
            plainParameters,
            TokenPlan.exact (.symbol .equal) equal.span,
            bodyPlan,
            TokenPlan.exact (.symbol .semicolon) semicolon.span]
          have parameterRelation : TokenSlot.ListMatches parameterCore.slots
              (PhysicalTokens tokens origin finish) := by
            simpa [parameterCore, beforeParameters, afterParameters,
              TokenPlan.concat_cons, TokenPlan.append_assoc] using
                replacedParameters
          let keywordCore := TokenPlan.concat [
            TokenPlan.plain (.hardKeyword .typeKw),
            namePlan,
            plainParameters,
            TokenPlan.exact (.symbol .equal) equal.span,
            bodyPlan,
            TokenPlan.exact (.symbol .semicolon) semicolon.span]
          have keywordRelation : TokenSlot.ListMatches keywordCore.slots
              (PhysicalTokens tokens origin finish) := by
            have converted := TokenSlot.ListMatches.exactBetweenToPlain
              (left := TokenPlan.empty)
              (right := TokenPlan.concat [
                namePlan,
                plainParameters,
                TokenPlan.exact (.symbol .equal) equal.span,
                bodyPlan,
                TokenPlan.exact (.symbol .semicolon) semicolon.span])
              (kind := .hardKeyword .typeKw)
              (span := typeKw.span)
              (by
                simpa [parameterCore, TokenPlan.concat_cons,
                  TokenPlan.append_assoc] using parameterRelation)
            simpa [keywordCore, TokenPlan.concat_cons,
              TokenPlan.append_assoc] using converted
          let equalCore := TokenPlan.concat [
            TokenPlan.plain (.hardKeyword .typeKw),
            namePlan,
            plainParameters,
            TokenPlan.plain (.symbol .equal),
            bodyPlan,
            TokenPlan.exact (.symbol .semicolon) semicolon.span]
          have equalRelation : TokenSlot.ListMatches equalCore.slots
              (PhysicalTokens tokens origin finish) := by
            have converted := TokenSlot.ListMatches.exactBetweenToPlain
              (left := TokenPlan.concat [
                TokenPlan.plain (.hardKeyword .typeKw),
                namePlan,
                plainParameters])
              (right := TokenPlan.concat [
                bodyPlan,
                TokenPlan.exact (.symbol .semicolon) semicolon.span])
              (kind := .symbol .equal)
              (span := equal.span)
              (by
                simpa [keywordCore, TokenPlan.concat_cons,
                  TokenPlan.append_assoc] using keywordRelation)
            simpa [equalCore, TokenPlan.concat_cons,
              TokenPlan.append_assoc] using converted
          let plainCore := TokenPlan.concat [
            TokenPlan.plain (.hardKeyword .typeKw),
            namePlan,
            plainParameters,
            TokenPlan.plain (.symbol .equal),
            bodyPlan,
            TokenPlan.plain (.symbol .semicolon)]
          have plainRelation : TokenSlot.ListMatches plainCore.slots
              (PhysicalTokens tokens origin finish) := by
            have converted := TokenSlot.ListMatches.exactBetweenToPlain
              (left := TokenPlan.concat [
                TokenPlan.plain (.hardKeyword .typeKw),
                namePlan,
                plainParameters,
                TokenPlan.plain (.symbol .equal),
                bodyPlan])
              (right := TokenPlan.empty)
              (kind := .symbol .semicolon)
              (span := semicolon.span)
              (by
                simpa [equalCore, TokenPlan.concat_cons,
                  TokenPlan.append_assoc] using equalRelation)
            simpa [plainCore, TokenPlan.concat_cons,
              TokenPlan.append_assoc] using converted
          have plainAnchored : plainCore.WellAnchored := by
            exact TokenPlan.WellAnchored.concat_plain_bookended_four
              (.hardKeyword .typeKw) (.symbol .semicolon)
              namePlan plainParameters
              (TokenPlan.plain (.symbol .equal)) bodyPlan
          have enclosed := TokenPlanEvidence.enclose
            (TokenPlanEvidence.some plainRelation)
            (fun candidate success => by
              simp only [Option.some.injEq] at success
              subst candidate
              exact plainAnchored)
            witness.consumed
          have bodyTypeEq : typeExprPlan? body = some bodyPlan := by
            simpa only [ruleTokenPlan?] using bodyEq
          apply enclosed.candidate_eq
          rw [typeAliasDeclPlan?_sourceLoc typeKw name parameters equal body
            semicolon witness]
          rw [bodyTypeEq]
          simp [plainCore, namePlan, plainParameters]

/-- Function declarations concatenate the exact signature and braced-body
plans, then retain the declaration's checked outer span. -/
theorem functionDecl_tokenPlanSound :
    GrammarRuleTokenPlanSound .functionDecl := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | functionDecl origin finish signature body witness =>
      rw [← inputEq] at inputEvidence
      change TokenPlanEvidence
        (functionDeclPlan? (sourceLoc witness {
          signature := signature
          body := body
        } : FunctionDecl)) _
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout = (do
          let signaturePlan ← ruleTokenPlan? .functionSignature signature
          let bodyPlan ← ruleTokenPlan? .body body
          pure (signaturePlan.append bodyPlan)) := by
        rw [inputEq]
        simp [m2cV1, m2cV1Rhs, Grammar.sequence,
          Grammar.nonterminal, sourceRuleTokenPlanLayout]
      have physicalEvidence := inputEvidence.candidate_eq candidateEq
      cases signatureEq : functionSignaturePlan? signature with
      | none =>
          simp [signatureEq, ruleTokenPlan?, TokenPlanEvidence]
            at physicalEvidence
      | some signaturePlan =>
          cases bodyEq : bodyTokenPlan? .braced body with
          | none =>
              simp [signatureEq, bodyEq, ruleTokenPlan?, TokenPlanEvidence]
                at physicalEvidence
          | some bodyPlan =>
              simp [signatureEq, bodyEq, ruleTokenPlan?] at physicalEvidence
              let corePlan := signaturePlan.append bodyPlan
              have coreAnchored : corePlan.WellAnchored := by
                exact TokenPlan.WellAnchored.of_starts_ends_append
                  (functionSignaturePlan_startsRequired signature
                    signaturePlan signatureEq)
                  (bracedBodyPlan_endsRequired body bodyPlan bodyEq)
              have enclosed := TokenPlanEvidence.enclose physicalEvidence
                (fun candidate success => by
                  simp only [Option.some.injEq] at success
                  subst candidate
                  exact coreAnchored)
                witness.consumed
              apply enclosed.candidate_eq
              unfold functionDeclPlan?
              simp [sourceLoc, signatureEq, bodyEq]

/-- Class methods preserve their signature and exact terminator, then retain
the checked source interval of the declaration. -/
theorem classMethod_tokenPlanSound :
    GrammarRuleTokenPlanSound .classMethod := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | classMethod origin finish signature semicolon witness =>
      rw [← inputEq] at inputEvidence
      change TokenPlanEvidence
        (classMethodDeclPlan? (sourceLoc witness {
          signature := signature
          terminator := semicolon.span
        } : ClassMethodDecl)) _
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout = (do
          let signaturePlan ← ruleTokenPlan? .functionSignature signature
          pure (signaturePlan.append
            (TokenPlan.exact (.symbol .semicolon) semicolon.span))) := by
        rw [inputEq]
        simp [m2cV1, m2cV1Rhs, Grammar.sequence,
          Grammar.nonterminal, Grammar.symbol, Grammar.terminal,
          sourceRuleTokenPlanLayout,
          matchedSymbol_physicalTokenPlan]
      have physicalEvidence := inputEvidence.candidate_eq candidateEq
      cases signatureEq : functionSignaturePlan? signature with
      | none =>
          simp [signatureEq, ruleTokenPlan?, TokenPlanEvidence]
            at physicalEvidence
      | some signaturePlan =>
          simp [signatureEq, ruleTokenPlan?] at physicalEvidence
          let corePlan := signaturePlan.append
            (TokenPlan.exact (.symbol .semicolon) semicolon.span)
          have coreAnchored : corePlan.WellAnchored := by
            exact TokenPlan.WellAnchored.of_starts_ends_append
              (functionSignaturePlan_startsRequired signature
                signaturePlan signatureEq)
              (by
                simpa [TokenPlan.concat] using
                  TokenPlan.WellAnchored.EndsRequired.concat_exact_last
                    [] (.symbol .semicolon) semicolon.span)
          have enclosed := TokenPlanEvidence.enclose physicalEvidence
            (fun candidate success => by
              simp only [Option.some.injEq] at success
              subst candidate
              exact coreAnchored)
            witness.consumed
          apply enclosed.candidate_eq
          unfold classMethodDeclPlan?
          simp [sourceLoc, signatureEq]

end Solcore.Surface.Multi
