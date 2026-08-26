import Solcore.Surface.Multi.ExactTokenExpressionAnchoring
import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRulePassThrough
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false
set_option linter.unnecessarySimpa false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

private theorem MatchedTerminal.physicalTokenPlan_contextualKeyword
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

private theorem TokenSlot.ListMatches.twoExactToPlain
    {firstKind secondKind : TokenKind}
    {firstSpan secondSpan : SourceSpan}
    {middle : TokenPlan} {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat [
        .exact firstKind firstSpan, middle,
        .exact secondKind secondSpan]).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.concat [
        .plain firstKind, middle,
        .plain secondKind]).slots actual := by
  simp only [TokenPlan.concat, List.flatMap_cons, List.flatMap_nil,
    TokenPlan.exact, TokenPlan.plain, List.append_nil,
    List.singleton_append] at relation ⊢
  cases relation with
  | required firstMatch afterFirst =>
      rcases afterFirst.split_append with
        ⟨middleActual, afterMiddleActual, rfl,
          middleRelation, afterMiddleRelation⟩
      cases afterMiddleRelation with
      | required secondMatch afterSecond =>
          exact .required firstMatch.toPlain <|
            middleRelation.append <|
              .required secondMatch.toPlain afterSecond

private theorem TokenSlot.ListMatches.exactHeadAndTwoExactToPlain
    {headKind firstKind secondKind : TokenKind}
    {headSpan firstSpan secondSpan : SourceSpan}
    {before middle : TokenPlan} {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat [
        .exact headKind headSpan, before,
        .exact firstKind firstSpan, middle,
        .exact secondKind secondSpan]).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.concat [
        .exact headKind headSpan, before,
        .plain firstKind, middle,
        .plain secondKind]).slots actual := by
  simp only [TokenPlan.concat, List.flatMap_cons, List.flatMap_nil,
    TokenPlan.exact, TokenPlan.plain, List.append_nil,
    List.singleton_append] at relation ⊢
  cases relation with
  | required headMatch afterHead =>
      rcases afterHead.split_append with
        ⟨beforeActual, afterBeforeActual, rfl,
          beforeRelation, afterBeforeRelation⟩
      cases afterBeforeRelation with
      | required firstMatch afterFirst =>
          rcases afterFirst.split_append with
            ⟨middleActual, afterMiddleActual, rfl,
              middleRelation, afterMiddleRelation⟩
          cases afterMiddleRelation with
          | required secondMatch afterSecond =>
              exact .required headMatch <|
                beforeRelation.append <|
                  .required firstMatch.toPlain <|
                    middleRelation.append <|
                      .required secondMatch.toPlain afterSecond

private theorem TokenSlot.ListMatches.beforeAndTwoExactToPlain
    {firstKind secondKind : TokenKind}
    {firstSpan secondSpan : SourceSpan}
    {before middle : TokenPlan} {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat [
        before, .exact firstKind firstSpan, middle,
        .exact secondKind secondSpan]).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.concat [
        before, .plain firstKind, middle,
        .plain secondKind]).slots actual := by
  simp only [TokenPlan.concat, List.flatMap_cons, List.flatMap_nil,
    TokenPlan.exact, TokenPlan.plain, List.append_nil,
    List.singleton_append] at relation ⊢
  rcases relation.split_append with
    ⟨beforeActual, afterBeforeActual, rfl,
      beforeRelation, afterBeforeRelation⟩
  cases afterBeforeRelation with
  | required firstMatch afterFirst =>
      rcases afterFirst.split_append with
        ⟨middleActual, afterMiddleActual, rfl,
          middleRelation, afterMiddleRelation⟩
      cases afterMiddleRelation with
      | required secondMatch afterSecond =>
          exact beforeRelation.append <|
            .required firstMatch.toPlain <|
              middleRelation.append <|
                .required secondMatch.toPlain afterSecond

private theorem TokenSlot.ListMatches.twoExactInterleavedToPlain
    {firstKind secondKind : TokenKind}
    {firstSpan secondSpan : SourceSpan}
    {firstPlan secondPlan : TokenPlan} {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat [
        .exact firstKind firstSpan, firstPlan,
        .exact secondKind secondSpan, secondPlan]).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.concat [
        .plain firstKind, firstPlan,
        .plain secondKind, secondPlan]).slots actual := by
  simp only [TokenPlan.concat, List.flatMap_cons, List.flatMap_nil,
    TokenPlan.exact, TokenPlan.plain, List.append_nil,
    List.singleton_append] at relation ⊢
  cases relation with
  | required firstMatch afterFirst =>
      rcases afterFirst.split_append with
        ⟨firstActual, afterFirstActual, rfl,
          firstRelation, afterFirstRelation⟩
      cases afterFirstRelation with
      | required secondMatch afterSecond =>
          exact .required firstMatch.toPlain <|
            firstRelation.append <|
              .required secondMatch.toPlain afterSecond

private theorem TokenPlanEvidence.exactToPlain
    {kind : TokenKind} {span : SourceSpan} {actual : List Token}
    (evidence : TokenPlanEvidence
      (Option.some (TokenPlan.exact kind span)) actual) :
    TokenPlanEvidence
      (Option.some (TokenPlan.plain kind)) actual := by
  rcases evidence with ⟨plan, success, relation⟩
  simp only [Option.some.injEq] at success
  subst plan
  exact TokenPlanEvidence.some relation.requiredHeadToPlain

private theorem patternPlans_eq_mapM (values : List Pattern) :
    patternTokenPlans? values =
      values.mapM (ruleTokenPlan? .pattern) := by
  change patternTokenPlans? values = values.mapM patternTokenPlan?
  induction values with
  | nil => simp [patternTokenPlans?]
  | cons head tail induction =>
      simp [patternTokenPlans?, induction]

private theorem patternPlans_eq_directMapM (values : List Pattern) :
    patternTokenPlans? values = values.mapM patternTokenPlan? := by
  induction values with
  | nil => simp [patternTokenPlans?]
  | cons head tail induction =>
      simp [patternTokenPlans?, induction]

private theorem optionMap_eq_bindPure
    {alpha beta : Type} (function : alpha → beta)
    (candidate : Option alpha) :
    candidate.map function = (do
      let value ← candidate
      pure (function value)) := by
  cases candidate <;> rfl

private theorem nonemptyPatternPlans_eq_mapM
    (values : NonemptyList Pattern) :
    nonemptyPatternTokenPlans? values = (do
      let headPlan ← ruleTokenPlan? .pattern values.head
      let tailPlans ← values.tail.mapM (ruleTokenPlan? .pattern)
      pure (headPlan :: tailPlans)) := by
  rcases values with ⟨head, tail⟩
  change nonemptyPatternTokenPlans? ⟨head, tail⟩ = _
  simp [nonemptyPatternTokenPlans?, patternPlans_eq_mapM,
    ruleTokenPlan?]

private theorem patternRuleValues_mapM_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (values : List Pattern) :
    (values.map (EbnfValue.ruleAtom
      (file := file) (tokens := tokens) .pattern)).mapM
        (fun value => value.tokenPlan? sourceRuleTokenPlanLayout) =
      values.mapM (ruleTokenPlan? .pattern) := by
  rw [List.mapM_map]
  simp [Function.comp_def, sourceRuleTokenPlanLayout]

/-- A nonempty grammar list of pattern rule values computes the same
comma-separated plan as the semantic nonempty-pattern visitor. -/
theorem nonemptyPatternRuleValues_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (values : NonemptyList Pattern) :
    (EbnfValue.list1 (.atom (.nonterminal .pattern))
      (values.map (EbnfValue.ruleAtom
        (file := file) (tokens := tokens) .pattern))).tokenPlan?
        sourceRuleTokenPlanLayout =
      (nonemptyPatternTokenPlans? values).map
        TokenPlan.commaSeparated := by
  rw [EbnfValue.tokenPlan?_list1]
  rcases values with ⟨head, tail⟩
  simp only [NonemptyList.map, EbnfValue.tokenPlan?_ruleAtom]
  rw [patternRuleValues_mapM_tokenPlan?]
  simp only [sourceRuleTokenPlanLayout]
  change (do
    let headPlan ← ruleTokenPlan? .pattern head
    let tailPlans ← tail.mapM (ruleTokenPlan? .pattern)
    pure (TokenPlan.commaSeparated (headPlan :: tailPlans))) = _
  rw [nonemptyPatternPlans_eq_mapM]
  symm
  change Option.map TokenPlan.commaSeparated (do
      let headPlan ← ruleTokenPlan? .pattern head
      let tailPlans ← tail.mapM (ruleTokenPlan? .pattern)
      pure (headPlan :: tailPlans)) = (do
    let headPlan ← ruleTokenPlan? .pattern head
    let tailPlans ← tail.mapM (ruleTokenPlan? .pattern)
    pure (TokenPlan.commaSeparated (headPlan :: tailPlans)))
  cases ruleTokenPlan? .pattern head <;>
    cases tail.mapM (ruleTokenPlan? .pattern) <;> rfl

private def patternTupleRestPlainPlan?
    {file : WorkspaceFile} {tokens : List Token} :
    List (MatchedTerminal file tokens (.symbol .comma) × Pattern) →
      Option TokenPlan
  | [] => some .empty
  | entry :: rest => do
      let patternPlan ← patternTokenPlan? entry.2
      let restPlan ← patternTupleRestPlainPlan? rest
      pure (((TokenPlan.plain (.symbol .comma)).append
        patternPlan).append restPlan)

private theorem patternTupleRestPlainPlan_eq
    {file : WorkspaceFile} {tokens : List Token}
    (rest : List
      (MatchedTerminal file tokens (.symbol .comma) × Pattern)) :
    patternTupleRestPlainPlan? rest = (do
      let plans ← (rest.map Prod.snd).mapM patternTokenPlan?
      pure (.concat (plans.map fun plan =>
        (TokenPlan.plain (.symbol .comma)).append plan))) := by
  induction rest with
  | nil => simp [patternTupleRestPlainPlan?, TokenPlan.concat,
      TokenPlan.empty]
  | cons entry rest induction =>
      rw [patternTupleRestPlainPlan?, List.map_cons,
        List.mapM_cons, induction]
      cases patternEq : patternTokenPlan? entry.2 <;>
        cases tailPlansEq : (rest.map Prod.snd).mapM
          patternTokenPlan? <;>
          simp [TokenPlan.concat, TokenPlan.append]

private abbrev patternTupleRestExpr : EbnfExpr :=
  .group (.sequence [
    .atom (.terminal (.symbol .comma)),
    .atom (.nonterminal .pattern)])

private def patternTupleRestValue
    {file : WorkspaceFile} {tokens : List Token}
    (entry : MatchedTerminal file tokens (.symbol .comma) × Pattern) :
    EbnfValue file tokens patternTupleRestExpr :=
  EbnfValue.group _ <| EbnfValue.sequence _ <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .comma) entry.1) <|
    EbnfValues.cons _ _
      (EbnfValue.ruleAtom .pattern entry.2) EbnfValues.nil

private theorem patternTupleRestValue_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (entry : MatchedTerminal file tokens (.symbol .comma) × Pattern) :
    (patternTupleRestValue entry).tokenPlan?
        sourceRuleTokenPlanLayout = (do
      let patternPlan ← patternTokenPlan? entry.2
      pure ((TokenPlan.exact (.symbol .comma) entry.1.span).append
        patternPlan)) := by
  cases patternEq : patternTokenPlan? entry.2 <;>
    simp [patternTupleRestValue, patternTupleRestExpr,
      sourceRuleTokenPlanLayout, ruleTokenPlan?, patternEq,
      MatchedTerminal.physicalTokenPlan_symbol,
      TokenPlan.append, TokenPlan.empty]

private theorem patternTupleRestEvidence_toPlain
    {file : WorkspaceFile} {tokens : List Token}
    (rest : List
      (MatchedTerminal file tokens (.symbol .comma) × Pattern))
    {actual : List Token}
    (evidence : TokenPlanEvidence
      ((EbnfValue.star patternTupleRestExpr
        (rest.map patternTupleRestValue)).tokenPlan?
          sourceRuleTokenPlanLayout) actual) :
    TokenPlanEvidence (patternTupleRestPlainPlan? rest) actual := by
  induction rest generalizing actual with
  | nil =>
      have flattened := evidence.candidate_eq
        (EbnfValue.tokenPlan?_star sourceRuleTokenPlanLayout
          patternTupleRestExpr [])
      simpa [patternTupleRestPlainPlan?, TokenPlan.concat,
        TokenPlan.empty] using flattened
  | cons entry rest induction =>
      have flattened := evidence.candidate_eq
        (EbnfValue.tokenPlan?_star sourceRuleTokenPlanLayout
          patternTupleRestExpr
          ((entry :: rest).map patternTupleRestValue))
      rw [List.map_cons, List.mapM_cons,
        patternTupleRestValue_tokenPlan?] at flattened
      cases patternEq : patternTokenPlan? entry.2 with
      | none =>
          rcases flattened with ⟨plan, success, relation⟩
          simp [patternEq] at success
      | some patternPlan =>
          cases tailPlansEq :
              (rest.map patternTupleRestValue).mapM
                (fun value => value.tokenPlan?
                  sourceRuleTokenPlanLayout) with
          | none =>
              rcases flattened with ⟨plan, success, relation⟩
              simp [patternEq, tailPlansEq]
                at success
          | some tailPlans =>
              have exactEvidence : TokenPlanEvidence
                  (Option.some ((TokenPlan.exact (.symbol .comma)
                    entry.1.span).append patternPlan |>.append
                      (TokenPlan.concat tailPlans)))
                  actual := by
                simpa [patternEq, tailPlansEq, TokenPlan.concat,
                  TokenPlan.append, TokenPlan.empty] using flattened
              rcases exactEvidence with ⟨plan, success, relation⟩
              simp only [Option.some.injEq] at success
              subst plan
              rcases relation.split_append with
                ⟨headActual, tailActual, actualEq,
                  headRelation, tailRelation⟩
              have headPlainRelation : TokenSlot.ListMatches
                  ((TokenPlan.plain (.symbol .comma)).append
                    patternPlan).slots headActual := by
                simpa [TokenPlan.append, TokenPlan.empty] using
                  (TokenSlot.ListMatches.exactBetweenToPlain
                    (left := TokenPlan.empty)
                    (right := patternPlan) headRelation)
              have headEvidence := TokenPlanEvidence.some headPlainRelation
              have tailEvidence : TokenPlanEvidence
                  ((EbnfValue.star patternTupleRestExpr
                    (rest.map patternTupleRestValue)).tokenPlan?
                      sourceRuleTokenPlanLayout) tailActual := by
                refine ⟨TokenPlan.concat tailPlans, ?_, tailRelation⟩
                rw [EbnfValue.tokenPlan?_star, tailPlansEq]
                rfl
              have tailPlainEvidence := induction tailEvidence
              have combined := headEvidence.append tailPlainEvidence
              have onActual := combined.actual_eq actualEq.symm
              apply onActual.candidate_eq
              simp [patternTupleRestPlainPlan?, patternEq,
                TokenPlan.append_assoc]

/-- Pattern reductions preserve complete source-token evidence. -/
theorem pattern_tokenPlanSound :
    GrammarRuleTokenPlanSound .pattern := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  cases reduces with
  | patternWildcard origin finish underscore witness =>
      change TokenPlanEvidence
        (patternTokenPlan? (sourceLoc witness
          (.wildcard
            (RuleReduction.marker underscore
              (.wildcardUnderscore underscore)))))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have terminalEvidence := selected.candidate_eq
        (EbnfValue.tokenPlan?_terminalAtom
          sourceRuleTokenPlanLayout _ underscore)
      have coreEvidence : TokenPlanEvidence
          (Option.some (TokenPlan.exact (.symbol .underscore)
            underscore.span))
        (PhysicalTokens tokens origin finish) := by
        simpa only [MatchedTerminal.physicalTokenPlan_symbol] using
          terminalEvidence
      have enclosed := coreEvidence.enclose
        (by
          intro plan success
          simp only [Option.some.injEq] at success
          subst plan
          exact TokenPlan.WellAnchored.exact _ _)
        witness.consumed
      simpa [ruleTokenPlan?, patternTokenPlan?, sourceLoc,
        RuleReduction.marker, RuleReduction.terminalLoc] using enclosed
  | patternLiteral origin finish literal witness =>
      change TokenPlanEvidence
        (patternTokenPlan? (sourceLoc witness (.literal literal)))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have literalEvidence := TokenPlanEvidence.rule
        sourceRuleTokenPlanLayout .literal literal selected
      have coreEvidence : TokenPlanEvidence
          (Option.some (literalTokenPlan literal))
          (PhysicalTokens tokens origin finish) := by
        simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?] using literalEvidence
      have enclosed := coreEvidence.enclose
        (by
          intro plan success
          simp only [Option.some.injEq] at success
          subst plan
          exact literalTokenPlan_wellAnchored literal)
        witness.consumed
      simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?, patternTokenPlan?,
        sourceLoc] using enclosed
  | patternDotConstructorWithoutArguments origin finish dot name spelling
      parsed projects witness =>
      change TokenPlanEvidence
        (patternTokenPlan? (sourceLoc witness
          (.dotConstructor
            (RuleReduction.terminalLoc dot ())
            (RuleReduction.terminalLoc name parsed)
            none)))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_optional_none,
        EbnfValues.tokenPlan?_nil,
        MatchedTerminal.physicalTokenPlan_symbol] at sequenceEvidence
      rw [identifierPhysicalTokenPlan_eq_identifierPlan
        name spelling parsed projects] at sequenceEvidence
      have coreEvidence : TokenPlanEvidence
          (Option.some (TokenPlan.concat [
            .exact (.symbol .dot) dot.span,
            identifierPlan (RuleReduction.terminalLoc name parsed)]))
          (PhysicalTokens tokens origin finish) := by
        simpa [TokenPlan.concat, TokenPlan.append, TokenPlan.empty] using
          sequenceEvidence
      have enclosed := coreEvidence.enclose
        (by
          intro plan success
          simp only [Option.some.injEq] at success
          subst plan
          apply TokenPlan.WellAnchored.concat
          intro component member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact TokenPlan.WellAnchored.exact _ _
          · exact identifierPlan_wellAnchored _)
        witness.consumed
      simpa [patternTokenPlan?, sourceLoc, RuleReduction.terminalLoc,
        TokenPlan.concat, TokenPlan.append] using enclosed
  | patternDotConstructorWithArguments origin finish dot name spelling
      parsed projects openParen arguments closeParen witness =>
      change TokenPlanEvidence
        (patternTokenPlan? (sourceLoc witness
          (.dotConstructor
            (RuleReduction.terminalLoc dot ())
            (RuleReduction.terminalLoc name parsed)
            (some arguments))))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_optional_some,
        EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_nil,
        MatchedTerminal.physicalTokenPlan_symbol] at sequenceEvidence
      rw [nonemptyPatternRuleValues_tokenPlan? arguments] at sequenceEvidence
      rw [identifierPhysicalTokenPlan_eq_identifierPlan
        name spelling parsed projects] at sequenceEvidence
      cases argumentPlansEq : nonemptyPatternTokenPlans? arguments with
      | none =>
          rcases sequenceEvidence with ⟨plan, success, relation⟩
          simp [argumentPlansEq] at success
      | some argumentPlans =>
          have exactEvidence : TokenPlanEvidence
              (Option.some (TokenPlan.concat [
                .exact (.symbol .dot) dot.span,
                identifierPlan (RuleReduction.terminalLoc name parsed),
                .exact (.symbol .leftParen) openParen.span,
                .commaSeparated argumentPlans,
                .exact (.symbol .rightParen) closeParen.span]))
              (PhysicalTokens tokens origin finish) := by
            simpa [sourceRuleTokenPlanLayout, argumentPlansEq,
              TokenPlan.concat, TokenPlan.append, TokenPlan.empty] using
              sequenceEvidence
          rcases exactEvidence with ⟨plan, success, relation⟩
          simp only [Option.some.injEq] at success
          subst plan
          have coreEvidence : TokenPlanEvidence
              (Option.some (TokenPlan.concat [
                .exact (.symbol .dot) dot.span,
                identifierPlan (RuleReduction.terminalLoc name parsed),
                .parens (.commaSeparated argumentPlans)]))
              (PhysicalTokens tokens origin finish) := by
            apply TokenPlanEvidence.some
            simpa [TokenPlan.parens, TokenPlan.concat, TokenPlan.append]
              using relation.exactHeadAndTwoExactToPlain
          have enclosed := coreEvidence.enclose
            (by
              intro plan success
              simp only [Option.some.injEq] at success
              subst plan
              apply TokenPlan.WellAnchored.concat
              intro component member
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl | rfl
              · exact TokenPlan.WellAnchored.exact _ _
              · exact identifierPlan_wellAnchored _
              · exact TokenPlan.WellAnchored.parens _)
            witness.consumed
          simpa [patternTokenPlan?, sourceLoc, RuleReduction.terminalLoc,
            argumentPlansEq, TokenPlan.parens, TokenPlan.concat,
            TokenPlan.append] using enclosed
  | patternNamedWithoutArguments origin finish name witness =>
      change TokenPlanEvidence
        (patternTokenPlan? (sourceLoc witness (.named name none)))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValue.tokenPlan?_optional_none,
        EbnfValues.tokenPlan?_nil] at sequenceEvidence
      have nameEvidence : TokenPlanEvidence
          (Option.some (qualifiedNamePlan name))
          (PhysicalTokens tokens origin finish) := by
        simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?] using
          sequenceEvidence
      have enclosed := nameEvidence.enclose
        (by
          intro plan success
          simp only [Option.some.injEq] at success
          subst plan
          exact qualifiedNamePlan_wellAnchored name)
        witness.consumed
      simpa [ruleTokenPlan?, patternTokenPlan?, sourceLoc] using enclosed
  | patternNamedWithArguments origin finish name openParen arguments
      closeParen witness =>
      change TokenPlanEvidence
        (patternTokenPlan? (sourceLoc witness
          (.named name (some arguments))))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValue.tokenPlan?_optional_some,
        EbnfValue.tokenPlan?_sequence,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValues.tokenPlan?_nil,
        MatchedTerminal.physicalTokenPlan_symbol] at sequenceEvidence
      rw [nonemptyPatternRuleValues_tokenPlan? arguments] at sequenceEvidence
      cases argumentPlansEq : nonemptyPatternTokenPlans? arguments with
      | none =>
          rcases sequenceEvidence with ⟨plan, success, relation⟩
          simp [sourceRuleTokenPlanLayout, ruleTokenPlan?,
            argumentPlansEq] at success
      | some argumentPlans =>
          have exactEvidence : TokenPlanEvidence
              (Option.some (TokenPlan.concat [
                qualifiedNamePlan name,
                .exact (.symbol .leftParen) openParen.span,
                .commaSeparated argumentPlans,
                .exact (.symbol .rightParen) closeParen.span]))
              (PhysicalTokens tokens origin finish) := by
            simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?,
              argumentPlansEq, TokenPlan.concat, TokenPlan.append,
              TokenPlan.empty] using sequenceEvidence
          rcases exactEvidence with ⟨plan, success, relation⟩
          simp only [Option.some.injEq] at success
          subst plan
          have coreEvidence : TokenPlanEvidence
              (Option.some ((qualifiedNamePlan name).append
                (.parens (.commaSeparated argumentPlans))))
              (PhysicalTokens tokens origin finish) := by
            apply TokenPlanEvidence.some
            simpa [TokenPlan.parens, TokenPlan.concat, TokenPlan.append]
              using relation.beforeAndTwoExactToPlain
          have enclosed := coreEvidence.enclose
            (by
              intro plan success
              simp only [Option.some.injEq] at success
              subst plan
              exact TokenPlan.WellAnchored.append
                (qualifiedNamePlan_wellAnchored name)
                (TokenPlan.WellAnchored.parens _))
            witness.consumed
          simpa [patternTokenPlan?, sourceLoc, argumentPlansEq]
            using enclosed
  | patternComptime origin finish comptime expression witness =>
      change TokenPlanEvidence
        (patternTokenPlan? (sourceLoc witness
          (.comptime
            (RuleReduction.marker comptime
              (.comptimeModifier comptime))
            expression)))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValues.tokenPlan?_nil,
        MatchedTerminal.physicalTokenPlan_contextualKeyword] at sequenceEvidence
      cases expressionEq : expressionTokenPlan? expression with
      | none =>
          have annotationEq :
              expressionTokenPlanAt? .annotation expression = none := by
            simpa [expressionTokenPlan?] using expressionEq
          rcases sequenceEvidence with ⟨plan, success, relation⟩
          simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?] at success
          simp [expressionEq] at success
      | some expressionPlan =>
          have annotationEq :
              expressionTokenPlanAt? .annotation expression =
                some expressionPlan := by
            simpa [expressionTokenPlan?] using expressionEq
          have coreEvidence : TokenPlanEvidence
              (Option.some ((TokenPlan.exact
                (.identifier ContextualKeyword.comptimeKw.spelling)
                comptime.span).append expressionPlan))
              (PhysicalTokens tokens origin finish) := by
            simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?, expressionEq]
              using sequenceEvidence
          have enclosed := coreEvidence.enclose
            (by
              intro plan success
              simp only [Option.some.injEq] at success
              subst plan
              exact TokenPlan.WellAnchored.append
                (TokenPlan.WellAnchored.exact _ _)
                (expressionTokenPlan?_wellAnchored
                  expression expressionPlan expressionEq))
            witness.consumed
          simpa [ruleTokenPlan?, patternTokenPlan?, sourceLoc,
            RuleReduction.marker, RuleReduction.terminalLoc,
            annotationEq] using enclosed
  | patternEmptyTuple origin finish openParen closeParen witness =>
      change TokenPlanEvidence
        (patternTokenPlan? (sourceLoc witness (.tuple [])))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValues.tokenPlan?_nil,
        MatchedTerminal.physicalTokenPlan_symbol] at sequenceEvidence
      have exactEvidence : TokenPlanEvidence
          (Option.some (TokenPlan.concat [
            .exact (.symbol .leftParen) openParen.span,
            .empty,
            .exact (.symbol .rightParen) closeParen.span]))
          (PhysicalTokens tokens origin finish) := by
        simpa [TokenPlan.concat, TokenPlan.append, TokenPlan.empty] using
          sequenceEvidence
      rcases exactEvidence with ⟨plan, success, relation⟩
      simp only [Option.some.injEq] at success
      subst plan
      have coreEvidence := TokenPlanEvidence.some relation.twoExactToPlain
      have enclosed := coreEvidence.enclose
        (by
          intro plan success
          simp only [Option.some.injEq] at success
          subst plan
          apply TokenPlan.WellAnchored.concat
          intro component member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact TokenPlan.WellAnchored.plain _
          · exact TokenPlan.WellAnchored.empty
          · exact TokenPlan.WellAnchored.plain _)
        witness.consumed
      simpa [patternTokenPlan?, sourceLoc, TokenPlan.parens] using enclosed
  | patternGroup origin finish openParen inner closeParen witness =>
      change TokenPlanEvidence
        (patternTokenPlan? (sourceLoc witness (.group inner)))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValues.tokenPlan?_nil,
        MatchedTerminal.physicalTokenPlan_symbol] at sequenceEvidence
      cases innerEq : patternTokenPlan? inner with
      | none =>
          rcases sequenceEvidence with ⟨plan, success, relation⟩
          simp [sourceRuleTokenPlanLayout, ruleTokenPlan?, innerEq]
            at success
      | some innerPlan =>
          have innerAnchored :=
            patternTokenPlan?_wellAnchored inner innerPlan innerEq
          have exactEvidence : TokenPlanEvidence
              (Option.some (TokenPlan.concat [
                .exact (.symbol .leftParen) openParen.span,
                innerPlan,
                .exact (.symbol .rightParen) closeParen.span]))
              (PhysicalTokens tokens origin finish) := by
            simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?, innerEq,
              TokenPlan.concat, TokenPlan.append, TokenPlan.empty] using
              sequenceEvidence
          rcases exactEvidence with ⟨plan, success, relation⟩
          simp only [Option.some.injEq] at success
          subst plan
          have coreEvidence := TokenPlanEvidence.some
            relation.twoExactToPlain
          have enclosed := coreEvidence.enclose
            (by
              intro plan success
              simp only [Option.some.injEq] at success
              subst plan
              apply TokenPlan.WellAnchored.concat
              intro component member
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl | rfl
              · exact TokenPlan.WellAnchored.plain _
              · exact innerAnchored
              · exact TokenPlan.WellAnchored.plain _)
            witness.consumed
          simpa [patternTokenPlan?, sourceLoc, innerEq,
            TokenPlan.parens] using enclosed
  | patternTuple origin finish openParen first comma second rest closeParen
      witness =>
      change TokenPlanEvidence
        (patternTokenPlan? (sourceLoc witness
          (.tuple (first :: second :: rest.map Prod.snd))))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValues.tokenPlan?_nil,
        MatchedTerminal.physicalTokenPlan_symbol] at sequenceEvidence
      rcases sequenceEvidence.splitAppend with
        ⟨openActual, tail₁, rootActualEq, openRaw, tailEvidence₁⟩
      rcases tailEvidence₁.splitAppend with
        ⟨firstActual, tail₂, tailActualEq₁, firstRaw, tailEvidence₂⟩
      rcases tailEvidence₂.splitAppend with
        ⟨commaActual, tail₃, tailActualEq₂, commaRaw, tailEvidence₃⟩
      rcases tailEvidence₃.splitAppend with
        ⟨secondActual, tail₄, tailActualEq₃, secondRaw, tailEvidence₄⟩
      rcases tailEvidence₄.splitAppend with
        ⟨restActual, tail₅, tailActualEq₄, restRaw, tailEvidence₅⟩
      rcases tailEvidence₅.splitAppend with
        ⟨closeActual, emptyActual, tailActualEq₅,
          closeRaw, emptyEvidence⟩
      have openExact : TokenPlanEvidence
          (Option.some (TokenPlan.exact (.symbol .leftParen)
            openParen.span)) openActual := by
        simpa only [MatchedTerminal.physicalTokenPlan_symbol] using openRaw
      have commaExact : TokenPlanEvidence
          (Option.some (TokenPlan.exact (.symbol .comma) comma.span))
          commaActual := by
        simpa only [MatchedTerminal.physicalTokenPlan_symbol] using commaRaw
      have closeExact : TokenPlanEvidence
          (Option.some (TokenPlan.exact (.symbol .rightParen)
            closeParen.span)) closeActual := by
        simpa only [MatchedTerminal.physicalTokenPlan_symbol] using closeRaw
      have firstEvidence : TokenPlanEvidence
          (patternTokenPlan? first) firstActual := by
        simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?] using firstRaw
      have secondEvidence : TokenPlanEvidence
          (patternTokenPlan? second) secondActual := by
        simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?] using secondRaw
      have restEvidence : TokenPlanEvidence
          ((EbnfValue.star patternTupleRestExpr
            (rest.map patternTupleRestValue)).tokenPlan?
              sourceRuleTokenPlanLayout) restActual := by
        exact restRaw
      have restPlainEvidence :=
        patternTupleRestEvidence_toPlain rest restEvidence
      have openPlain := openExact.exactToPlain
      have commaPlain := commaExact.exactToPlain
      have closePlain := closeExact.exactToPlain
      have combined := openPlain.append <|
        firstEvidence.append <|
        commaPlain.append <|
        secondEvidence.append <|
        restPlainEvidence.append <|
        closePlain.append emptyEvidence
      have actualEq :
          PhysicalTokens tokens origin finish =
            openActual ++ (firstActual ++ (commaActual ++
              (secondActual ++ (restActual ++
                (closeActual ++ emptyActual))))) := by
        rw [rootActualEq, tailActualEq₁, tailActualEq₂,
          tailActualEq₃, tailActualEq₄, tailActualEq₅]
      have onActual := combined.actual_eq actualEq.symm
      rcases firstEvidence with ⟨firstPlan, firstEq, firstRelation⟩
      rcases secondEvidence with
        ⟨secondPlan, secondEq, secondRelation⟩
      have enclosed := onActual.enclose
        (by
          intro plan success
          cases restPlainEq : patternTupleRestPlainPlan? rest with
          | none => simp [restPlainEq] at success
          | some restPlain =>
              simp [restPlainEq, firstEq, secondEq] at success
              subst plan
              simpa [TokenPlan.concat, TokenPlan.append,
                TokenPlan.empty] using
                TokenPlan.WellAnchored.concatPlainBookended
                  (.symbol .leftParen) (.symbol .rightParen)
                  [firstPlan, .plain (.symbol .comma),
                    secondPlan, restPlain])
        witness.consumed
      apply enclosed.candidate_eq
      rw [patternTupleRestPlainPlan_eq]
      cases restPlansEq : (rest.map Prod.snd).mapM
          patternTokenPlan? <;>
        simp [patternTokenPlan?, sourceLoc,
          patternPlans_eq_directMapM, firstEq, secondEq,
          restPlansEq, TokenPlan.parens,
          TokenPlan.commaSeparated, TokenPlan.concat,
          TokenPlan.append, TokenPlan.empty]

private theorem expressionPlans_eq_mapM (values : List Expression) :
    expressionTokenPlans? values =
      values.mapM (ruleTokenPlan? .expression) := by
  change expressionTokenPlans? values = values.mapM expressionTokenPlan?
  induction values with
  | nil => simp [expressionTokenPlans?]
  | cons head tail induction =>
      simp [expressionTokenPlans?, expressionTokenPlan?, induction]

private theorem expressionPlans_eq_directMapM
    (values : List Expression) :
    expressionTokenPlans? values =
      values.mapM expressionTokenPlan? := by
  induction values with
  | nil => simp [expressionTokenPlans?]
  | cons head tail induction =>
      simp [expressionTokenPlans?, expressionTokenPlan?, induction]

private theorem expressionRuleValues_mapM_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (values : List Expression) :
    (values.map (EbnfValue.ruleAtom
      (file := file) (tokens := tokens) .expression)).mapM
        (fun value => value.tokenPlan? sourceRuleTokenPlanLayout) =
      values.mapM (ruleTokenPlan? .expression) := by
  rw [List.mapM_map]
  simp [Function.comp_def, sourceRuleTokenPlanLayout]

private theorem expressionRuleValues_list0_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (values : List Expression) :
    (EbnfValue.list0 (.atom (.nonterminal .expression))
      (values.map (EbnfValue.ruleAtom
        (file := file) (tokens := tokens) .expression))).tokenPlan?
        sourceRuleTokenPlanLayout =
      (expressionTokenPlans? values).map
        TokenPlan.commaSeparated := by
  rw [EbnfValue.tokenPlan?_list0,
    expressionRuleValues_mapM_tokenPlan?, expressionPlans_eq_mapM]
  symm
  exact optionMap_eq_bindPure TokenPlan.commaSeparated _

private def expressionTupleRestPlainPlan?
    {file : WorkspaceFile} {tokens : List Token} :
    List (MatchedTerminal file tokens (.symbol .comma) × Expression) →
      Option TokenPlan
  | [] => some .empty
  | entry :: rest => do
      let expressionPlan ← expressionTokenPlan? entry.2
      let restPlan ← expressionTupleRestPlainPlan? rest
      pure (((TokenPlan.plain (.symbol .comma)).append
        expressionPlan).append restPlan)

private theorem expressionTupleRestPlainPlan_eq
    {file : WorkspaceFile} {tokens : List Token}
    (rest : List
      (MatchedTerminal file tokens (.symbol .comma) × Expression)) :
    expressionTupleRestPlainPlan? rest = (do
      let plans ← (rest.map Prod.snd).mapM expressionTokenPlan?
      pure (.concat (plans.map fun plan =>
        (TokenPlan.plain (.symbol .comma)).append plan))) := by
  induction rest with
  | nil => simp [expressionTupleRestPlainPlan?, TokenPlan.concat,
      TokenPlan.empty]
  | cons entry rest induction =>
      rw [expressionTupleRestPlainPlan?, List.map_cons,
        List.mapM_cons, induction]
      cases expressionEq : expressionTokenPlan? entry.2 <;>
        cases tailPlansEq : (rest.map Prod.snd).mapM
          expressionTokenPlan? <;>
          simp [TokenPlan.concat, TokenPlan.append]

private abbrev expressionTupleRestExpr : EbnfExpr :=
  .group (.sequence [
    .atom (.terminal (.symbol .comma)),
    .atom (.nonterminal .expression)])

private def expressionTupleRestValue
    {file : WorkspaceFile} {tokens : List Token}
    (entry : MatchedTerminal file tokens (.symbol .comma) × Expression) :
    EbnfValue file tokens expressionTupleRestExpr :=
  EbnfValue.group _ <| EbnfValue.sequence _ <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .comma) entry.1) <|
    EbnfValues.cons _ _
      (EbnfValue.ruleAtom .expression entry.2) EbnfValues.nil

private theorem expressionTupleRestValue_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (entry : MatchedTerminal file tokens (.symbol .comma) × Expression) :
    (expressionTupleRestValue entry).tokenPlan?
        sourceRuleTokenPlanLayout = (do
      let expressionPlan ← expressionTokenPlan? entry.2
      pure ((TokenPlan.exact (.symbol .comma) entry.1.span).append
        expressionPlan)) := by
  cases expressionEq : expressionTokenPlan? entry.2 <;>
    simp [expressionTupleRestValue, expressionTupleRestExpr,
      sourceRuleTokenPlanLayout, ruleTokenPlan?, expressionEq,
      MatchedTerminal.physicalTokenPlan_symbol,
      TokenPlan.append, TokenPlan.empty]

private theorem expressionTupleRestEvidence_toPlain
    {file : WorkspaceFile} {tokens : List Token}
    (rest : List
      (MatchedTerminal file tokens (.symbol .comma) × Expression))
    {actual : List Token}
    (evidence : TokenPlanEvidence
      ((EbnfValue.star expressionTupleRestExpr
        (rest.map expressionTupleRestValue)).tokenPlan?
          sourceRuleTokenPlanLayout) actual) :
    TokenPlanEvidence (expressionTupleRestPlainPlan? rest) actual := by
  induction rest generalizing actual with
  | nil =>
      have flattened := evidence.candidate_eq
        (EbnfValue.tokenPlan?_star sourceRuleTokenPlanLayout
          expressionTupleRestExpr [])
      simpa [expressionTupleRestPlainPlan?, TokenPlan.concat,
        TokenPlan.empty] using flattened
  | cons entry rest induction =>
      have flattened := evidence.candidate_eq
        (EbnfValue.tokenPlan?_star sourceRuleTokenPlanLayout
          expressionTupleRestExpr
          ((entry :: rest).map expressionTupleRestValue))
      rw [List.map_cons, List.mapM_cons,
        expressionTupleRestValue_tokenPlan?] at flattened
      cases expressionEq : expressionTokenPlan? entry.2 with
      | none =>
          rcases flattened with ⟨plan, success, relation⟩
          simp [expressionEq] at success
      | some expressionPlan =>
          cases tailPlansEq :
              (rest.map expressionTupleRestValue).mapM
                (fun value => value.tokenPlan?
                  sourceRuleTokenPlanLayout) with
          | none =>
              rcases flattened with ⟨plan, success, relation⟩
              simp [expressionEq, tailPlansEq] at success
          | some tailPlans =>
              have exactEvidence : TokenPlanEvidence
                  (Option.some ((TokenPlan.exact (.symbol .comma)
                    entry.1.span).append expressionPlan |>.append
                      (TokenPlan.concat tailPlans)))
                  actual := by
                simpa [expressionEq, tailPlansEq, TokenPlan.concat,
                  TokenPlan.append, TokenPlan.empty] using flattened
              rcases exactEvidence with ⟨plan, success, relation⟩
              simp only [Option.some.injEq] at success
              subst plan
              rcases relation.split_append with
                ⟨headActual, tailActual, actualEq,
                  headRelation, tailRelation⟩
              have headPlainRelation : TokenSlot.ListMatches
                  ((TokenPlan.plain (.symbol .comma)).append
                    expressionPlan).slots headActual := by
                simpa [TokenPlan.append, TokenPlan.empty] using
                  (TokenSlot.ListMatches.exactBetweenToPlain
                    (left := TokenPlan.empty)
                    (right := expressionPlan) headRelation)
              have headEvidence := TokenPlanEvidence.some headPlainRelation
              have tailEvidence : TokenPlanEvidence
                  ((EbnfValue.star expressionTupleRestExpr
                    (rest.map expressionTupleRestValue)).tokenPlan?
                      sourceRuleTokenPlanLayout) tailActual := by
                refine ⟨TokenPlan.concat tailPlans, ?_, tailRelation⟩
                rw [EbnfValue.tokenPlan?_star, tailPlansEq]
                rfl
              have tailPlainEvidence := induction tailEvidence
              have combined := headEvidence.append tailPlainEvidence
              have onActual := combined.actual_eq actualEq.symm
              apply onActual.candidate_eq
              simp [expressionTupleRestPlainPlan?, expressionEq,
                TokenPlan.append_assoc]

/-- Atomic-expression reductions preserve complete source-token evidence. -/
theorem atom_tokenPlanSound :
    GrammarRuleTokenPlanSound .atom := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  cases reduces with
  | atomLiteral origin finish literal witness =>
      change TokenPlanEvidence
        (atomExpressionTokenPlan?
          (sourceLoc witness (.literal literal)))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have literalEvidence := TokenPlanEvidence.rule
        sourceRuleTokenPlanLayout .literal literal selected
      have coreEvidence : TokenPlanEvidence
          (Option.some (literalTokenPlan literal))
          (PhysicalTokens tokens origin finish) := by
        simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?] using
          literalEvidence
      have enclosed := coreEvidence.enclose
        (by
          intro plan success
          simp only [Option.some.injEq] at success
          subst plan
          exact literalTokenPlan_wellAnchored literal)
        witness.consumed
      simpa [atomExpressionTokenPlan?, expressionTokenPlanAt?, sourceLoc]
        using enclosed
  | atomName origin finish name spelling parsed projects witness =>
      change TokenPlanEvidence
        (atomExpressionTokenPlan? (sourceLoc witness
          (.name (RuleReduction.terminalLoc name parsed))))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have terminalEvidence := selected.candidate_eq
        (EbnfValue.tokenPlan?_terminalAtom
          sourceRuleTokenPlanLayout _ name)
      rw [identifierPhysicalTokenPlan_eq_identifierPlan
        name spelling parsed projects] at terminalEvidence
      have enclosed := terminalEvidence.enclose
        (by
          intro plan success
          simp only [Option.some.injEq] at success
          subst plan
          exact identifierPlan_wellAnchored _)
        witness.consumed
      simpa [atomExpressionTokenPlan?, expressionTokenPlanAt?, sourceLoc]
        using enclosed
  | atomDotConstructorWithoutArguments origin finish dot name spelling
      parsed projects witness =>
      change TokenPlanEvidence
        (atomExpressionTokenPlan? (sourceLoc witness
          (.dotConstructor
            (RuleReduction.terminalLoc dot ())
            (RuleReduction.terminalLoc name parsed)
            none)))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_optional_none,
        EbnfValues.tokenPlan?_nil,
        MatchedTerminal.physicalTokenPlan_symbol] at sequenceEvidence
      rw [identifierPhysicalTokenPlan_eq_identifierPlan
        name spelling parsed projects] at sequenceEvidence
      have coreEvidence : TokenPlanEvidence
          (Option.some (TokenPlan.concat [
            .exact (.symbol .dot) dot.span,
            identifierPlan (RuleReduction.terminalLoc name parsed)]))
          (PhysicalTokens tokens origin finish) := by
        simpa [TokenPlan.concat, TokenPlan.append, TokenPlan.empty] using
          sequenceEvidence
      have enclosed := coreEvidence.enclose
        (by
          intro plan success
          simp only [Option.some.injEq] at success
          subst plan
          apply TokenPlan.WellAnchored.concat
          intro component member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact TokenPlan.WellAnchored.exact _ _
          · exact identifierPlan_wellAnchored _)
        witness.consumed
      simpa [atomExpressionTokenPlan?, expressionTokenPlanAt?, sourceLoc,
        RuleReduction.terminalLoc, TokenPlan.concat, TokenPlan.append]
        using enclosed
  | atomDotConstructorWithArguments origin finish dot name spelling
      parsed projects openParen arguments closeParen witness =>
      change TokenPlanEvidence
        (atomExpressionTokenPlan? (sourceLoc witness
          (.dotConstructor
            (RuleReduction.terminalLoc dot ())
            (RuleReduction.terminalLoc name parsed)
            (some arguments))))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_optional_some,
        EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_nil,
        MatchedTerminal.physicalTokenPlan_symbol] at sequenceEvidence
      rw [expressionRuleValues_list0_tokenPlan? arguments]
        at sequenceEvidence
      rw [identifierPhysicalTokenPlan_eq_identifierPlan
        name spelling parsed projects] at sequenceEvidence
      cases argumentPlansEq : expressionTokenPlans? arguments with
      | none =>
          rcases sequenceEvidence with ⟨plan, success, relation⟩
          simp [argumentPlansEq] at success
      | some argumentPlans =>
          have exactEvidence : TokenPlanEvidence
              (Option.some (TokenPlan.concat [
                .exact (.symbol .dot) dot.span,
                identifierPlan (RuleReduction.terminalLoc name parsed),
                .exact (.symbol .leftParen) openParen.span,
                .commaSeparated argumentPlans,
                .exact (.symbol .rightParen) closeParen.span]))
              (PhysicalTokens tokens origin finish) := by
            simpa [sourceRuleTokenPlanLayout, argumentPlansEq,
              TokenPlan.concat, TokenPlan.append, TokenPlan.empty] using
              sequenceEvidence
          rcases exactEvidence with ⟨plan, success, relation⟩
          simp only [Option.some.injEq] at success
          subst plan
          have coreEvidence : TokenPlanEvidence
              (Option.some (TokenPlan.concat [
                .exact (.symbol .dot) dot.span,
                identifierPlan (RuleReduction.terminalLoc name parsed),
                .parens (.commaSeparated argumentPlans)]))
              (PhysicalTokens tokens origin finish) := by
            apply TokenPlanEvidence.some
            simpa [TokenPlan.parens, TokenPlan.concat, TokenPlan.append]
              using relation.exactHeadAndTwoExactToPlain
          have enclosed := coreEvidence.enclose
            (by
              intro plan success
              simp only [Option.some.injEq] at success
              subst plan
              apply TokenPlan.WellAnchored.concat
              intro component member
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl | rfl
              · exact TokenPlan.WellAnchored.exact _ _
              · exact identifierPlan_wellAnchored _
              · exact TokenPlan.WellAnchored.parens _)
            witness.consumed
          simpa [atomExpressionTokenPlan?, expressionTokenPlanAt?, sourceLoc,
            RuleReduction.terminalLoc, argumentPlansEq, TokenPlan.parens,
            TokenPlan.concat, TokenPlan.append] using enclosed
  | atomProxy origin finish atTerminal typeValue witness =>
      change TokenPlanEvidence
        (atomExpressionTokenPlan? (sourceLoc witness
          (.proxy (RuleReduction.terminalLoc atTerminal ()) typeValue)))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValues.tokenPlan?_nil,
        MatchedTerminal.physicalTokenPlan_symbol] at sequenceEvidence
      cases typeEq : typeAtomPlan? typeValue with
      | none =>
          rcases sequenceEvidence with ⟨plan, success, relation⟩
          simp [sourceRuleTokenPlanLayout, ruleTokenPlan?, typeEq]
            at success
      | some typePlan =>
          have coreEvidence : TokenPlanEvidence
              (Option.some ((TokenPlan.exact (.symbol .at)
                atTerminal.span).append typePlan))
              (PhysicalTokens tokens origin finish) := by
            simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?, typeEq]
              using sequenceEvidence
          have enclosed := coreEvidence.enclose
            (by
              intro plan success
              simp only [Option.some.injEq] at success
              subst plan
              exact TokenPlan.WellAnchored.append
                (TokenPlan.WellAnchored.exact _ _)
                (typeAtomPlan?_wellAnchored typeValue typePlan typeEq))
            witness.consumed
          simpa [atomExpressionTokenPlan?, expressionTokenPlanAt?, sourceLoc,
            RuleReduction.terminalLoc, typeEq] using enclosed
  | atomLambda origin finish value =>
      exact RuleReduction.SemanticPassThrough.tokenPlanEvidence
        (by apply RuleReduction.SemanticPassThrough.atomLambda)
        inputEvidence
  | atomEmptyTuple origin finish openParen closeParen witness =>
      change TokenPlanEvidence
        (atomExpressionTokenPlan? (sourceLoc witness (.tuple [])))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValues.tokenPlan?_nil,
        MatchedTerminal.physicalTokenPlan_symbol] at sequenceEvidence
      have exactEvidence : TokenPlanEvidence
          (Option.some (TokenPlan.concat [
            .exact (.symbol .leftParen) openParen.span,
            .empty,
            .exact (.symbol .rightParen) closeParen.span]))
          (PhysicalTokens tokens origin finish) := by
        simpa [TokenPlan.concat, TokenPlan.append, TokenPlan.empty] using
          sequenceEvidence
      rcases exactEvidence with ⟨plan, success, relation⟩
      simp only [Option.some.injEq] at success
      subst plan
      have coreEvidence := TokenPlanEvidence.some relation.twoExactToPlain
      have enclosed := coreEvidence.enclose
        (by
          intro plan success
          simp only [Option.some.injEq] at success
          subst plan
          apply TokenPlan.WellAnchored.concat
          intro component member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact TokenPlan.WellAnchored.plain _
          · exact TokenPlan.WellAnchored.empty
          · exact TokenPlan.WellAnchored.plain _)
        witness.consumed
      simpa [atomExpressionTokenPlan?, expressionTokenPlanAt?, sourceLoc,
        TokenPlan.parens] using enclosed
  | atomGroup origin finish openParen inner closeParen witness =>
      change TokenPlanEvidence
        (atomExpressionTokenPlan? (sourceLoc witness (.group inner)))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValues.tokenPlan?_nil,
        MatchedTerminal.physicalTokenPlan_symbol] at sequenceEvidence
      cases innerEq : expressionTokenPlan? inner with
      | none =>
          rcases sequenceEvidence with ⟨plan, success, relation⟩
          simp [sourceRuleTokenPlanLayout, ruleTokenPlan?, innerEq]
            at success
      | some innerPlan =>
          have innerAnchored :=
            expressionTokenPlan?_wellAnchored inner innerPlan innerEq
          have annotationEq :
              expressionTokenPlanAt? .annotation inner =
                some innerPlan := by
            simpa [expressionTokenPlan?] using innerEq
          have exactEvidence : TokenPlanEvidence
              (Option.some (TokenPlan.concat [
                .exact (.symbol .leftParen) openParen.span,
                innerPlan,
                .exact (.symbol .rightParen) closeParen.span]))
              (PhysicalTokens tokens origin finish) := by
            simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?, innerEq,
              TokenPlan.concat, TokenPlan.append, TokenPlan.empty] using
              sequenceEvidence
          rcases exactEvidence with ⟨plan, success, relation⟩
          simp only [Option.some.injEq] at success
          subst plan
          have coreEvidence := TokenPlanEvidence.some
            relation.twoExactToPlain
          have enclosed := coreEvidence.enclose
            (by
              intro plan success
              simp only [Option.some.injEq] at success
              subst plan
              apply TokenPlan.WellAnchored.concat
              intro component member
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl | rfl
              · exact TokenPlan.WellAnchored.plain _
              · exact innerAnchored
              · exact TokenPlan.WellAnchored.plain _)
            witness.consumed
          simpa [atomExpressionTokenPlan?, expressionTokenPlanAt?, sourceLoc,
            annotationEq, TokenPlan.parens] using enclosed
  | atomTuple origin finish openParen first comma second rest closeParen
      witness =>
      change TokenPlanEvidence
        (atomExpressionTokenPlan? (sourceLoc witness
          (.tuple (first :: second :: rest.map Prod.snd))))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValues.tokenPlan?_nil,
        MatchedTerminal.physicalTokenPlan_symbol] at sequenceEvidence
      rcases sequenceEvidence.splitAppend with
        ⟨openActual, tail₁, rootActualEq, openRaw, tailEvidence₁⟩
      rcases tailEvidence₁.splitAppend with
        ⟨firstActual, tail₂, tailActualEq₁, firstRaw, tailEvidence₂⟩
      rcases tailEvidence₂.splitAppend with
        ⟨commaActual, tail₃, tailActualEq₂, commaRaw, tailEvidence₃⟩
      rcases tailEvidence₃.splitAppend with
        ⟨secondActual, tail₄, tailActualEq₃, secondRaw, tailEvidence₄⟩
      rcases tailEvidence₄.splitAppend with
        ⟨restActual, tail₅, tailActualEq₄, restRaw, tailEvidence₅⟩
      rcases tailEvidence₅.splitAppend with
        ⟨closeActual, emptyActual, tailActualEq₅,
          closeRaw, emptyEvidence⟩
      have openExact : TokenPlanEvidence
          (Option.some (TokenPlan.exact (.symbol .leftParen)
            openParen.span)) openActual := by
        simpa only [MatchedTerminal.physicalTokenPlan_symbol] using openRaw
      have commaExact : TokenPlanEvidence
          (Option.some (TokenPlan.exact (.symbol .comma) comma.span))
          commaActual := by
        simpa only [MatchedTerminal.physicalTokenPlan_symbol] using commaRaw
      have closeExact : TokenPlanEvidence
          (Option.some (TokenPlan.exact (.symbol .rightParen)
            closeParen.span)) closeActual := by
        simpa only [MatchedTerminal.physicalTokenPlan_symbol] using closeRaw
      have firstEvidence : TokenPlanEvidence
          (expressionTokenPlan? first) firstActual := by
        simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?] using firstRaw
      have secondEvidence : TokenPlanEvidence
          (expressionTokenPlan? second) secondActual := by
        simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?] using secondRaw
      have restEvidence : TokenPlanEvidence
          ((EbnfValue.star expressionTupleRestExpr
            (rest.map expressionTupleRestValue)).tokenPlan?
              sourceRuleTokenPlanLayout) restActual := by
        exact restRaw
      have restPlainEvidence :=
        expressionTupleRestEvidence_toPlain rest restEvidence
      have openPlain := openExact.exactToPlain
      have commaPlain := commaExact.exactToPlain
      have closePlain := closeExact.exactToPlain
      have combined := openPlain.append <|
        firstEvidence.append <|
        commaPlain.append <|
        secondEvidence.append <|
        restPlainEvidence.append <|
        closePlain.append emptyEvidence
      have actualEq :
          PhysicalTokens tokens origin finish =
            openActual ++ (firstActual ++ (commaActual ++
              (secondActual ++ (restActual ++
                (closeActual ++ emptyActual))))) := by
        rw [rootActualEq, tailActualEq₁, tailActualEq₂,
          tailActualEq₃, tailActualEq₄, tailActualEq₅]
      have onActual := combined.actual_eq actualEq.symm
      rcases firstEvidence with ⟨firstPlan, firstEq, firstRelation⟩
      rcases secondEvidence with
        ⟨secondPlan, secondEq, secondRelation⟩
      have enclosed := onActual.enclose
        (by
          intro plan success
          cases restPlainEq : expressionTupleRestPlainPlan? rest with
          | none => simp [restPlainEq] at success
          | some restPlain =>
              simp [restPlainEq, firstEq, secondEq] at success
              subst plan
              simpa [TokenPlan.concat, TokenPlan.append,
                TokenPlan.empty] using
                TokenPlan.WellAnchored.concatPlainBookended
                  (.symbol .leftParen) (.symbol .rightParen)
                  [firstPlan, .plain (.symbol .comma),
                    secondPlan, restPlain])
        witness.consumed
      apply enclosed.candidate_eq
      rw [expressionTupleRestPlainPlan_eq]
      cases restPlansEq : (rest.map Prod.snd).mapM
          expressionTokenPlan? <;>
        simp [atomExpressionTokenPlan?, expressionTokenPlanAt?, sourceLoc,
          expressionPlans_eq_directMapM, firstEq,
          secondEq, restPlansEq, TokenPlan.parens,
          TokenPlan.commaSeparated, TokenPlan.concat,
          TokenPlan.append, TokenPlan.empty]

end Solcore.Surface.Multi
