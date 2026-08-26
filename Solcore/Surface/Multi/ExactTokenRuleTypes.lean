import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRulePassThrough
import Solcore.Surface.Multi.ExactTokenRuleSoundness
import Solcore.Surface.Multi.ExactTokenTypeAnchoring

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

private theorem TokenPlanEvidence.splitAppend
    {headCandidate tailCandidate : Option TokenPlan}
    {actual : List Token}
    (evidence : TokenPlanEvidence
      (do
        let headPlan ← headCandidate
        let tailPlan ← tailCandidate
        pure (headPlan.append tailPlan)) actual) :
    ∃ headActual tailActual,
      actual = headActual ++ tailActual ∧
        TokenPlanEvidence headCandidate headActual ∧
        TokenPlanEvidence tailCandidate tailActual := by
  rcases evidence with ⟨plan, success, relation⟩
  rcases Option.bind_eq_some_iff.mp success with
    ⟨headPlan, headEq, afterHeadEq⟩
  rcases Option.bind_eq_some_iff.mp afterHeadEq with
    ⟨tailPlan, tailEq, resultEq⟩
  injection resultEq with planEq
  subst plan
  rcases relation.split_append with
    ⟨headActual, tailActual, actualEq, headRelation, tailRelation⟩
  exact ⟨headActual, tailActual, actualEq,
    ⟨headPlan, headEq, headRelation⟩,
    ⟨tailPlan, tailEq, tailRelation⟩⟩

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
  rw [show typeExprPlanAt? false values.head =
      typeExprPlan? values.head by rfl,
    typeExprPlans_eq_mapM]

private theorem typeRuleValues_mapM_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (values : List TypeExpr) :
    (values.map (EbnfValue.ruleAtom
      (file := file) (tokens := tokens) .type)).mapM
        (fun value => value.tokenPlan? sourceRuleTokenPlanLayout) =
      values.mapM typeExprPlan? := by
  rw [List.mapM_map]
  simp [Function.comp_def, sourceRuleTokenPlanLayout, ruleTokenPlan?]
  rfl

private theorem nonemptyTypeRuleValues_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (values : NonemptyList TypeExpr) :
    (EbnfValue.list1 (.atom (.nonterminal .type))
      (values.map (EbnfValue.ruleAtom
        (file := file) (tokens := tokens) .type))).tokenPlan?
        sourceRuleTokenPlanLayout =
      (nonemptyTypeExprPlans? values).map
        TokenPlan.commaSeparated := by
  rw [EbnfValue.tokenPlan?_list1]
  rcases values with ⟨head, tail⟩
  rw [nonemptyTypeExprPlans_eq_mapM]
  simp only [NonemptyList.map, EbnfValue.tokenPlan?_ruleAtom,
    sourceRuleTokenPlanLayout, ruleTokenPlan?]
  rw [List.mapM_map]
  simp only [Function.comp_def, EbnfValue.tokenPlan?_ruleAtom,
    ruleTokenPlan?]
  change (do
    let headPlan ← typeExprPlan? head
    let tailPlans ← tail.mapM typeExprPlan?
    pure (TokenPlan.commaSeparated (headPlan :: tailPlans))) =
      Option.map TokenPlan.commaSeparated (do
        let headPlan ← typeExprPlan? head
        let tailPlans ← tail.mapM typeExprPlan?
        pure (headPlan :: tailPlans))
  cases typeExprPlan? head <;>
    cases tail.mapM typeExprPlan? <;> rfl

private def typeTupleRestPlainPlan?
    {file : WorkspaceFile} {tokens : List Token} :
    List (MatchedTerminal file tokens (.symbol .comma) × TypeExpr) →
      Option TokenPlan
  | [] => some .empty
  | entry :: rest => do
      let typePlan ← typeExprPlan? entry.2
      let restPlan ← typeTupleRestPlainPlan? rest
      pure (((TokenPlan.plain (.symbol .comma)).append
        typePlan).append restPlan)

private theorem typeTupleRestPlainPlan_eq
    {file : WorkspaceFile} {tokens : List Token}
    (rest : List
      (MatchedTerminal file tokens (.symbol .comma) × TypeExpr)) :
    typeTupleRestPlainPlan? rest = (do
      let plans ← (rest.map Prod.snd).mapM typeExprPlan?
      pure (.concat (plans.map fun plan =>
        (TokenPlan.plain (.symbol .comma)).append plan))) := by
  induction rest with
  | nil => simp [typeTupleRestPlainPlan?, TokenPlan.concat,
      TokenPlan.empty]
  | cons entry rest induction =>
      rw [typeTupleRestPlainPlan?, List.map_cons,
        List.mapM_cons, induction]
      cases typeEq : typeExprPlan? entry.2 <;>
        cases tailPlansEq : (rest.map Prod.snd).mapM
          typeExprPlan? <;>
          simp [TokenPlan.concat, TokenPlan.append]

private abbrev typeTupleRestExpr : EbnfExpr :=
  .group (.sequence [
    .atom (.terminal (.symbol .comma)),
    .atom (.nonterminal .type)])

private def typeTupleRestValue
    {file : WorkspaceFile} {tokens : List Token}
    (entry : MatchedTerminal file tokens (.symbol .comma) × TypeExpr) :
    EbnfValue file tokens typeTupleRestExpr :=
  EbnfValue.group _ <| EbnfValue.sequence _ <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .comma) entry.1) <|
    EbnfValues.cons _ _
      (EbnfValue.ruleAtom .type entry.2) EbnfValues.nil

private theorem typeTupleRestValue_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (entry : MatchedTerminal file tokens (.symbol .comma) × TypeExpr) :
    (typeTupleRestValue entry).tokenPlan?
        sourceRuleTokenPlanLayout = (do
      let typePlan ← typeExprPlan? entry.2
      pure ((TokenPlan.exact (.symbol .comma) entry.1.span).append
        typePlan)) := by
  cases typeEq : typeExprPlan? entry.2 <;>
    simp [typeTupleRestValue, typeTupleRestExpr,
      sourceRuleTokenPlanLayout, ruleTokenPlan?, typeEq,
      MatchedTerminal.physicalTokenPlan_symbol,
      TokenPlan.append, TokenPlan.empty]

private theorem typeTupleRestEvidence_toPlain
    {file : WorkspaceFile} {tokens : List Token}
    (rest : List
      (MatchedTerminal file tokens (.symbol .comma) × TypeExpr))
    {actual : List Token}
    (evidence : TokenPlanEvidence
      ((EbnfValue.star typeTupleRestExpr
        (rest.map typeTupleRestValue)).tokenPlan?
          sourceRuleTokenPlanLayout) actual) :
    TokenPlanEvidence (typeTupleRestPlainPlan? rest) actual := by
  induction rest generalizing actual with
  | nil =>
      have flattened := evidence.candidate_eq
        (EbnfValue.tokenPlan?_star sourceRuleTokenPlanLayout
          typeTupleRestExpr [])
      simpa [typeTupleRestPlainPlan?, TokenPlan.concat,
        TokenPlan.empty] using flattened
  | cons entry rest induction =>
      have flattened := evidence.candidate_eq
        (EbnfValue.tokenPlan?_star sourceRuleTokenPlanLayout
          typeTupleRestExpr
          ((entry :: rest).map typeTupleRestValue))
      rw [List.map_cons, List.mapM_cons,
        typeTupleRestValue_tokenPlan?] at flattened
      cases typeEq : typeExprPlan? entry.2 with
      | none =>
          rcases flattened with ⟨plan, success, relation⟩
          simp [typeEq] at success
      | some typePlan =>
          cases tailPlansEq :
              (rest.map typeTupleRestValue).mapM
                (fun value => value.tokenPlan?
                  sourceRuleTokenPlanLayout) with
          | none =>
              rcases flattened with ⟨plan, success, relation⟩
              simp [typeEq, tailPlansEq] at success
          | some tailPlans =>
              have exactEvidence : TokenPlanEvidence
                  (Option.some ((TokenPlan.exact (.symbol .comma)
                    entry.1.span).append typePlan |>.append
                      (TokenPlan.concat tailPlans))) actual := by
                simpa [typeEq, tailPlansEq, TokenPlan.concat,
                  TokenPlan.append, TokenPlan.empty] using flattened
              rcases exactEvidence with ⟨plan, success, relation⟩
              simp only [Option.some.injEq] at success
              subst plan
              rcases relation.split_append with
                ⟨headActual, tailActual, actualEq,
                  headRelation, tailRelation⟩
              have headPlainRelation : TokenSlot.ListMatches
                  ((TokenPlan.plain (.symbol .comma)).append
                    typePlan).slots headActual := by
                simpa [TokenPlan.append, TokenPlan.empty] using
                  (TokenSlot.ListMatches.exactBetweenToPlain
                    (left := TokenPlan.empty)
                    (right := typePlan) headRelation)
              have headEvidence := TokenPlanEvidence.some headPlainRelation
              have tailEvidence : TokenPlanEvidence
                  ((EbnfValue.star typeTupleRestExpr
                    (rest.map typeTupleRestValue)).tokenPlan?
                      sourceRuleTokenPlanLayout) tailActual := by
                refine ⟨TokenPlan.concat tailPlans, ?_, tailRelation⟩
                rw [EbnfValue.tokenPlan?_star, tailPlansEq]
                rfl
              have tailPlainEvidence := induction tailEvidence
              have combined := headEvidence.append tailPlainEvidence
              have onActual := combined.actual_eq actualEq.symm
              apply onActual.candidate_eq
              simp [typeTupleRestPlainPlan?, typeEq,
                TokenPlan.append_assoc]

private theorem typeTuplePlainCandidate_eq
    {file : WorkspaceFile} {tokens : List Token}
    (first second : TypeExpr)
    (rest : List
      (MatchedTerminal file tokens (.symbol .comma) × TypeExpr)) :
    (do
      let firstPlan ← typeExprPlan? first
      let secondPlan ← typeExprPlan? second
      let restPlan ← typeTupleRestPlainPlan? rest
      pure (TokenPlan.concat [
        .plain (.symbol .leftParen), firstPlan,
        .plain (.symbol .comma), secondPlan,
        restPlan, .plain (.symbol .rightParen)])) =
    (do
      let plans ← typeExprPlans?
        (first :: second :: rest.map Prod.snd)
      pure (.parens (.commaSeparated plans))) := by
  rw [typeTupleRestPlainPlan_eq, typeExprPlans_eq_mapM]
  simp only [List.mapM_cons]
  cases firstEq : typeExprPlan? first <;>
    cases secondEq : typeExprPlan? second <;>
      cases restPlansEq : (rest.map Prod.snd).mapM
        typeExprPlan? <;>
        simp [TokenPlan.parens, TokenPlan.commaSeparated,
          TokenPlan.concat, TokenPlan.append, TokenPlan.empty,
          List.append_assoc]

/-- Full-type reductions preserve recursive type plans and retained markers. -/
theorem type_tokenPlanSound :
    GrammarRuleTokenPlanSound .type := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  cases reduces with
  | typeComptime origin finish comptimeToken inner comptimeProjects witness =>
      change TokenPlanEvidence
        (typeExprPlan? (sourceLoc witness (.comptime
          (RuleReduction.marker comptimeToken comptimeProjects) inner)))
        (PhysicalTokens tokens origin finish)
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValues.tokenPlan?_nil,
        MatchedTerminal.physicalTokenPlan_contextualKeyword]
        at sequenceEvidence
      cases innerEq : typeExprPlan? inner with
      | none =>
          rcases sequenceEvidence with ⟨plan, success, relation⟩
          simp [sourceRuleTokenPlanLayout, ruleTokenPlan?, innerEq]
            at success
      | some innerPlan =>
          have innerEqAt : typeExprPlanAt? false inner =
              some innerPlan := innerEq
          have coreEvidence : TokenPlanEvidence
              (Option.some ((TokenPlan.exact
                (.identifier ContextualKeyword.comptimeKw.spelling)
                comptimeToken.span).append innerPlan))
              (PhysicalTokens tokens origin finish) := by
            simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?, innerEq]
              using sequenceEvidence
          have enclosed := coreEvidence.enclose
            (by
              intro plan success
              simp only [Option.some.injEq] at success
              subst plan
              exact TokenPlan.WellAnchored.append
                (TokenPlan.WellAnchored.exact _ _)
                (typeExprPlan?_wellAnchored inner innerPlan innerEq))
            witness.consumed
          simpa [typeExprPlan?, typeExprPlanAt?, sourceLoc,
            RuleReduction.marker, RuleReduction.terminalLoc, innerEqAt]
            using enclosed
  | typeAtomOnly origin finish atom =>
      exact RuleReduction.SemanticPassThrough.tokenPlanEvidence
        (by apply RuleReduction.SemanticPassThrough.typeAtomOnly)
        inputEvidence
  | typeFunction origin finish domain arrow codomain witness =>
      change TokenPlanEvidence
        (typeExprPlan? (sourceLoc witness (.function domain codomain)))
        (PhysicalTokens tokens origin finish)
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
        MatchedTerminal.physicalTokenPlan_symbol]
        at sequenceEvidence
      cases domainEq : typeAtomPlan? domain with
      | none =>
          rcases sequenceEvidence with ⟨plan, success, relation⟩
          simp [sourceRuleTokenPlanLayout, ruleTokenPlan?, domainEq]
            at success
      | some domainPlan =>
          cases codomainEq : typeExprPlan? codomain with
          | none =>
              rcases sequenceEvidence with ⟨plan, success, relation⟩
              simp [sourceRuleTokenPlanLayout, ruleTokenPlan?, domainEq,
                codomainEq] at success
          | some codomainPlan =>
              have domainEqAt : typeExprPlanAt? true domain =
                  some domainPlan := domainEq
              have codomainEqAt : typeExprPlanAt? false codomain =
                  some codomainPlan := codomainEq
              have exactEvidence : TokenPlanEvidence
                  (Option.some (TokenPlan.concat [
                    domainPlan,
                    .exact (.symbol .arrow) arrow.span,
                    codomainPlan]))
                  (PhysicalTokens tokens origin finish) := by
                simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?, domainEq,
                  codomainEq, TokenPlan.concat, TokenPlan.append,
                  TokenPlan.empty] using sequenceEvidence
              rcases exactEvidence with ⟨plan, success, relation⟩
              simp only [Option.some.injEq] at success
              subst plan
              have coreRelation : TokenSlot.ListMatches
                  (domainPlan.append
                    ((TokenPlan.plain (.symbol .arrow)).append
                      codomainPlan)).slots
                  (PhysicalTokens tokens origin finish) := by
                have sourceRelation : TokenSlot.ListMatches
                    (domainPlan.append
                      ((TokenPlan.exact (.symbol .arrow) arrow.span).append
                        codomainPlan)).slots
                    (PhysicalTokens tokens origin finish) := by
                  simpa [TokenPlan.concat, TokenPlan.append,
                    List.append_assoc]
                    using relation
                exact TokenSlot.ListMatches.exactBetweenToPlain
                  sourceRelation
              have coreEvidence := TokenPlanEvidence.some coreRelation
              have enclosed := coreEvidence.enclose
                (by
                  intro plan success
                  simp only [Option.some.injEq] at success
                  subst plan
                  exact TokenPlan.WellAnchored.append
                    (typeAtomPlan?_wellAnchored
                      domain domainPlan domainEq)
                    (TokenPlan.WellAnchored.append
                      (TokenPlan.WellAnchored.plain _)
                      (typeExprPlan?_wellAnchored
                        codomain codomainPlan codomainEq)))
                witness.consumed
              simpa [typeExprPlan?, typeExprPlanAt?, sourceLoc,
                domainEqAt, codomainEqAt, TokenPlan.concat,
                TokenPlan.append] using enclosed

/-- Atomic-type reductions preserve names, proxies, tuples, and grouping. -/
theorem typeAtom_tokenPlanSound :
    GrammarRuleTokenPlanSound .typeAtom := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  cases reduces with
  | typeAtomProxy origin finish atToken inner witness =>
      change TokenPlanEvidence
        (typeAtomPlan? (sourceLoc witness (.proxy
          (RuleReduction.terminalLoc atToken ()) inner)))
        (PhysicalTokens tokens origin finish)
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValues.tokenPlan?_nil,
        MatchedTerminal.physicalTokenPlan_symbol]
        at sequenceEvidence
      cases innerEq : typeAtomPlan? inner with
      | none =>
          rcases sequenceEvidence with ⟨plan, success, relation⟩
          simp [sourceRuleTokenPlanLayout, ruleTokenPlan?, innerEq]
            at success
      | some innerPlan =>
          have innerEqAt : typeExprPlanAt? true inner =
              some innerPlan := innerEq
          have coreEvidence : TokenPlanEvidence
              (Option.some ((TokenPlan.exact (.symbol .at)
                atToken.span).append innerPlan))
              (PhysicalTokens tokens origin finish) := by
            simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?, innerEq]
              using sequenceEvidence
          have enclosed := coreEvidence.enclose
            (by
              intro plan success
              simp only [Option.some.injEq] at success
              subst plan
              exact TokenPlan.WellAnchored.append
                (TokenPlan.WellAnchored.exact _ _)
                (typeAtomPlan?_wellAnchored inner innerPlan innerEq))
            witness.consumed
          simpa [typeAtomPlan?, typeExprPlanAt?, sourceLoc,
            RuleReduction.terminalLoc, innerEqAt] using enclosed
  | typeAtomNamedWithoutArguments origin finish name witness =>
      change TokenPlanEvidence
        (typeAtomPlan? (sourceLoc witness (.named name none)))
        (PhysicalTokens tokens origin finish)
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
        simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?]
          using sequenceEvidence
      have enclosed := nameEvidence.enclose
        (by
          intro plan success
          simp only [Option.some.injEq] at success
          subst plan
          exact qualifiedNamePlan_wellAnchored name)
        witness.consumed
      simpa [typeAtomPlan?, typeExprPlanAt?, sourceLoc] using enclosed
  | typeAtomNamedWithArguments origin finish name openParen arguments
      closeParen witness =>
      change TokenPlanEvidence
        (typeAtomPlan? (sourceLoc witness (.named name
          (RuleReduction.arguments
            (some (openParen, arguments, closeParen, ()))))))
        (PhysicalTokens tokens origin finish)
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
        MatchedTerminal.physicalTokenPlan_symbol]
        at sequenceEvidence
      rw [nonemptyTypeRuleValues_tokenPlan? arguments]
        at sequenceEvidence
      cases argumentPlansEq : nonemptyTypeExprPlans? arguments with
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
          simpa [typeAtomPlan?, typeExprPlanAt?, sourceLoc,
            RuleReduction.arguments, argumentPlansEq]
            using enclosed
  | typeAtomEmptyTuple origin finish openParen closeParen witness =>
      change TokenPlanEvidence
        (typeAtomPlan? (sourceLoc witness (.tuple [])))
        (PhysicalTokens tokens origin finish)
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
        simpa [TokenPlan.concat, TokenPlan.append, TokenPlan.empty]
          using sequenceEvidence
      rcases exactEvidence with ⟨plan, success, relation⟩
      simp only [Option.some.injEq] at success
      subst plan
      have coreEvidence := TokenPlanEvidence.some relation.twoExactToPlain
      have enclosed := coreEvidence.enclose
        (by
          intro plan success
          simp only [Option.some.injEq] at success
          subst plan
          exact TokenPlan.WellAnchored.parens _)
        witness.consumed
      simpa [typeAtomPlan?, typeExprPlanAt?, sourceLoc,
        TokenPlan.parens] using enclosed
  | typeAtomGroup origin finish openParen inner closeParen witness =>
      change TokenPlanEvidence
        (typeAtomPlan? (sourceLoc witness (.group inner)))
        (PhysicalTokens tokens origin finish)
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValues.tokenPlan?_nil,
        MatchedTerminal.physicalTokenPlan_symbol] at sequenceEvidence
      cases innerEq : typeExprPlan? inner with
      | none =>
          rcases sequenceEvidence with ⟨plan, success, relation⟩
          simp [sourceRuleTokenPlanLayout, ruleTokenPlan?, innerEq]
            at success
      | some innerPlan =>
          have innerEqAt : typeExprPlanAt? false inner =
              some innerPlan := innerEq
          have exactEvidence : TokenPlanEvidence
              (Option.some (TokenPlan.concat [
                .exact (.symbol .leftParen) openParen.span,
                innerPlan,
                .exact (.symbol .rightParen) closeParen.span]))
              (PhysicalTokens tokens origin finish) := by
            simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?, innerEq,
              TokenPlan.concat, TokenPlan.append, TokenPlan.empty]
              using sequenceEvidence
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
              exact TokenPlan.WellAnchored.parens innerPlan)
            witness.consumed
          simpa [typeAtomPlan?, typeExprPlanAt?, sourceLoc, innerEq,
            innerEqAt, TokenPlan.parens] using enclosed
  | typeAtomTuple origin finish openParen first comma second rest closeParen
      witness =>
      change TokenPlanEvidence
        (typeAtomPlan? (sourceLoc witness
          (.tuple (first :: second :: rest.map Prod.snd))))
        (PhysicalTokens tokens origin finish)
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
        ⟨openActual, afterOpenActual, physicalEq,
          openEvidence, afterOpenEvidence⟩
      rcases afterOpenEvidence.splitAppend with
        ⟨firstActual, afterFirstActual, afterOpenEq,
          firstEvidence, afterFirstEvidence⟩
      rcases afterFirstEvidence.splitAppend with
        ⟨commaActual, afterCommaActual, afterFirstEq,
          commaEvidence, afterCommaEvidence⟩
      rcases afterCommaEvidence.splitAppend with
        ⟨secondActual, afterSecondActual, afterCommaEq,
          secondEvidence, afterSecondEvidence⟩
      rcases afterSecondEvidence.splitAppend with
        ⟨restActual, afterRestActual, afterSecondEq,
          restEvidence, afterRestEvidence⟩
      rcases afterRestEvidence.splitAppend with
        ⟨closeActual, emptyActual, afterRestEq,
          closeEvidence, emptyEvidence⟩
      have openPlain := openEvidence.exactToPlain
      have commaPlain := commaEvidence.exactToPlain
      have closePlain := closeEvidence.exactToPlain
      have firstTypeEvidence : TokenPlanEvidence
          (typeExprPlan? first) firstActual := by
        simpa only [sourceRuleTokenPlanLayout, ruleTokenPlan?]
          using firstEvidence
      have secondTypeEvidence : TokenPlanEvidence
          (typeExprPlan? second) secondActual := by
        simpa only [sourceRuleTokenPlanLayout, ruleTokenPlan?]
          using secondEvidence
      change TokenPlanEvidence
        ((EbnfValue.star typeTupleRestExpr
          (rest.map typeTupleRestValue)).tokenPlan?
            sourceRuleTokenPlanLayout) restActual at restEvidence
      have restPlain := typeTupleRestEvidence_toPlain rest restEvidence
      have combined := openPlain.append <|
        firstTypeEvidence.append <|
          commaPlain.append <|
            secondTypeEvidence.append <|
              restPlain.append <|
                closePlain.append emptyEvidence
      have actualEq : PhysicalTokens tokens origin finish =
          openActual ++ (firstActual ++ (commaActual ++
            (secondActual ++ (restActual ++
              (closeActual ++ emptyActual))))) := by
        rw [physicalEq, afterOpenEq, afterFirstEq, afterCommaEq,
          afterSecondEq, afterRestEq]
      have onActual := combined.actual_eq actualEq.symm
      have coreEvidence : TokenPlanEvidence
          (do
            let firstPlan ← typeExprPlan? first
            let secondPlan ← typeExprPlan? second
            let restPlan ← typeTupleRestPlainPlan? rest
            pure (TokenPlan.concat [
              .plain (.symbol .leftParen), firstPlan,
              .plain (.symbol .comma), secondPlan,
              restPlan, .plain (.symbol .rightParen)]))
          (PhysicalTokens tokens origin finish) := by
        apply onActual.candidate_eq
        cases typeExprPlan? first <;>
          cases typeExprPlan? second <;>
            cases typeTupleRestPlainPlan? rest <;>
              simp [TokenPlan.concat, TokenPlan.append, TokenPlan.empty]
      have tupleEvidence := coreEvidence.candidate_eq
        (typeTuplePlainCandidate_eq first second rest)
      have enclosed := tupleEvidence.enclose
        (by
          intro plan success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨plans, plansEq, resultEq⟩
          injection resultEq with planEq
          subst plan
          exact TokenPlan.WellAnchored.parens _)
        witness.consumed
      apply enclosed.candidate_eq
      simp only [typeAtomPlan?, typeExprPlanAt?, sourceLoc]
      cases typeExprPlans?
        (first :: second :: rest.map Prod.snd) <;> rfl

end Solcore.Surface.Multi
