import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRuleSoundness
import Solcore.Surface.Multi.ExactTokenTypeAnchoring

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace
open Lean Lean.Elab Lean.Elab.Tactic

elab "unfoldForallBinderNonemptyTypePlanCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.nonemptyTypePlans?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] =>
      unfoldTarget declaration
  | _ =>
      throwError
        "the declaration visitor contains an unexpected type-plan helper"

private abbrev forallBinderArgumentChildren : List EbnfExpr := [
  .atom (.terminal (.symbol .leftParen)),
  .list1 (.atom (.nonterminal .type)),
  .atom (.terminal (.symbol .rightParen))]

private abbrev forallBinderBoundedChildren : List EbnfExpr := [
  .atom (.terminal (.category .identifier)),
  .atom (.terminal (.symbol .colon)),
  .atom (.nonterminal .qualifiedName),
  .optional (.sequence forallBinderArgumentChildren)]

private abbrev forallBinderSourceBranches : List EbnfExpr := [
  .atom (.terminal (.category .identifier)),
  .sequence forallBinderBoundedChildren]

private def forallBinderBoundedWithArgumentsInput
    {file : WorkspaceFile} {tokens : List Token}
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (colon : MatchedTerminal file tokens (.symbol .colon))
    (className : QualifiedName)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (arguments : NonemptyList TypeExpr)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen)) :
    EbnfValue file tokens (.sequence forallBinderBoundedChildren) :=
  EbnfValue.sequence _ <|
      EbnfValues.cons _ _
        (EbnfValue.terminalAtom (.category .identifier) name.matched) <|
      EbnfValues.cons _ _
        (EbnfValue.terminalAtom (.symbol .colon) colon) <|
      EbnfValues.cons _ _
        (EbnfValue.ruleAtom .qualifiedName className) <|
      EbnfValues.cons _ _
        (EbnfValue.optional _ (some <|
          EbnfValue.sequence _ <|
            EbnfValues.cons _ _
              (EbnfValue.terminalAtom (.symbol .leftParen) openParen) <|
            EbnfValues.cons _ _
              (EbnfValue.list1 _
                (arguments.map (EbnfValue.ruleAtom .type))) <|
            EbnfValues.cons _ _
              (EbnfValue.terminalAtom (.symbol .rightParen) closeParen)
              EbnfValues.nil))
        EbnfValues.nil

/-- An identifier projection equates the scanned token plan with the plan
retained by the binder node. -/
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
    · have parsedEq := Option.some.inj parseEq
      rw [← parsedEq]
      rfl
    · contradiction
  simp [MatchedTerminal.physicalTokenPlan, identifierPlan,
    RuleReduction.terminalLoc, valueEq, payloadEq, spellingEq]

/-- The recursive type-list visitor agrees with the standard monadic
left-to-right traversal. -/
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

private theorem forallBinderBoundedWithArgumentsInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (colon : MatchedTerminal file tokens (.symbol .colon))
    (className : QualifiedName)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (arguments : NonemptyList TypeExpr)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (nameProjects : IdentifierProjects name.matched
      name.spelling name.parsed) :
    (forallBinderBoundedWithArgumentsInput name colon className openParen
      arguments closeParen).tokenPlan? sourceRuleTokenPlanLayout = (do
        let headPlan ← ruleTokenPlan? .type arguments.head
        let tailPlans ← arguments.tail.mapM (ruleTokenPlan? .type)
        pure ((identifierPlan
          (RuleReduction.terminalLoc name.matched name.parsed)).append
            ((TokenPlan.exact (.symbol .colon) colon.span).append
              ((qualifiedNamePlan className).append
                ((TokenPlan.exact (.symbol .leftParen)
                  openParen.span).append
                  ((TokenPlan.commaSeparated (headPlan :: tailPlans)).append
                    (TokenPlan.exact (.symbol .rightParen)
                      closeParen.span))))))) := by
  unfold forallBinderBoundedWithArgumentsInput
  rw [EbnfValue.tokenPlan?_sequence]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_terminalAtom]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_terminalAtom]
  rw [EbnfValues.tokenPlan?_cons]
  rw [EbnfValue.tokenPlan?_ruleAtom]
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
  rw [identifierPhysicalPlan_eq name nameProjects]
  rw [MatchedTerminal.physicalTokenPlan_symbol,
    MatchedTerminal.physicalTokenPlan_symbol,
    MatchedTerminal.physicalTokenPlan_symbol]
  simp [NonemptyList.map, Function.comp_def, sourceRuleTokenPlanLayout,
    TokenPlan.append_assoc] <;>
    cases headEq : ruleTokenPlan? .type arguments.head <;>
    cases tailEq : arguments.tail.mapM (ruleTokenPlan? .type) <;>
    simp [ruleTokenPlan?, TokenPlan.append_assoc]

/-- The no-argument binder plan exposes its fixed empty suffix. -/
private theorem forallBinderPlan?_bounded_none
    (span : SourceSpan) (name : IdentifierOccurrence)
    (className : QualifiedName) :
    forallBinderPlan? ({
      span := span
      payload := .bounded name className none
    } : ForallBinder) = some (.enclose span (.concat [
      identifierPlan name,
      .plain (.symbol .colon),
      qualifiedNamePlan className,
      .empty])) := by
  rfl

/-- The argument-bearing binder plan exposes the shared recursive type-list
visitor used by source reconstruction. -/
private theorem forallBinderPlan?_bounded_some
    (span : SourceSpan) (name : IdentifierOccurrence)
    (className : QualifiedName) (arguments : NonemptyList TypeExpr) :
    forallBinderPlan? ({
      span := span
      payload := .bounded name className (some arguments)
    } : ForallBinder) = (do
      let argumentPlans ← nonemptyTypeExprPlans? arguments
      pure (.enclose span (.concat [
        identifierPlan name,
        .plain (.symbol .colon),
        qualifiedNamePlan className,
        .parens (.commaSeparated argumentPlans)]))) := by
  simp_all! [forallBinderPlan?]
  unfoldForallBinderNonemptyTypePlanCore
  cases nonemptyTypeExprPlans? arguments <;> simp

/-- Forall-binder reductions preserve the binder, bound, and optional
nonempty argument list while weakening only fixed punctuation. -/
theorem forallBinder_tokenPlanSound :
    GrammarRuleTokenPlanSound .forallBinder := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | forallBinderBare origin finish name nameProjects witness =>
      change EbnfValue file tokens (.choice [
        .atom (.terminal (.category .identifier)),
        .sequence [
          .atom (.terminal (.category .identifier)),
          .atom (.terminal (.symbol .colon)),
          .atom (.nonterminal .qualifiedName),
          .optional (.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))])]]) at input
      rw [← inputEq] at inputEvidence
      change TokenPlanEvidence
        (forallBinderPlan? (sourceLoc witness (.bare
          (RuleReduction.terminalLoc name.matched name.parsed))))
        (PhysicalTokens tokens origin finish)
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          some (identifierPlan
            (RuleReduction.terminalLoc name.matched name.parsed)) := by
        rw [inputEq]
        simp [m2cV1, m2cV1Rhs, Grammar.choice, Grammar.identifier,
          Grammar.category, Grammar.terminal, Grammar.sequence,
          Grammar.symbol, Grammar.nonterminal, Grammar.optional,
          Grammar.list1,
          sourceRuleTokenPlanLayout,
          identifierPhysicalPlan_eq name nameProjects]
      have physicalEvidence := inputEvidence.candidate_eq candidateEq
      have enclosed := TokenPlanEvidence.enclose physicalEvidence
        (fun plan success => by
          simp only [Option.some.injEq] at success
          subst plan
          exact identifierPlan_wellAnchored _)
        witness.consumed
      simpa [forallBinderPlan?, sourceLoc] using enclosed
  | forallBinderBoundedWithoutArguments origin finish name colon className
      nameProjects witness =>
      change EbnfValue file tokens (.choice [
        .atom (.terminal (.category .identifier)),
        .sequence [
          .atom (.terminal (.category .identifier)),
          .atom (.terminal (.symbol .colon)),
          .atom (.nonterminal .qualifiedName),
          .optional (.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))])]]) at input
      rw [← inputEq] at inputEvidence
      change TokenPlanEvidence
        (forallBinderPlan? (sourceLoc witness (.bounded
          (RuleReduction.terminalLoc name.matched name.parsed)
          className none)))
        (PhysicalTokens tokens origin finish)
      let namePlan := identifierPlan
        (RuleReduction.terminalLoc name.matched name.parsed)
      let classPlan := qualifiedNamePlan className
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          some (namePlan.append
            ((TokenPlan.exact (.symbol .colon) colon.span).append
              classPlan)) := by
        rw [inputEq]
        simp [m2cV1, m2cV1Rhs, Grammar.choice, Grammar.identifier,
          Grammar.category, Grammar.terminal, Grammar.sequence,
          Grammar.symbol, Grammar.nonterminal, Grammar.optional,
          Grammar.list1,
          sourceRuleTokenPlanLayout, ruleTokenPlan?,
          identifierPhysicalPlan_eq name nameProjects,
          MatchedTerminal.physicalTokenPlan_symbol, namePlan, classPlan]
      have physicalEvidence := inputEvidence.candidate_eq candidateEq
      let innerPlan := namePlan.append
        ((TokenPlan.plain (.symbol .colon)).append classPlan)
      rcases physicalEvidence with ⟨plan, planCandidateEq, relation⟩
      injection planCandidateEq with planEq
      rw [← planEq] at relation
      have innerRelation : TokenSlot.ListMatches innerPlan.slots
          (PhysicalTokens tokens origin finish) := by
        apply TokenSlot.ListMatches.exactBetweenToPlain
          (left := namePlan) (right := classPlan)
        exact relation
      have innerAnchored : innerPlan.WellAnchored := by
        apply TokenPlan.WellAnchored.append
          (identifierPlan_wellAnchored _)
        exact TokenPlan.WellAnchored.append
          (TokenPlan.WellAnchored.plain (.symbol .colon))
          (qualifiedNamePlan_wellAnchored className)
      have enclosed := TokenPlanEvidence.enclose
        (TokenPlanEvidence.some innerRelation)
        (fun plan success => by
          simp only [Option.some.injEq] at success
          subst plan
          exact innerAnchored)
        witness.consumed
      apply enclosed.candidate_eq
      simp only [sourceLoc]
      rw [forallBinderPlan?_bounded_none]
      simp [innerPlan, namePlan, classPlan, TokenPlan.concat_cons]
  | forallBinderBoundedWithArguments origin finish name colon className
      openParen arguments closeParen nameProjects witness =>
      change EbnfValue file tokens (.choice [
        .atom (.terminal (.category .identifier)),
        .sequence [
          .atom (.terminal (.category .identifier)),
          .atom (.terminal (.symbol .colon)),
          .atom (.nonterminal .qualifiedName),
          .optional (.sequence [
            .atom (.terminal (.symbol .leftParen)),
            .list1 (.atom (.nonterminal .type)),
            .atom (.terminal (.symbol .rightParen))])]]) at input
      rw [← inputEq] at inputEvidence
      change TokenPlanEvidence
        (forallBinderPlan? (sourceLoc witness (.bounded
          (RuleReduction.terminalLoc name.matched name.parsed)
          className (RuleReduction.arguments
            (some (openParen, arguments, closeParen, ()))))))
        (PhysicalTokens tokens origin finish)
      let namePlan := identifierPlan
        (RuleReduction.terminalLoc name.matched name.parsed)
      let classPlan := qualifiedNamePlan className
      have candidateEq : input.tokenPlan? sourceRuleTokenPlanLayout =
          (do
            let headPlan ← ruleTokenPlan? .type arguments.head
            let tailPlans ← arguments.tail.mapM (ruleTokenPlan? .type)
            pure (namePlan.append
              ((TokenPlan.exact (.symbol .colon) colon.span).append
                (classPlan.append
                  ((TokenPlan.exact (.symbol .leftParen)
                    openParen.span).append
                    ((TokenPlan.commaSeparated
                      (headPlan :: tailPlans)).append
                      (TokenPlan.exact (.symbol .rightParen)
                        closeParen.span))))))) := by
        rw [inputEq]
        simp only [m2cV1, m2cV1Rhs, Grammar.choice, Grammar.identifier,
          Grammar.category, Grammar.terminal, Grammar.sequence,
          Grammar.symbol, Grammar.nonterminal, Grammar.optional,
          Grammar.list1]
        rw [EbnfValue.tokenPlan?_transport]
        rw [EbnfValue.tokenPlan?_choice]
        change (forallBinderBoundedWithArgumentsInput name colon className
          openParen arguments closeParen).tokenPlan?
            sourceRuleTokenPlanLayout = _
        simpa [namePlan, classPlan] using
          forallBinderBoundedWithArgumentsInput_tokenPlan? name colon
            className openParen arguments closeParen nameProjects
      have physicalEvidence := inputEvidence.candidate_eq candidateEq
      cases headEq : ruleTokenPlan? .type arguments.head with
      | none =>
          simp [headEq, TokenPlanEvidence] at physicalEvidence
      | some headPlan =>
          cases tailEq : arguments.tail.mapM (ruleTokenPlan? .type) with
          | none =>
              simp [headEq, tailEq, TokenPlanEvidence] at physicalEvidence
          | some tailPlans =>
              simp only [headEq, tailEq] at physicalEvidence
              rcases physicalEvidence with ⟨plan, planCandidateEq, relation⟩
              let argumentPlan := TokenPlan.commaSeparated
                (headPlan :: tailPlans)
              let sourcePlan := namePlan.append
                ((TokenPlan.exact (.symbol .colon) colon.span).append
                  (classPlan.append
                    ((TokenPlan.exact (.symbol .leftParen)
                      openParen.span).append
                      (argumentPlan.append
                        (TokenPlan.exact (.symbol .rightParen)
                          closeParen.span)))))
              change some sourcePlan = some plan at planCandidateEq
              injection planCandidateEq with planEq
              rw [← planEq] at relation
              dsimp [sourcePlan] at relation
              let afterColon := namePlan.append
                ((TokenPlan.plain (.symbol .colon)).append
                  (classPlan.append
                    ((TokenPlan.exact (.symbol .leftParen)
                      openParen.span).append
                      (argumentPlan.append
                        (TokenPlan.exact (.symbol .rightParen)
                          closeParen.span)))))
              have colonRelation : TokenSlot.ListMatches afterColon.slots
                  (PhysicalTokens tokens origin finish) := by
                apply TokenSlot.ListMatches.exactBetweenToPlain
                  (left := namePlan)
                  (right := classPlan.append
                    ((TokenPlan.exact (.symbol .leftParen)
                      openParen.span).append
                      (argumentPlan.append
                        (TokenPlan.exact (.symbol .rightParen)
                          closeParen.span))))
                exact relation
              let afterOpen := namePlan.append
                ((TokenPlan.plain (.symbol .colon)).append
                  (classPlan.append
                    ((TokenPlan.plain (.symbol .leftParen)).append
                      (argumentPlan.append
                        (TokenPlan.exact (.symbol .rightParen)
                          closeParen.span)))))
              have openRelation : TokenSlot.ListMatches afterOpen.slots
                  (PhysicalTokens tokens origin finish) := by
                have converted :=
                  TokenSlot.ListMatches.exactBetweenToPlain
                    (left := namePlan.append
                      ((TokenPlan.plain (.symbol .colon)).append classPlan))
                    (right := argumentPlan.append
                      (TokenPlan.exact (.symbol .rightParen)
                        closeParen.span))
                    (kind := .symbol .leftParen)
                    (span := openParen.span)
                    (by
                      simpa [afterColon, TokenPlan.append_assoc] using
                        colonRelation)
                simpa [afterOpen, TokenPlan.append_assoc] using converted
              let innerPlan := namePlan.append
                ((TokenPlan.plain (.symbol .colon)).append
                  (classPlan.append
                    ((TokenPlan.plain (.symbol .leftParen)).append
                      (argumentPlan.append
                        (TokenPlan.plain (.symbol .rightParen))))))
              have innerRelation : TokenSlot.ListMatches innerPlan.slots
                  (PhysicalTokens tokens origin finish) := by
                have converted :=
                  TokenSlot.ListMatches.exactBetweenToPlain
                    (left := namePlan.append
                      ((TokenPlan.plain (.symbol .colon)).append
                        (classPlan.append
                          ((TokenPlan.plain (.symbol .leftParen)).append
                            argumentPlan))))
                    (right := TokenPlan.empty)
                    (kind := .symbol .rightParen)
                    (span := closeParen.span)
                    (by
                      simpa [afterOpen, TokenPlan.append_assoc] using
                        openRelation)
                simpa [innerPlan, TokenPlan.append_assoc] using converted
              have innerAnchored : innerPlan.WellAnchored := by
                apply TokenPlan.WellAnchored.append
                  (identifierPlan_wellAnchored _)
                apply TokenPlan.WellAnchored.append
                  (TokenPlan.WellAnchored.plain (.symbol .colon))
                apply TokenPlan.WellAnchored.append
                  (qualifiedNamePlan_wellAnchored className)
                exact TokenPlan.WellAnchored.parens argumentPlan
              have enclosed := TokenPlanEvidence.enclose
                (TokenPlanEvidence.some innerRelation)
                (fun plan success => by
                  simp only [Option.some.injEq] at success
                  subst plan
                  exact innerAnchored)
                witness.consumed
              have headTypeEq : typeExprPlan? arguments.head =
                  some headPlan := by
                simpa only [ruleTokenPlan?] using headEq
              have tailTypeEq : arguments.tail.mapM typeExprPlan? =
                  some tailPlans := by
                change arguments.tail.mapM typeExprPlan? =
                  some tailPlans at tailEq
                exact tailEq
              have nonemptyPlansEq :
                  nonemptyTypeExprPlans? arguments =
                    some (headPlan :: tailPlans) := by
                rw [nonemptyTypeExprPlans_eq_mapM, headTypeEq, tailTypeEq]
                rfl
              apply enclosed.candidate_eq
              simp only [sourceLoc, RuleReduction.arguments]
              rw [forallBinderPlan?_bounded_some]
              simp [nonemptyPlansEq, innerPlan, namePlan, classPlan,
                argumentPlan, TokenPlan.concat_cons, TokenPlan.parens,
                TokenPlan.append_assoc]

end Solcore.Surface.Multi
