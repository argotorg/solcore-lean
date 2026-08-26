import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRuleSoundness
import Solcore.Surface.Multi.ExactTokenTypeAnchoring

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- Replace one source-exact fixed token inside a larger matched plan by its
grammar-level plain spelling. -/
private theorem TokenSlot.ListMatches.fixedToPlain
    {left right : TokenPlan} {kind : TokenKind} {span : SourceSpan}
    {actual : List Token}
    (relation : TokenSlot.ListMatches
      (left.append ((TokenPlan.exact kind span).append right)).slots actual) :
    TokenSlot.ListMatches
      (left.append ((TokenPlan.plain kind).append right)).slots actual := by
  change TokenSlot.ListMatches
    (left.slots ++
      .required (ExpectedToken.exact kind span) :: right.slots) actual
      at relation
  change TokenSlot.ListMatches
    (left.slots ++
      .required (ExpectedToken.plain kind) :: right.slots) actual
  rcases relation.split_append with
    ⟨leftActual, rightActual, actualEq, leftRelation, rightRelation⟩
  rw [actualEq]
  exact leftRelation.append rightRelation.requiredHeadToPlain

/-- The recursive type-list visitor agrees with the standard monadic
left-to-right traversal. -/
private theorem typeExprPlans_eq_mapM (values : List TypeExpr) :
    typeExprPlans? values = values.mapM typeExprPlan? := by
  induction values with
  | nil => simp [typeExprPlans?]
  | cons head tail induction =>
      simp [typeExprPlans?, List.mapM_cons, typeExprPlan?, induction]

/-- Predicate reductions preserve the main type, class name, and optional
nonempty argument list while weakening only fixed punctuation. -/
theorem predicate_tokenPlanSound :
    GrammarRuleTokenPlanSound .predicate := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  cases reduces with
  | predicateWithoutArguments origin finish main colon className witness =>
      change TokenPlanEvidence
        (predicatePlan? (sourceLoc witness
          ({ main := main
             className := className
             parameters := none } : PredicatePayload)))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfValue.tokenPlan?_transport,
        EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_optional_none,
        EbnfValues.tokenPlan?_nil,
        sourceRuleTokenPlanLayout] at inputEvidence
      simp only [ruleTokenPlan?] at inputEvidence
      cases mainEq : typeAtomPlan? main with
      | none =>
          simp [mainEq, TokenPlanEvidence] at inputEvidence
      | some mainPlan =>
          simp only [mainEq] at inputEvidence
          rcases inputEvidence with ⟨plan, candidateEq, relation⟩
          change some (mainPlan.append
            (colon.physicalTokenPlan.append
              ((qualifiedNamePlan className).append
                (TokenPlan.empty.append TokenPlan.empty)))) =
            some plan at candidateEq
          injection candidateEq with planEq
          rw [← planEq] at relation
          simp only [TokenPlan.append_empty] at relation
          rw [MatchedTerminal.physicalTokenPlan_symbol] at relation
          let classPlan := qualifiedNamePlan className
          let innerPlan := mainPlan.append
            ((TokenPlan.plain (.symbol .colon)).append classPlan)
          have innerRelation : TokenSlot.ListMatches innerPlan.slots
              (PhysicalTokens tokens origin finish) := by
            apply TokenSlot.ListMatches.fixedToPlain
              (left := mainPlan) (right := classPlan) relation
          have innerAnchored : innerPlan.WellAnchored := by
            apply TokenPlan.WellAnchored.append
              (typeAtomPlan?_wellAnchored main mainPlan mainEq)
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
          unfold predicatePlan?
          change (some innerPlan).map (TokenPlan.enclose witness.span) =
            (typeAtomPlan? main).bind fun mainResult =>
              (some TokenPlan.empty).bind fun parametersPlan =>
                some (TokenPlan.enclose witness.span (TokenPlan.concat [
                mainResult,
                TokenPlan.plain (.symbol .colon),
                qualifiedNamePlan className,
                parametersPlan]))
          simp [mainEq, innerPlan, classPlan, TokenPlan.concat_cons]
  | predicateWithArguments origin finish main colon className openParen
      parameters closeParen witness =>
      change TokenPlanEvidence
        (predicatePlan? (sourceLoc witness
          ({ main := main
             className := className
             parameters := some parameters } : PredicatePayload)))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfValue.tokenPlan?_transport,
        EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_optional_some,
        EbnfValue.tokenPlan?_list1,
        EbnfValues.tokenPlan?_nil,
        sourceRuleTokenPlanLayout] at inputEvidence
      simp only [ruleTokenPlan?] at inputEvidence
      simp [NonemptyList.map, Function.comp_def,
        EbnfValue.tokenPlan?_ruleAtom] at inputEvidence
      cases mainEq : typeAtomPlan? main with
      | none =>
          simp [mainEq, TokenPlanEvidence] at inputEvidence
      | some mainPlan =>
          cases headEq : ruleTokenPlan? .type parameters.head with
          | none =>
              simp [mainEq, headEq, TokenPlanEvidence] at inputEvidence
          | some headPlan =>
              cases tailEq : parameters.tail.mapM
                  (ruleTokenPlan? .type) with
              | none =>
                  have tailEq' :
                      List.mapM (fun value =>
                        ruleTokenPlan? .type value)
                        parameters.tail = none := by
                    simpa only using tailEq
                  rw [tailEq'] at inputEvidence
                  simp [mainEq, headEq,
                    TokenPlanEvidence] at inputEvidence
              | some tailPlans =>
                  have tailEq' :
                      List.mapM (fun value =>
                        ruleTokenPlan? .type value)
                        parameters.tail = some tailPlans := by
                    simpa only using tailEq
                  rw [tailEq'] at inputEvidence
                  simp only [mainEq, headEq] at inputEvidence
                  rcases inputEvidence with
                    ⟨plan, candidateEq, relation⟩
                  let parameterPlan := TokenPlan.commaSeparated
                    (headPlan :: tailPlans)
                  have headTypeEq : typeExprPlan? parameters.head =
                      some headPlan := by
                    simpa only [ruleTokenPlan?] using headEq
                  have tailTypeEq : parameters.tail.mapM typeExprPlan? =
                      some tailPlans := by
                    change parameters.tail.mapM typeExprPlan? =
                      some tailPlans at tailEq
                    exact tailEq
                  let classPlan := qualifiedNamePlan className
                  let sourcePlan := mainPlan.append
                    ((TokenPlan.exact (.symbol .colon) colon.span).append
                      (classPlan.append
                        ((TokenPlan.exact (.symbol .leftParen)
                          openParen.span).append
                          (parameterPlan.append
                            (TokenPlan.exact (.symbol .rightParen)
                              closeParen.span)))))
                  change some sourcePlan = some plan at candidateEq
                  injection candidateEq with planEq
                  rw [← planEq] at relation
                  dsimp [sourcePlan] at relation
                  let afterColon := mainPlan.append
                    ((TokenPlan.plain (.symbol .colon)).append
                      (classPlan.append
                        ((TokenPlan.exact (.symbol .leftParen)
                          openParen.span).append
                            (parameterPlan.append
                              (TokenPlan.exact (.symbol .rightParen)
                                closeParen.span)))))
                  have colonRelation : TokenSlot.ListMatches
                      afterColon.slots
                      (PhysicalTokens tokens origin finish) := by
                    apply TokenSlot.ListMatches.fixedToPlain
                      (left := mainPlan)
                      (right := classPlan.append
                        ((TokenPlan.exact (.symbol .leftParen)
                          openParen.span).append
                            (parameterPlan.append
                              (TokenPlan.exact (.symbol .rightParen)
                                closeParen.span))))
                    exact relation
                  let afterOpen := mainPlan.append
                    ((TokenPlan.plain (.symbol .colon)).append
                      (classPlan.append
                        ((TokenPlan.plain (.symbol .leftParen)).append
                          (parameterPlan.append
                            (TokenPlan.exact (.symbol .rightParen)
                              closeParen.span)))))
                  have openRelation : TokenSlot.ListMatches
                      afterOpen.slots
                      (PhysicalTokens tokens origin finish) := by
                    have converted :=
                      TokenSlot.ListMatches.fixedToPlain
                        (left := mainPlan.append
                          ((TokenPlan.plain (.symbol .colon)).append classPlan))
                        (right := parameterPlan.append
                          (TokenPlan.exact (.symbol .rightParen)
                            closeParen.span))
                        (kind := .symbol .leftParen)
                        (span := openParen.span)
                        (by
                          simpa [afterColon, TokenPlan.append_assoc] using
                            colonRelation)
                    simpa [afterOpen, TokenPlan.append_assoc] using converted
                  let innerPlan := mainPlan.append
                    ((TokenPlan.plain (.symbol .colon)).append
                      (classPlan.append
                        ((TokenPlan.plain (.symbol .leftParen)).append
                          (parameterPlan.append
                            (TokenPlan.plain (.symbol .rightParen))))))
                  have innerRelation : TokenSlot.ListMatches innerPlan.slots
                      (PhysicalTokens tokens origin finish) := by
                    have converted :=
                      TokenSlot.ListMatches.fixedToPlain
                        (left := mainPlan.append
                          ((TokenPlan.plain (.symbol .colon)).append
                            (classPlan.append
                              ((TokenPlan.plain (.symbol .leftParen)).append
                                parameterPlan))))
                        (right := TokenPlan.empty)
                        (kind := .symbol .rightParen)
                        (span := closeParen.span)
                        (by
                          simpa [afterOpen, TokenPlan.append_assoc] using
                            openRelation)
                    simpa [innerPlan, TokenPlan.append_assoc] using converted
                  have innerAnchored : innerPlan.WellAnchored := by
                    apply TokenPlan.WellAnchored.append
                      (typeAtomPlan?_wellAnchored main mainPlan mainEq)
                    apply TokenPlan.WellAnchored.append
                      (TokenPlan.WellAnchored.plain (.symbol .colon))
                    apply TokenPlan.WellAnchored.append
                      (qualifiedNamePlan_wellAnchored className)
                    exact TokenPlan.WellAnchored.parens parameterPlan
                  have enclosed := TokenPlanEvidence.enclose
                    (TokenPlanEvidence.some innerRelation)
                    (fun plan success => by
                      simp only [Option.some.injEq] at success
                      subst plan
                      exact innerAnchored)
                    witness.consumed
                  have nonemptyPlansEq :
                      nonemptyTypeExprPlans? parameters =
                        some (headPlan :: tailPlans) := by
                    unfold nonemptyTypeExprPlans?
                    rw [show typeExprPlanAt? false parameters.head =
                        typeExprPlan? parameters.head by rfl,
                      headTypeEq, typeExprPlans_eq_mapM, tailTypeEq]
                    rfl
                  apply enclosed.candidate_eq
                  change (some innerPlan).map
                      (TokenPlan.enclose witness.span) =
                    predicatePlan? ({
                      span := witness.span
                      payload := {
                        main := main
                        className := className
                        parameters := some parameters
                      }
                    } : Predicate)
                  rw [predicatePlan?_parameters_some]
                  simp [mainEq, nonemptyPlansEq, innerPlan, classPlan,
                    parameterPlan, TokenPlan.concat_cons,
                    TokenPlan.parens, TokenPlan.append_assoc]

end Solcore.Surface.Multi
