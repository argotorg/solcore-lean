import Solcore.Surface.Multi.ExactTokenAnchoring
import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

private theorem optionalForallBinderPlans_eq_mapM
    (values : List (OptionalCommaValue × ForallBinder)) :
    List.mapM (fun value =>
        (forallBinderPlan? value.snd).bind fun plan =>
          some ((TokenPlan.optional (.symbol .comma)).append plan)) values =
      ((values.map Prod.snd).mapM forallBinderPlan?).map
        (List.map fun plan =>
          (TokenPlan.optional (.symbol .comma)).append plan) := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.mapM_cons, List.map_cons, Option.bind_eq_bind,
        List.map_cons]
      cases headEq : forallBinderPlan? head.snd with
      | none => simp
      | some headPlan =>
          cases tailEq : List.mapM forallBinderPlan? (tail.map Prod.snd) with
          | none => simp [tailEq, induction]
          | some tailPlans => simp [tailEq, induction]

/-- Forall-clause reductions retain every binder token and permit precisely
the optional commas erased by the syntax tree. -/
theorem forallClause_tokenPlanSound :
    GrammarRuleTokenPlanSound .forallClause := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  cases reduces with
  | forallClause origin finish forallKw first rest dot witness =>
      change TokenPlanEvidence
        (forallClausePlan? (sourceLoc witness ({
          binders := {
            head := first
            tail := rest.map Prod.snd
          }
        } : ForallClausePayload)))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfValue.tokenPlan?_transport,
        EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValue.tokenPlan?_star,
        EbnfValues.tokenPlan?_nil,
        sourceRuleTokenPlanLayout] at inputEvidence
      simp only [ruleTokenPlan?] at inputEvidence
      simp [Function.comp_def, EbnfValue.tokenPlan?_group,
        EbnfValue.tokenPlan?_sequence,
        EbnfValue.tokenPlan?_ruleAtom, ruleTokenPlan?] at inputEvidence
      rw [optionalForallBinderPlans_eq_mapM] at inputEvidence
      cases firstEq : forallBinderPlan? first with
      | none =>
          simp [firstEq, TokenPlanEvidence] at inputEvidence
      | some firstPlan =>
          cases restEq : List.mapM forallBinderPlan?
              (rest.map Prod.snd) with
          | none =>
              simp [firstEq, restEq, TokenPlanEvidence] at inputEvidence
          | some restPlans =>
              simp only [firstEq, restEq, Option.map_some,
                Option.bind_some] at inputEvidence
              rcases inputEvidence with ⟨sourcePlan, sourceEq, relation⟩
              simp only [Option.some.injEq] at sourceEq
              subst sourcePlan
              let tailPlan := TokenPlan.concat <|
                restPlans.map fun plan =>
                  (TokenPlan.optional (.symbol .comma)).append plan
              let innerPlan := TokenPlan.concat [
                TokenPlan.plain (.hardKeyword .forallKw),
                firstPlan,
                tailPlan,
                TokenPlan.plain (.symbol .dot)]
              have firstPlainRelation : TokenSlot.ListMatches
                  ((TokenPlan.plain (.hardKeyword .forallKw)).append
                    (firstPlan.append
                      (tailPlan.append
                        (TokenPlan.exact (.symbol .dot) dot.span)))).slots
                  (PhysicalTokens tokens origin finish) := by
                apply TokenSlot.ListMatches.exactBetweenToPlain
                  (left := TokenPlan.empty)
                  (right := firstPlan.append
                    (tailPlan.append
                      (TokenPlan.exact (.symbol .dot) dot.span)))
                simpa [tailPlan] using relation
              have innerRelation : TokenSlot.ListMatches innerPlan.slots
                  (PhysicalTokens tokens origin finish) := by
                have dotPlainRelation :=
                  TokenSlot.ListMatches.exactBetweenToPlain
                    (left := (TokenPlan.plain
                      (.hardKeyword .forallKw)).append
                        (firstPlan.append tailPlan))
                    (right := TokenPlan.empty)
                    (kind := .symbol .dot)
                    (span := dot.span)
                    (by
                      simpa [TokenPlan.append_assoc] using
                        firstPlainRelation)
                simpa [innerPlan, TokenPlan.concat, TokenPlan.append,
                  TokenPlan.empty,
                  List.append_assoc] using dotPlainRelation
              have innerAnchored : innerPlan.WellAnchored := by
                simpa [innerPlan] using
                  TokenPlan.WellAnchored.concatPlainBookended
                    (.hardKeyword .forallKw) (.symbol .dot)
                    [firstPlan, tailPlan]
              have enclosed := TokenPlanEvidence.enclose
                (TokenPlanEvidence.some innerRelation)
                (fun plan success => by
                  simp only [Option.some.injEq] at success
                  subst plan
                  exact innerAnchored)
                witness.consumed
              apply enclosed.candidate_eq
              rw [forallClausePlan?_eq_mapM]
              simp [firstEq, restEq, sourceLoc, forallClausePlanWith,
                innerPlan, tailPlan]

end Solcore.Surface.Multi
