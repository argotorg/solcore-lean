import Solcore.Surface.Multi.ExactTokenAnchoring
import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- Generic-prefix reductions preserve their forall clause and optional
predicate context, weakening only the fixed implication arrow. -/
theorem genericPrefix_tokenPlanSound :
    GrammarRuleTokenPlanSound .genericPrefix := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  cases reduces with
  | genericPrefixBare origin finish forallClause witness =>
      change TokenPlanEvidence
        (genericPrefixPlan? (sourceLoc witness ({
          forallClause := forallClause
          context := none
        } : GenericPrefixPayload)))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfValue.tokenPlan?_transport,
        EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValue.tokenPlan?_optional_none,
        EbnfValues.tokenPlan?_nil,
        sourceRuleTokenPlanLayout] at inputEvidence
      simp only [ruleTokenPlan?] at inputEvidence
      cases forallEq : forallClausePlan? forallClause with
      | none =>
          simp [forallEq, TokenPlanEvidence] at inputEvidence
      | some forallPlan =>
          simp only [forallEq] at inputEvidence
          rcases inputEvidence with ⟨plan, candidateEq, relation⟩
          change some (forallPlan.append
            (TokenPlan.empty.append TokenPlan.empty)) =
              some plan at candidateEq
          injection candidateEq with planEq
          rw [← planEq] at relation
          simp only [TokenPlan.append_empty] at relation
          have enclosed := TokenPlanEvidence.enclose
            (TokenPlanEvidence.some relation)
            (fun plan success => by
              simp only [Option.some.injEq] at success
              subst plan
              exact forallClausePlan?_wellAnchored
                forallClause forallPlan forallEq)
            witness.consumed
          apply enclosed.candidate_eq
          unfold genericPrefixPlan?
          dsimp only [sourceLoc]
          change (some forallPlan).map
              (TokenPlan.enclose witness.span) =
            (forallClausePlan? forallClause).bind fun result =>
              some (TokenPlan.enclose witness.span
                (result.append TokenPlan.empty))
          simp [forallEq]
  | genericPrefixContext origin finish forallClause predicates fatArrow
      witness =>
      change TokenPlanEvidence
        (genericPrefixPlan? (sourceLoc witness ({
          forallClause := forallClause
          context := some predicates
        } : GenericPrefixPayload)))
        (PhysicalTokens tokens origin finish)
      simp only [EbnfValue.tokenPlan?_transport,
        EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValue.tokenPlan?_optional_some,
        EbnfValues.tokenPlan?_nil,
        sourceRuleTokenPlanLayout] at inputEvidence
      simp only [ruleTokenPlan?] at inputEvidence
      cases forallEq : forallClausePlan? forallClause with
      | none =>
          simp [forallEq, TokenPlanEvidence] at inputEvidence
      | some forallPlan =>
          cases predicatesEq : predicateListPlan? predicates with
          | none =>
              simp [forallEq, predicatesEq,
                TokenPlanEvidence] at inputEvidence
          | some predicatesPlan =>
              simp only [forallEq, predicatesEq] at inputEvidence
              rcases inputEvidence with ⟨plan, candidateEq, relation⟩
              change some (forallPlan.append
                ((predicatesPlan.append
                  (fatArrow.physicalTokenPlan.append TokenPlan.empty)).append
                    TokenPlan.empty)) = some plan at candidateEq
              injection candidateEq with planEq
              rw [← planEq] at relation
              simp only [TokenPlan.append_empty] at relation
              rw [MatchedTerminal.physicalTokenPlan_symbol] at relation
              let innerPlan := forallPlan.append
                (predicatesPlan.append
                  (TokenPlan.plain (.symbol .fatArrow)))
              have innerRelation : TokenSlot.ListMatches innerPlan.slots
                  (PhysicalTokens tokens origin finish) := by
                have converted :=
                  TokenSlot.ListMatches.exactBetweenToPlain
                    (left := forallPlan.append predicatesPlan)
                    (right := TokenPlan.empty)
                    (kind := .symbol .fatArrow)
                    (span := fatArrow.span)
                    (by
                      simpa [TokenPlan.append_assoc] using relation)
                simpa [innerPlan, TokenPlan.append_assoc] using converted
              have innerAnchored : innerPlan.WellAnchored := by
                exact TokenPlan.WellAnchored.of_starts_ends_append
                  (forallClausePlan?_startsRequired
                    forallClause forallPlan forallEq)
                  (TokenPlan.WellAnchored.EndsRequired.append_plain_last
                    predicatesPlan (.symbol .fatArrow))
              have enclosed := TokenPlanEvidence.enclose
                (TokenPlanEvidence.some innerRelation)
                (fun plan success => by
                  simp only [Option.some.injEq] at success
                  subst plan
                  exact innerAnchored)
                witness.consumed
              apply enclosed.candidate_eq
              unfold genericPrefixPlan?
              dsimp only [sourceLoc]
              change (some innerPlan).map
                  (TokenPlan.enclose witness.span) =
                (forallClausePlan? forallClause).bind fun forallResult =>
                  (predicateListPlan? predicates).bind
                    fun predicatesResult =>
                      some (TokenPlan.enclose witness.span
                        (forallResult.append
                          (predicatesResult.append
                            (TokenPlan.plain (.symbol .fatArrow)))))
              simp [forallEq, predicatesEq, innerPlan]

end Solcore.Surface.Multi
