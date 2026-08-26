import Solcore.Surface.Multi.ExactTokenEvidence
import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRuleLayout

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- The source rule for the AST-erased optional binder comma preserves exact
complete-consumption evidence in both its absent and present branches. -/
theorem RuleReduction.optionalComma_tokenPlanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .optionalComma)}
    {output : RuleValue .optionalComma}
    (reduces : RuleReduction file tokens .optionalComma
      origin finish input output)
    (inputEvidence : TokenPlanEvidence
      (input.tokenPlan? sourceRuleTokenPlanLayout)
      (PhysicalTokens tokens origin finish)) :
    TokenPlanEvidence
      (ruleTokenPlan? .optionalComma output)
      (PhysicalTokens tokens origin finish) := by
  generalize actualEq : PhysicalTokens tokens origin finish = actual at inputEvidence ⊢
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
        MatchedTerminal.physicalTokenPlan_symbol] at inputEvidence
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
