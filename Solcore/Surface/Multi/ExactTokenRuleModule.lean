import Solcore.Surface.Multi.ExactTokenRuleLayout
import Solcore.Surface.Multi.ExactTokenEvidence

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- The complete-file source reduction preserves the exact concatenation of
its top-level token plans; logical EOF contributes no retained token. -/
theorem RuleReduction.module_tokenPlanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .module)}
    {output : RuleValue .module}
    (reduces : RuleReduction file tokens .module origin finish input output)
    (inputEvidence : TokenPlanEvidence
      (input.tokenPlan? sourceRuleTokenPlanLayout)
      (PhysicalTokens tokens origin finish)) :
    TokenPlanEvidence (ruleTokenPlan? .module output)
      (PhysicalTokens tokens origin finish) := by
  cases reduces with
  | module origin finish items eof originEq finishEq eofValue =>
      simp only [EbnfValue.tokenPlan?_transport,
        EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_star,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValues.tokenPlan?_nil,
        sourceRuleTokenPlanLayout,
        ruleTokenPlan?] at inputEvidence ⊢
      simp [MatchedTerminal.physicalTokenPlan, eofValue,
        TokenPlan.append, TokenPlan.empty, Function.comp_def,
        EbnfValue.tokenPlan?_ruleAtom, ruleTokenPlan?] at inputEvidence
      rw [declarationModulePlan?_eq_mapM]
      change TokenPlanEvidence
        (((items.mapM topItemPlan?).bind fun plans =>
          some (TokenPlan.concat plans)).bind fun headPlan =>
            some { slots := headPlan.slots }) _ at inputEvidence
      change TokenPlanEvidence
        (Option.map TokenPlan.concat (items.mapM topItemPlan?)) _
      cases result : items.mapM topItemPlan? with
      | none => simpa [result] using inputEvidence
      | some plans => simpa [result] using inputEvidence

end Solcore.Surface.Multi
