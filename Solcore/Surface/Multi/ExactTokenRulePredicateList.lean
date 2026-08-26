import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- The predicate list1 reduction and the public predicate-list visitor use
the same comma-separated sequence of child plans. -/
theorem predicateList_tokenPlanSound :
    GrammarRuleTokenPlanSound .predicateList := by
  intro file tokens origin finish input output reduces inputEvidence
  cases reduces with
  | predicateList origin finish predicates =>
      simp only [EbnfValue.tokenPlan?_transport,
        EbnfValue.tokenPlan?_list1,
        sourceRuleTokenPlanLayout,
        ruleTokenPlan?] at inputEvidence ⊢
      rw [predicateListPlan?_eq_mapM]
      simp [NonemptyList.map, Function.comp_def,
        EbnfValue.tokenPlan?_ruleAtom, ruleTokenPlan?] at inputEvidence
      change TokenPlanEvidence
        ((predicatePlan? output.head).bind fun headPlan =>
          (output.tail.mapM predicatePlan?).bind fun tailPlans =>
            some (headPlan.append (TokenPlan.commaTail tailPlans))) _
      change TokenPlanEvidence
        ((predicatePlan? output.head).bind fun headPlan =>
          (output.tail.mapM predicatePlan?).bind fun tailPlans =>
            some (headPlan.append (TokenPlan.commaTail tailPlans))) _ at inputEvidence
      exact inputEvidence

end Solcore.Surface.Multi
