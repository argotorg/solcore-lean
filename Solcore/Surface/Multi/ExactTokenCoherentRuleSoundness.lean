import Solcore.Surface.Multi.ExactTokenReachability
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

namespace CoherentGrammarRuleTokenPlanSound

/-- An unrestricted source-rule proof applies to the coherent callback after
viewing the complete prefix as the root action input. -/
theorem ofGrammarRule
    {rule : GrammarRuleId}
    (sound : GrammarRuleTokenPlanSound rule) :
    CoherentGrammarRuleTokenPlanSound sourceRuleTokenPlanLayout rule := by
  intro file tokens memo correct final origin finish context priorValues output
    complete owned _sourceExact _coherentPrefix reduces inputEvidence
  apply sound owned reduces
  apply inputEvidence.candidate_eq
  symm
  rw [RootAction.unpack_tokenPlan?]
  simpa only [CanonicalCompleteRootItem] using
    (PrefixValues.tokenPlan?_fullValue sourceRuleTokenPlanLayout
      (CanonicalCompleteRootItem tokens rule origin finish context)
      complete priorValues)

end CoherentGrammarRuleTokenPlanSound

end Solcore.Surface.Multi
