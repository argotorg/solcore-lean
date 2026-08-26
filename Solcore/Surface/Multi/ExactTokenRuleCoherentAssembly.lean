import Solcore.Surface.Multi.ExactTokenRuleCoverage
import Solcore.Surface.Multi.ExactTokenRuleLetBindingCoherent
import Solcore.Surface.Multi.ExactTokenRuleModuleReferenceSourceExact

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar

/-- Assemble parser-wide exact-token soundness from the three coherent rules
whose source-reachable forms remain intentionally narrower than their raw
grammar-rule relations. -/
theorem rootActionTokenPlanSound_of_matchArm_postfix_body
    (matchArmSound : CoherentGrammarRuleTokenPlanSound
      sourceRuleTokenPlanLayout .matchArm)
    (postfixSound : CoherentGrammarRuleTokenPlanSound
      sourceRuleTokenPlanLayout .postfix)
    (bodySound : CoherentGrammarRuleTokenPlanSound
      sourceRuleTokenPlanLayout .body) :
    RootActionTokenPlanSound sourceRuleTokenPlanLayout :=
  rootActionTokenPlanSound_of_coherentExceptions
    moduleRef_coherentTokenPlanSound
    letBinding_coherentTokenPlanSound
    matchArmSound
    postfixSound
    bodySound

end Solcore.Surface.Multi
