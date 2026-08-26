import Solcore.Surface.Multi.ExactTokenRuleCoherentAssembly
import Solcore.Surface.Multi.ExactTokenRulePostfixCoherent
import Solcore.Surface.Multi.ExactTokenRuleStatementRegionsCoherent

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar

/-- Every source-reachable completed grammar action preserves the exact
retained-token plan selected by its semantic result. -/
theorem rootActionTokenPlanSound :
    RootActionTokenPlanSound sourceRuleTokenPlanLayout :=
  rootActionTokenPlanSound_of_matchArm_postfix_body
    matchArm_coherentTokenPlanSound
    postfix_coherentTokenPlanSound
    body_coherentTokenPlanSound

end Solcore.Surface.Multi
