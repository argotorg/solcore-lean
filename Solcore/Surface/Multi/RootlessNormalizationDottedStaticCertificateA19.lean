import Solcore.Surface.Multi.RootlessNormalizationDottedStaticCertificateA18
import Lean.Elab.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace Solcore.Surface.Multi

open Grammar

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem dottedStaticRankTail_2368_true :
    (allDottedRhs.zipIdx.drop 2368).all
      dottedStaticRankRowAt = true := by
  run_tac
    Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl

end Solcore.Surface.Multi

