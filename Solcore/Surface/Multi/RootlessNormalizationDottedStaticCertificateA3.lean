import Solcore.Surface.Multi.RootlessNormalizationDottedStaticCertificateA2
import Lean.Elab.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace Solcore.Surface.Multi

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem dottedStaticRankChunk_0832_true :
    dottedStaticRankChunk 832 96 = true := by
  run_tac
    Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl

end Solcore.Surface.Multi

