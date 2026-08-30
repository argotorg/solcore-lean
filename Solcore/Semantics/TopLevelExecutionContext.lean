import Solcore.Semantics.CheckedCoreContract
import Solcore.Semantics.FrameCheckpointSnapshot
import Solcore.Semantics.HostStorageContext

/-! Root storage context derived from explicit top-level execution inputs. -/

set_option autoImplicit false

namespace Solcore.Semantics

namespace TopLevelExecution

/-- Root execution currently has no separate rollback payload or event trace. -/
def initialEffects : FrameEffectJournal Unit Unit :=
  ⟨(), ()⟩

/-- Use the same explicit world and empty effects as checkpoint and working data. -/
def initialValues
    (initialWorld : WorldState) :
    FrameCheckpointedWorkingPair Unit Unit :=
  let working := (initialWorld, initialEffects)
  ⟨FrameCheckpointSnapshot.fromWorkingPair working, working⟩

/-- Build the exact root storage context certified by contract installation. -/
def initialContext
    {initialWorld : WorldState}
    {target : Address}
    {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract initialWorld target contract) :
    HostStorageDriver.Context Unit Unit := {
  context := {
    storageAddress := target
    values := initialValues initialWorld
  }
  storageAccount := installed.account
  storageAccount_present := installed.account_present
}

end TopLevelExecution

end Solcore.Semantics
