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

/--
Pair an original transaction checkpoint with a separately prepared working
world. This is the root context shape used after a successful call-value
transfer: execution sees the transferred world, while rollback retains the
exact caller-supplied world.
-/
def preparedValues
    (checkpointWorld workingWorld : WorldState) :
    FrameCheckpointedWorkingPair Unit Unit :=
  let checkpoint :=
    FrameCheckpointSnapshot.fromWorkingPair
      (checkpointWorld, initialEffects)
  ⟨checkpoint, (workingWorld, initialEffects)⟩

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

/-- Build a root context with distinct checkpoint and working worlds. -/
def preparedContext
    {checkpointWorld workingWorld : WorldState}
    {target : Address}
    {contract : CheckedCoreContract}
    (installed :
      InstalledCheckedCoreContract workingWorld target contract) :
    HostStorageDriver.Context Unit Unit := {
  context := {
    storageAddress := target
    values := preparedValues checkpointWorld workingWorld
  }
  storageAccount := installed.account
  storageAccount_present := installed.account_present
}

end TopLevelExecution

end Solcore.Semantics
