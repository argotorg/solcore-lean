import Solcore.Semantics.HostStorageContext

/-! Proof-preserving replacement of one storage context's working world. -/

set_option autoImplicit false

namespace Solcore.Semantics.HostStorageDriver.Context

universe u v

/--
Install a selected working world while retaining the frame checkpoint, effects,
and storage selector. The caller supplies the refreshed selected Account.
-/
def rebaseWorking
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState)
    (storageAccount : Account)
    (storageAccount_present :
      world.account? context.context.storageAddress = some storageAccount) :
    HostStorageDriver.Context RollbackState TraceState := {
  context := {
    storageAddress := context.context.storageAddress
    values := {
      checkpoint := context.context.values.checkpoint
      working := (world, context.context.values.working.2)
    }
  }
  storageAccount := storageAccount
  storageAccount_present := storageAccount_present
}

@[simp] theorem rebaseWorking_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState) (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (context.rebaseWorking world account present).context.storageAddress =
      context.context.storageAddress :=
  rfl

@[simp] theorem rebaseWorking_checkpoint
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState) (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (context.rebaseWorking world account present).context.values.checkpoint =
      context.context.values.checkpoint :=
  rfl

@[simp] theorem rebaseWorking_workingWorld
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState) (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (context.rebaseWorking world account present).context.values.working.1 =
      world :=
  rfl

@[simp] theorem rebaseWorking_workingEffects
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState) (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (context.rebaseWorking world account present).context.values.working.2 =
      context.context.values.working.2 :=
  rfl

/--
Install a selected working world and effect journal while retaining the frame
checkpoint and storage selector. The caller supplies the refreshed selected
Account.
-/
def rebaseWorkingWithEffects
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (storageAccount : Account)
    (storageAccount_present :
      world.account? context.context.storageAddress = some storageAccount) :
    HostStorageDriver.Context RollbackState TraceState := {
  context := {
    storageAddress := context.context.storageAddress
    values := {
      checkpoint := context.context.values.checkpoint
      working := (world, effects)
    }
  }
  storageAccount := storageAccount
  storageAccount_present := storageAccount_present
}

@[simp] theorem rebaseWorkingWithEffects_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (context.rebaseWorkingWithEffects world effects account present).context.storageAddress =
      context.context.storageAddress :=
  rfl

@[simp] theorem rebaseWorkingWithEffects_checkpoint
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (context.rebaseWorkingWithEffects world effects account present).context.values.checkpoint =
      context.context.values.checkpoint :=
  rfl

@[simp] theorem rebaseWorkingWithEffects_workingWorld
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (context.rebaseWorkingWithEffects world effects account present).context.values.working.1 =
      world :=
  rfl

@[simp] theorem rebaseWorkingWithEffects_workingEffects
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (context.rebaseWorkingWithEffects world effects account present).context.values.working.2 =
      effects :=
  rfl

end Solcore.Semantics.HostStorageDriver.Context
