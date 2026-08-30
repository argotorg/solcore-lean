import Solcore.Semantics.HostStorageContextRebase

/-! Compile-only regressions for joint working-world and effect rebasing. -/

set_option autoImplicit false

namespace Tests.HostStorageContextRebaseWithEffects

open Solcore.Semantics

universe u v

private example
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (HostStorageDriver.Context.rebaseWorkingWithEffects
      context world effects account present).context.storageAddress =
      context.context.storageAddress := by
  simp

private example
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (HostStorageDriver.Context.rebaseWorkingWithEffects
      context world effects account present).context.values.checkpoint =
      context.context.values.checkpoint := by
  simp

private example
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (HostStorageDriver.Context.rebaseWorkingWithEffects
      context world effects account present).context.values.working.1 =
      world := by
  simp

private example
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (HostStorageDriver.Context.rebaseWorkingWithEffects
      context world effects account present).context.values.working.2 =
      effects := by
  simp

end Tests.HostStorageContextRebaseWithEffects
