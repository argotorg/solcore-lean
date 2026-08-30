import Solcore.Semantics.OneLevelNestedCreationCompletion
import Solcore.Semantics.OneLevelNestedExecutionTransitions
import Solcore.Semantics.BalanceTransferInstallationProperties

/-! Reachability seal for scheduler states produced by checked execution. -/

set_option autoImplicit false

namespace Solcore.Semantics.OneLevelNestedExecution

/--
Evidence that an active scheduler mode was obtained from an installed root by
only the transitions of the one-level executor under one fixed environment.

This seal prevents low-level frame constructors and transition helpers from
being used to manufacture a resumable state with an unrelated working world.
-/
inductive Reachable
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (environment : ExecutionEnvironment) :
    Mode initialWorld rootContract rootInvocation → Prop where
  | initial
      (installed :
        InstalledCheckedCoreContract initialWorld rootInvocation.target
          rootContract) :
      Reachable environment
        (Mode.initialRoot rootContract rootInvocation installed)
  | balancedInitial
      {workingWorld : WorldState}
      (installed :
        InstalledCheckedCoreContract initialWorld rootInvocation.target
          rootContract)
      (transferred :
        initialWorld.transferBalance rootInvocation.caller
            rootInvocation.target rootInvocation.callValue =
          .ok workingWorld) :
      Reachable environment
        (Mode.preparedRoot rootContract rootInvocation
          (WorldState.transferBalance_preserves_installed transferred
            installed))
  | rootNext
      {frame : RootFrame initialWorld rootContract rootInvocation}
      {next : Core.State}
      (prior : Reachable environment (.root frame))
      (advanced : Core.hostAdvance frame.state = .next next) :
      Reachable environment (.root (frame.afterNext next advanced))
  | rootSuspended
      {frame : RootFrame initialWorld rootContract rootInvocation}
      {suspension : Core.HostSuspension}
      (prior : Reachable environment (.root frame))
      (creatorAddress_eq : rootInvocation.executionInputs.currentAddress =
        frame.context.context.storageAddress)
      (advanced : Core.hostAdvance frame.state = .suspended suspension) :
      Reachable environment
        (frame.afterSuspensionWithEnvironment environment creatorAddress_eq
          suspension advanced)
  | childDone
      {frame : ChildFrame initialWorld rootContract rootInvocation}
      {value : Core.Value}
      (prior : Reachable environment (.child frame))
      (advanced : Core.hostAdvance frame.childState = .done value) :
      Reachable environment
        (.root (frame.resumeRoot (frame.outcomeDone value advanced)))
  | childNext
      {frame : ChildFrame initialWorld rootContract rootInvocation}
      {next : Core.State}
      (prior : Reachable environment (.child frame))
      (advanced : Core.hostAdvance frame.childState = .next next) :
      Reachable environment (.child (frame.afterNext next advanced))
  | childSuspended
      {frame : ChildFrame initialWorld rootContract rootInvocation}
      {suspension : Core.HostSuspension}
      (prior : Reachable environment (.child frame))
      (advanced : Core.hostAdvance frame.childState = .suspended suspension) :
      Reachable environment
        (.child (frame.afterHandledSuspension suspension advanced))
  | initializerDone
      {frame : PreparedInitializerFrame initialWorld rootContract rootInvocation}
      {value : Core.Value}
      (prior : Reachable environment (.initializer frame))
      (advanced : Core.hostAdvance frame.initializerState = .done value) :
      Reachable environment
        (.root
          ((frame.complete (frame.outcomeDone value advanced)).root))
  | initializerNext
      {frame : PreparedInitializerFrame initialWorld rootContract rootInvocation}
      {next : Core.State}
      (prior : Reachable environment (.initializer frame))
      (advanced : Core.hostAdvance frame.initializerState = .next next) :
      Reachable environment (.initializer (frame.afterNext next advanced))
  | initializerSuspended
      {frame : PreparedInitializerFrame initialWorld rootContract rootInvocation}
      {suspension : Core.HostSuspension}
      (prior : Reachable environment (.initializer frame))
      (advanced :
        Core.hostAdvance frame.initializerState = .suspended suspension) :
      Reachable environment
        (.initializer (frame.afterHandledSuspension suspension advanced))

end Solcore.Semantics.OneLevelNestedExecution
