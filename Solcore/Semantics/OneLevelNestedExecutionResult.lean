import Solcore.Semantics.CheckedContractRegistry
import Solcore.Semantics.OneLevelNestedExecutionReachability
import Solcore.Semantics.WorldStateDelta

/-! Total bounded results for one-level nested checked-Core execution. -/

set_option autoImplicit false

namespace Solcore.Semantics.OneLevelNestedExecution

/--
A terminal root result with exact speculative and externally committed world
endpoints. The outcome determines which endpoint the executor selects.
-/
structure TerminalResult
    (initialWorld : WorldState)
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation) where
  terminalContext : HostStorageDriver.Context Unit Unit
  coreValue : Core.Value
  coreStore : Core.Store
  outcome : FrameOutcome Core.Word
  finalWorld : WorldState
  workingDelta :
    WorldStateDelta initialWorld
      terminalContext.context.values.working.1
  committedDelta : WorldStateDelta initialWorld finalWorld

/--
One bounded scheduler run either completes the root or retains the exact active
typed machine needed to continue with additional shared fuel.
-/
inductive Result
    (initialWorld : WorldState)
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation) where
  | completed
      (terminal : TerminalResult initialWorld rootContract rootInvocation)
  | outOfFuel
      (registry : CheckedContractRegistry)
      (mode : Mode initialWorld rootContract rootInvocation)
      (reachable : Reachable registry mode)

end Solcore.Semantics.OneLevelNestedExecution
