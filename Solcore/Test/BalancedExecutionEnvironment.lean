import Solcore.Test.Adr0147BalancedTopLevelExecutionFixture

/-! Actual fixed-environment regressions at the balanced top-level boundary. -/

set_option autoImplicit false

namespace Tests.BalancedExecutionEnvironment

open Solcore.Core
open Solcore.ContractRuntime
open Tests.Adr0147BalancedTopLevelExecutionFixture
open Tests.TopLevelExecutionFixture

private def templateId : Word := ⟨0xd1, by decide⟩
private def createdAddress : Address := ⟨0xd2, by decide⟩

private def environment : ExecutionEnvironment := {
  callRegistry := emptyRegistry
  creationTemplates := {
    lookup := fun identifier =>
      if identifier = templateId then
        some { initializer := returningContract, runtime := returningContract }
      else none
  }
  creationAddressPolicy := {
    derive := fun _creator _nonce => createdAddress
  }
}

private def invocation : TopLevelInvocation :=
  invocationFrom callerAddress one

private def runWith (fuel : Nat) :=
  BalancedTopLevelExecution.runWithEnvironment returningContract invocation
    (installedWithBalances returningContract ten three) environment fuel

private def exhaustedRetainsEnvironmentAndOneTransfer : Bool :=
  match (runWith 0).view with
  | .rejected _ => false
  | .execution execution =>
      match execution.view with
      | .completed _ => false
      | .outOfFuel retained (.root frame) _ =>
          (retained.creationTemplates.lookup templateId).isSome &&
            retained.creationAddressPolicy.derive callerAddress Word.zero ==
              createdAddress &&
            frame.context.context.values.working.1.balance? callerAddress ==
              some nine &&
            frame.context.context.values.working.1.balance? targetAddress ==
              some four
      | .outOfFuel _ (.child _) _ => false
      | .outOfFuel _ (.initializer _) _ => false

private def terminalBalances
    (result : BalancedTopLevelExecution.Result
      (worldWithBalances returningContract ten three)
      returningContract invocation) : Option (Option Word × Option Word) :=
  result.finalWorld?.map fun world =>
    (world.balance? callerAddress, world.balance? targetAddress)

private def resumedUsesRetainedEnvironmentWithoutRepeatingTransfer : Bool :=
  let resumed := BalancedTopLevelExecution.resumeWithFuel (runWith 0) completionFuel
  let oneShot := runWith completionFuel
  terminalBalances resumed == terminalBalances oneShot &&
    terminalBalances resumed == some (some nine, some four)

private theorem exhaustedRetainsEnvironmentAndOneTransfer_exact :
    exhaustedRetainsEnvironmentAndOneTransfer = true := by
  native_decide

private theorem resumedUsesRetainedEnvironmentWithoutRepeatingTransfer_exact :
    resumedUsesRetainedEnvironmentWithoutRepeatingTransfer = true := by
  native_decide

example (additional : Nat) :
    BalancedTopLevelExecution.resumeWithFuel (runWith 0) additional =
      runWith additional := by
  simpa [runWith] using
    BalancedTopLevelExecution.resumeWithFuel_runWithEnvironment
      returningContract invocation
      (installedWithBalances returningContract ten three)
      environment 0 additional

def runBalancedExecutionEnvironmentTests : IO Unit := do
  unless exhaustedRetainsEnvironmentAndOneTransfer do
    throw (IO.userError "balanced OOF lost its environment or repeated transfer")
  unless resumedUsesRetainedEnvironmentWithoutRepeatingTransfer do
    throw (IO.userError "balanced retained-environment resume differed from one-shot")

end Tests.BalancedExecutionEnvironment
