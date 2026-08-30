import Solcore.Test.Adr0148NestedCreationLifecycleFixture

/-! External consumers and executable initializer-lifecycle regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics
open Solcore.Semantics.OneLevelNestedExecution
open Adr0148NestedCreationLifecycleFixture
open Adr0148CheckedCreationPreflightFixture

example := @RootFrame.suspendCreation
example := @SuspendedCreationRoot.resumeWith
example := @SuspendedCreationRoot.startInitializer
example := @PreparedInitializerFrame.afterNext
example := @PreparedInitializerFrame.afterHandledSuspension
example := @PreparedInitializerFrame.outcomeDone
example := @PreparedInitializerFrame.completeReturned
example := @PreparedInitializerFrame.complete
example := @DeployedInitializerResult.deployed_code
example := @DeployedInitializerResult.deployed_storage
example := @DeployedInitializerResult.deployed_balance
example := @DeployedInitializerResult.deployed_nonce

private def returnInstallsRuntime : Bool :=
  completionObservation (.returned initializerPayload)

private def revertSelectsPostNonce : Bool :=
  completionObservation (.reverted initializerPayload)

private def trapSelectsPostNonce : Bool :=
  completionObservation (.trapped initializerPayload)

private theorem compileTimeLifecycle :
    returnInstallsRuntime && revertSelectsPostNonce &&
      trapSelectsPostNonce = true := by
  native_decide

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def testAdr0148NestedCreationLifecycle : IO Unit := do
  assertTrue returnInstallsRuntime
    "initializer return did not install runtime or preserve payload state"
  assertTrue revertSelectsPostNonce
    "initializer revert did not select post-nonce world or preserve payload"
  assertTrue trapSelectsPostNonce
    "initializer trap did not select post-nonce world or preserve reason"

end Tests
