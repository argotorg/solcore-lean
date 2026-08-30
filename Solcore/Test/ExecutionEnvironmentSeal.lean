import Solcore.Semantics.ExecutionEnvironmentProperties
import Solcore.Semantics.OneLevelNestedExecutionResumptionProperties
import Solcore.Test.Adr0148CreationEndToEndFixture
import Solcore.Test.OneLevelNestedExecutionFixture

/-! External regressions for the immutable nested-execution environment seal. -/

set_option autoImplicit false

namespace Tests.ExecutionEnvironmentSeal

open Solcore.Core
open Solcore.Semantics
open Tests.OneLevelNestedExecutionFixture

private def root : CheckedCoreContract :=
  rootContract .commit childTargetWord

private def child : CheckedCoreContract :=
  childReturnContract

private def callRegistry : CheckedContractRegistry :=
  registry root child

private def templateId : Word := ⟨0xc1, by decide⟩

private def creationTemplate : CheckedCreationTemplate := {
  initializer := child
  runtime := child
}

private def creationTemplates : CheckedCreationTemplateRegistry := {
  lookup := fun identifier =>
    if identifier = templateId then some creationTemplate else none
}

private def createdAddress : Address := ⟨0xc2, by decide⟩

private def addressPolicy : CreationAddressPolicy := {
  derive := fun _creator _nonce => createdAddress
}

private def environment : ExecutionEnvironment := {
  callRegistry := callRegistry
  creationTemplates := creationTemplates
  creationAddressPolicy := addressPolicy
}

private def runWith (fuel : Nat) :
    OneLevelNestedExecution.Result (initialWorld root child) root invocation :=
  OneLevelNestedExecution.runWithEnvironment root invocation
    (installedRoot root child) environment fuel

private def runCallsOnly (fuel : Nat) :
    OneLevelNestedExecution.Result (initialWorld root child) root invocation :=
  OneLevelNestedExecution.run root invocation (installedRoot root child)
    callRegistry fuel

/-- The old public API is exactly the calls-only environment specialization. -/
example (fuel : Nat) :
    runCallsOnly fuel =
      OneLevelNestedExecution.runWithEnvironment root invocation
        (installedRoot root child) (.callsOnly callRegistry) fuel :=
  rfl

/-- OOF exposes the full retained environment, including creation capabilities. -/
private def outOfFuelRetainsFullEnvironment : Bool :=
  match (runWith 0).view with
  | .outOfFuel retained _mode _reachable =>
      (retained.creationTemplates.lookup templateId).isSome &&
        (retained.creationAddressPolicy.derive rootAddress Word.zero ==
          createdAddress) &&
        (retained.callRegistry.resolve?
          (initialWorld root child) childAddress).isSome
  | .completed _ => false

private theorem outOfFuelRetainsFullEnvironment_exact :
    outOfFuelRetainsFullEnvironment = true := by
  native_decide

/-- Resumption has no environment input and equals one run under the retained one. -/
example (additional : Nat) :
    OneLevelNestedExecution.resumeWithFuel (runWith 0) additional =
      runWith additional := by
  simpa [runWith] using
    OneLevelNestedExecution.resumeWithFuel_runWithEnvironment
      root invocation (installedRoot root child) environment 0 additional

private def resumedAndOneShotCompleteIdentically : Bool :=
  let resumed := OneLevelNestedExecution.resumeWithFuel (runWith 0) 512
  let oneShot := runWith 512
  match resumed.view, oneShot.view with
  | .completed left, .completed right =>
      left.outcome == right.outcome &&
        childStorageValue? left.finalWorld == childStorageValue? right.finalWorld
  | _, _ => false

private theorem resumedAndOneShotCompleteIdentically_exact :
    resumedAndOneShotCompleteIdentically = true := by
  native_decide

/-- Calls-only deliberately rejects the ADR-0148 root creation capability. -/
private def callsOnlyCreationIsUnavailable : Bool :=
  let creationRoot :=
    Tests.Adr0148CreationEndToEndFixture.commitRoot
  let result := OneLevelNestedExecution.run creationRoot
    Tests.Adr0148CreationEndToEndFixture.invocation
    Tests.Adr0148CreationEndToEndFixture.commitInstalled
    Tests.Adr0148CreationEndToEndFixture.environment.callRegistry 512
  match result.view with
  | .outOfFuel _ _ _ => false
  | .completed terminal =>
      terminal.outcome ==
        .trapped ContractCallFailure.unavailable.code &&
      terminal.finalWorld.nonce?
          Tests.Adr0148CreationEndToEndFixture.creator ==
        some Tests.Adr0148CreationEndToEndFixture.oldNonce &&
      (terminal.finalWorld.account?
        Tests.Adr0148CreationEndToEndFixture.created).isNone

private theorem callsOnlyCreationIsUnavailable_exact :
    callsOnlyCreationIsUnavailable = true := by
  native_decide

def runExecutionEnvironmentSealTests : IO Unit := do
  unless outOfFuelRetainsFullEnvironment do
    throw (IO.userError "OOF did not retain the full execution environment")
  unless resumedAndOneShotCompleteIdentically do
    throw (IO.userError "retained-environment resumption differed from one-shot")
  unless callsOnlyCreationIsUnavailable do
    throw (IO.userError "calls-only creation did not return unavailable")

end Tests.ExecutionEnvironmentSeal
