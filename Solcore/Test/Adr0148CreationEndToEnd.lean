import Solcore.ContractRuntime.OneLevelNestedExecution
import Solcore.ContractRuntime.WorldStateDelta
import Solcore.Test.Adr0148CreationEndToEndFixture

/-! Executable checked-program regressions for the ADR-0148 lifecycle. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.ContractRuntime.OneLevelNestedExecution
open Adr0148CreationEndToEndFixture

private def fuel : Nat := 1024

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def storageValue? (world : WorldState) (address : Address)
    (slot : Word) : Option Word :=
  (world.account? address).bind fun account => account.storageValue? slot

private def codeProgramsMatch
    (endpoints : Option CheckedHostCoreProgram ×
      Option CheckedHostCoreProgram)
    (before after : Option Program) : Bool :=
  endpoints.1.map CheckedHostCoreProgram.program == before &&
    endpoints.2.map CheckedHostCoreProgram.program == after

private def terminal?
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld root rootInvocation) :
    Option (TerminalResult initialWorld root rootInvocation) :=
  match result.view with
  | .completed terminal => some terminal
  | .outOfFuel _ _ _ => none

private def run
    (root : CheckedCoreContract) (environment : ExecutionEnvironment) :=
  runWithEnvironment root invocation (rootInstalled root) environment fuel

private def committedCreation := run commitRoot environment

private def committedCreationChecks : Bool :=
  match terminal? committedCreation with
  | none => false
  | some terminal =>
      let world := terminal.finalWorld
      let delta := terminal.committedDelta
      terminal.outcome ==
          .returned (encodeWordBytesBE (addressToWord created)) &&
        (delta.accountEndpoints creator).1.isSome &&
        (delta.accountEndpoints creator).2.isSome &&
        world.nonce? creator == some ⟨8, by decide⟩ &&
        world.balance? creator == some ⟨8, by decide⟩ &&
        world.balance? created == some creationValue &&
        (world.code? created).map CheckedHostCoreProgram.program ==
          some runtime.code.program &&
        storageValue? world created callerSlot ==
          some (addressToWord creator) &&
        storageValue? world created valueSlot == some creationValue &&
        storageValue? world created inputWordSlot == some initializerInput &&
        storageValue? world created inputSizeSlot == some ⟨32, by decide⟩ &&
        storageValue? world created storageAddressSlot ==
          some (addressToWord created) &&
        storageValue? world created currentAddressSlot ==
          some (addressToWord created) &&
        storageValue? world created codeAddressSlot ==
          some (addressToWord created) &&
        delta.nonceEndpoints creator ==
          (some oldNonce, some ⟨8, by decide⟩) &&
        delta.balanceEndpoints creator ==
          (some creatorBalance, some ⟨8, by decide⟩) &&
        delta.storageEndpoints creator callerSlot ==
          (some Word.zero, some Word.zero) &&
        codeProgramsMatch (delta.codeEndpoints creator)
          (some commitRoot.code.program) (some commitRoot.code.program) &&
        !delta.createdAccount? creator &&
        !(delta.accountEndpoints created).1.isSome &&
        (delta.accountEndpoints created).2.isSome &&
        delta.createdAccount? created &&
        delta.nonceEndpoints created == (none, some Word.zero) &&
        delta.balanceEndpoints created == (none, some creationValue) &&
        delta.storageEndpoints created callerSlot ==
          (none, some (addressToWord creator)) &&
        codeProgramsMatch (delta.codeEndpoints created)
          none (some runtime.code.program) &&
        (delta.accountEndpoints unrelated).1.isSome &&
        (delta.accountEndpoints unrelated).2.isSome &&
        !delta.createdAccount? unrelated &&
        delta.nonceEndpoints unrelated ==
          (some Word.zero, some Word.zero) &&
        delta.balanceEndpoints unrelated ==
          (some unrelatedBalance, some unrelatedBalance) &&
        codeProgramsMatch (delta.codeEndpoints unrelated) none none &&
        delta.storageEndpoints unrelated callerSlot ==
          (some Word.zero, some Word.zero)

/-- A root that commits the initializer's failure result instead of propagating it. -/
private def catchCreationProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .caseE creationExpr
      (returned (.var 0))
      (.caseE (.var 0)
        (returned (.var 0))
        (.caseE (.var 0)
          (returned (.var 0))
          (returned (.var 0))))
}

private theorem catchCreationProgram_checked :
    catchCreationProgram.checkHost = true := by native_decide

private def catchCreationRoot : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨catchCreationProgram, catchCreationProgram_checked⟩ rfl

private def failureRun (environment : ExecutionEnvironment) :=
  run catchCreationRoot environment

private def initializerFailureChecks
    (environment : ExecutionEnvironment) : Bool :=
  match terminal? (failureRun environment) with
  | none => false
  | some terminal =>
      let world := terminal.finalWorld
      let delta := terminal.committedDelta
      world.nonce? creator == some ⟨8, by decide⟩ &&
        world.balance? creator == some creatorBalance &&
        (world.account? created).isNone &&
        storageValue? world created callerSlot == none &&
        delta.nonceEndpoints creator ==
          (some oldNonce, some ⟨8, by decide⟩) &&
        delta.balanceChange? creator == none &&
        !delta.createdAccount? created &&
        delta.balanceChange? created == none &&
        delta.storageEndpoints created callerSlot == (none, none) &&
        delta.balanceChange? unrelated == none

private def initializerRevertChecks : Bool :=
  initializerFailureChecks revertingInitializerEnvironment

private def initializerTrapChecks : Bool :=
  initializerFailureChecks trappingInitializerEnvironment

private def rootRollbackChecks
    (root : CheckedCoreContract) (expected : FrameOutcome Word) : Bool :=
  match terminal? (run root environment) with
  | none => false
  | some terminal =>
      let world := terminal.finalWorld
      terminal.outcome == expected &&
        world.nonce? creator == some oldNonce &&
        world.balance? creator == some creatorBalance &&
        world.balance? unrelated == some unrelatedBalance &&
        (world.account? created).isNone &&
        terminal.committedDelta.nonceChange? creator == none &&
        terminal.committedDelta.balanceChange? creator == none &&
        !terminal.committedDelta.createdAccount? created

private def rootRevertChecks : Bool :=
  rootRollbackChecks revertRoot
    (.reverted (encodeWordBytesBE rootRevertReason))

private def rootTrapChecks : Bool :=
  rootRollbackChecks trapRoot (.trapped rootTrapReason)

private def sameRootCallChecks : Bool :=
  match terminal? (run sameRootCallRoot environment) with
  | none => false
  | some terminal =>
      let world := terminal.finalWorld
      terminal.outcome == .returned (encodeWordBytesBE runtimeSentinel) &&
        storageValue? world created runtimeSlot == some runtimeSentinel &&
        storageValue? world created callerSlot == some (addressToWord creator) &&
        (world.code? created).map CheckedHostCoreProgram.program ==
          some runtime.code.program &&
        terminal.committedDelta.storageEndpoints created runtimeSlot ==
          (none, some runtimeSentinel) &&
        terminal.committedDelta.createdAccount? created

private def allCreationChecks : Bool :=
  committedCreationChecks && initializerRevertChecks &&
    initializerTrapChecks && rootRevertChecks && rootTrapChecks &&
    sameRootCallChecks

private theorem compileTimeCreationChecks : allCreationChecks = true := by
  native_decide

def testAdr0148CreationEndToEnd : IO Unit := do
  assertTrue committedCreationChecks
    "initializer return did not commit observations, value, nonce, or runtime"
  assertTrue initializerRevertChecks
    "initializer revert did not refund value while retaining creator nonce"
  assertTrue initializerTrapChecks
    "initializer trap did not refund value while retaining creator nonce"
  assertTrue rootRevertChecks
    "root revert did not roll the successful creation back globally"
  assertTrue rootTrapChecks
    "root trap did not roll the successful creation back globally"
  assertTrue sameRootCallChecks
    "same-root call did not resolve and execute the deployed runtime"

end Tests
