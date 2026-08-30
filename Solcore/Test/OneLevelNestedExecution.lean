import Solcore.Test.OneLevelNestedExecutionFixture

/-! Runtime regressions for the one-level shared-fuel nested executor. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics
open OneLevelNestedExecutionFixture

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def completionFuel : Nat := 512

private def rootCommitContract : CheckedCoreContract :=
  rootContract .commit childTargetWord

private def rootRevertContract : CheckedCoreContract :=
  rootContract .revert childTargetWord

private def rootTrapContract : CheckedCoreContract :=
  rootContract .trap childTargetWord

private def invalidAddressRoot : CheckedCoreContract :=
  rootContract .commit invalidTargetWord

private def unavailableRoot : CheckedCoreContract :=
  rootContract .commit unavailableTargetWord

private def childValueAtWorking
    {initialWorld : WorldState}
    {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (terminal :
      OneLevelNestedExecution.TerminalResult initialWorld root invocation) :
    Option Word :=
  childStorageValue? terminal.terminalContext.context.values.working.1

private def terminalMatches
    {initialWorld : WorldState}
    {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : OneLevelNestedExecution.Result initialWorld root invocation)
    (expectedOutcome : FrameOutcome Word)
    (expectedWorkingChild expectedFinalChild : Option Word) : Bool :=
  match result with
  | .completed terminal =>
      terminal.outcome == expectedOutcome &&
        childValueAtWorking terminal == expectedWorkingChild &&
        childStorageValue? terminal.finalWorld == expectedFinalChild &&
        rootStorageValue?
          terminal.terminalContext.context.values.working.1 == none &&
        rootStorageValue? terminal.finalWorld == none
  | .outOfFuel _ _ _ => false

private def childReturnCommits : Bool :=
  terminalMatches
    (runScenario rootCommitContract childReturnContract completionFuel)
    (.returned (encodeWordBytesBE childPayload))
    (some childNewValue) (some childNewValue)

private def childRevertRollsBack : Bool :=
  terminalMatches
    (runScenario rootCommitContract childRevertContract completionFuel)
    (.reverted (encodeWordBytesBE childRevertPayload))
    (some childOldValue) (some childOldValue)

private def childTrapRollsBack : Bool :=
  terminalMatches
    (runScenario rootCommitContract childTrapContract completionFuel)
    (.trapped childTrapReason)
    (some childOldValue) (some childOldValue)

private def rootRevertRollsBackSuccessfulChild : Bool :=
  terminalMatches
    (runScenario rootRevertContract childReturnContract completionFuel)
    (.reverted (encodeWordBytesBE rootRevertPayload))
    (some childNewValue) (some childOldValue)

private def rootTrapRollsBackSuccessfulChild : Bool :=
  terminalMatches
    (runScenario rootTrapContract childReturnContract completionFuel)
    (.trapped rootTrapReason)
    (some childNewValue) (some childOldValue)

private def invalidAddressIsTotalFailure : Bool :=
  terminalMatches
    (runScenario invalidAddressRoot childReturnContract completionFuel)
    (.trapped ContractCallFailure.invalidAddress.code)
    (some childOldValue) (some childOldValue)

private def unavailableIsTotalFailure : Bool :=
  terminalMatches
    (runScenario unavailableRoot childReturnContract completionFuel)
    (.trapped ContractCallFailure.unavailable.code)
    (some childOldValue) (some childOldValue)

private def depthExceededIsTypedLeafResponse : Bool :=
  terminalMatches
    (runScenario rootCommitContract childDepthContract completionFuel)
    (.returned (encodeWordBytesBE ContractCallFailure.depthExceeded.code))
    (some childNewValue) (some childNewValue)

private def initialRegistryResolvesChild : Bool :=
  ((registry rootCommitContract childReturnContract).resolve?
    (initialWorld rootCommitContract childReturnContract)
    childAddress).isSome

private def rootOutOfFuelVisible : Bool :=
  match runScenario rootCommitContract childReturnContract 0 with
  | .outOfFuel _ (.root _) _ => true
  | _ => false

private def childOutOfFuelAt (fuel : Nat) : Bool :=
  match runScenario rootCommitContract childReturnContract fuel with
  | .outOfFuel _ (.child _) _ => true
  | _ => false

private def childOutOfFuelVisible : Bool :=
  (List.range 128).any childOutOfFuelAt

private theorem compileTimeChildReturnCommit :
    childReturnCommits = true := by
  native_decide

private theorem compileTimeChildRevertRollback :
    childRevertRollsBack = true := by
  native_decide

private theorem compileTimeChildTrapRollback :
    childTrapRollsBack = true := by
  native_decide

private theorem compileTimeRootRevertRollback :
    rootRevertRollsBackSuccessfulChild = true := by
  native_decide

private theorem compileTimeRootTrapRollback :
    rootTrapRollsBackSuccessfulChild = true := by
  native_decide

private theorem compileTimeInvalidAddress :
    invalidAddressIsTotalFailure = true := by
  native_decide

private theorem compileTimeUnavailable :
    unavailableIsTotalFailure = true := by
  native_decide

private theorem compileTimeDepthExceeded :
    depthExceededIsTypedLeafResponse = true := by
  native_decide

private theorem compileTimeRegistryResolution :
    initialRegistryResolvesChild = true := by
  native_decide

private theorem compileTimeRootOutOfFuelMode :
    rootOutOfFuelVisible = true := by
  native_decide

private theorem compileTimeChildOutOfFuelMode :
    childOutOfFuelVisible = true := by
  native_decide

/-- Execute every checked-contract nested-call scenario at runtime. -/
def testOneLevelNestedExecution : IO Unit := do
  assertTrue initialRegistryResolvesChild
    "the installed child did not resolve through the dynamic registry"
  assertTrue childReturnCommits
    "cross-account child return did not commit its storage write"
  assertTrue childRevertRollsBack
    "child revert did not restore the call checkpoint"
  assertTrue childTrapRollsBack
    "child trap did not restore the call checkpoint"
  assertTrue rootRevertRollsBackSuccessfulChild
    "root revert did not undo a previously successful child write"
  assertTrue rootTrapRollsBackSuccessfulChild
    "root trap did not undo a previously successful child write"
  assertTrue invalidAddressIsTotalFailure
    "invalid call address did not become the typed failure response"
  assertTrue unavailableIsTotalFailure
    "unavailable checked contract did not become the typed failure response"
  assertTrue depthExceededIsTypedLeafResponse
    "grandchild call did not receive the typed depth-exceeded response"
  assertTrue rootOutOfFuelVisible
    "zero shared fuel did not retain the active root mode"
  assertTrue childOutOfFuelVisible
    "shared fuel never exposed a retained active child mode"

end Tests
