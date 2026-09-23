import Solcore.ContractRuntime.WorldStateDelta
import Solcore.Test.Adr0147NestedValueExecutionFixture

/-! Runtime and compile-time regressions for checked nested value calls. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open OneLevelNestedExecution
open OneLevelNestedExecutionFixture
open Adr0147NestedValueExecutionFixture

private def completionFuel : Nat := 768

private def terminalSatisfies
    {initialWorld : WorldState}
    {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : Result initialWorld root invocation)
    (predicate : TerminalResult initialWorld root invocation → Bool) : Bool :=
  match result.view with
  | .completed terminal => predicate terminal
  | .outOfFuel _ _ _ => false

private def successfulValueCallCommits : Bool :=
  terminalSatisfies
    (runValueScenario .commit returningChild rootInitialBalance
      childInitialBalance completionFuel) fun terminal =>
    terminal.outcome == .returned (encodeWordBytesBE transferValue) &&
      balance? terminal.finalWorld rootAddress == some rootFinalBalance &&
      balance? terminal.finalWorld childAddress == some childFinalBalance &&
      valueStored? terminal.finalWorld == some transferValue

private def revertingChildRollsBack : Bool :=
  terminalSatisfies
    (runValueScenario .commit revertingChild rootInitialBalance
      childInitialBalance completionFuel) fun terminal =>
    terminal.outcome == .reverted (encodeWordBytesBE childRevertPayload) &&
      balance? terminal.terminalContext.context.values.working.1 rootAddress ==
        some rootInitialBalance &&
      balance? terminal.finalWorld childAddress == some childInitialBalance &&
      valueStored? terminal.finalWorld == none &&
      terminal.committedDelta.balanceEndpoints rootAddress ==
        (some rootInitialBalance, some rootInitialBalance) &&
      terminal.committedDelta.balanceEndpoints childAddress ==
        (some childInitialBalance, some childInitialBalance) &&
      terminal.committedDelta.balanceEndpoints untouchedAddress ==
        (some untouchedBalance, some untouchedBalance) &&
      terminal.committedDelta.balanceChange? rootAddress == none &&
      terminal.committedDelta.balanceChange? childAddress == none &&
      terminal.committedDelta.balanceChange? untouchedAddress == none &&
      terminal.committedDelta.slotChange? childAddress valueSlot == none

private def trappingChildRollsBack : Bool :=
  terminalSatisfies
    (runValueScenario .commit trappingChild rootInitialBalance
      childInitialBalance completionFuel) fun terminal =>
    terminal.outcome == .trapped childTrapReason &&
      balance? terminal.terminalContext.context.values.working.1 childAddress ==
        some childInitialBalance &&
      balance? terminal.finalWorld rootAddress == some rootInitialBalance &&
      valueStored? terminal.finalWorld == none &&
      terminal.committedDelta.balanceEndpoints rootAddress ==
        (some rootInitialBalance, some rootInitialBalance) &&
      terminal.committedDelta.balanceEndpoints childAddress ==
        (some childInitialBalance, some childInitialBalance) &&
      terminal.committedDelta.balanceEndpoints untouchedAddress ==
        (some untouchedBalance, some untouchedBalance) &&
      terminal.committedDelta.balanceChange? rootAddress == none &&
      terminal.committedDelta.balanceChange? childAddress == none &&
      terminal.committedDelta.balanceChange? untouchedAddress == none &&
      terminal.committedDelta.slotChange? childAddress valueSlot == none

private def successfulChildThenRootRevertRollsBack : Bool :=
  terminalSatisfies
    (runValueScenario .revert returningChild rootInitialBalance
      childInitialBalance completionFuel) fun terminal =>
    terminal.outcome == .reverted (encodeWordBytesBE rootRevertPayload) &&
      balance? terminal.terminalContext.context.values.working.1 rootAddress ==
        some rootFinalBalance &&
      valueStored? terminal.terminalContext.context.values.working.1 ==
        some transferValue &&
      balance? terminal.finalWorld rootAddress == some rootInitialBalance &&
      balance? terminal.finalWorld childAddress == some childInitialBalance &&
      valueStored? terminal.finalWorld == none &&
      terminal.committedDelta.balanceEndpoints rootAddress ==
        (some rootInitialBalance, some rootInitialBalance) &&
      terminal.committedDelta.balanceEndpoints childAddress ==
        (some childInitialBalance, some childInitialBalance) &&
      terminal.committedDelta.balanceChange? rootAddress == none &&
      terminal.committedDelta.balanceChange? childAddress == none

private def successfulChildThenRootTrapRollsBack : Bool :=
  terminalSatisfies
    (runValueScenario .trap returningChild rootInitialBalance
      childInitialBalance completionFuel) fun terminal =>
    terminal.outcome == .trapped rootTrapReason &&
      balance? terminal.terminalContext.context.values.working.1 childAddress ==
        some childFinalBalance &&
      balance? terminal.finalWorld rootAddress == some rootInitialBalance &&
      balance? terminal.finalWorld childAddress == some childInitialBalance &&
      terminal.committedDelta.balanceEndpoints rootAddress ==
        (some rootInitialBalance, some rootInitialBalance) &&
      terminal.committedDelta.balanceEndpoints childAddress ==
        (some childInitialBalance, some childInitialBalance) &&
      terminal.committedDelta.balanceChange? rootAddress == none &&
      terminal.committedDelta.balanceChange? childAddress == none

private def insufficientFailsWithoutChildExecution : Bool :=
  terminalSatisfies
    (runValueScenario .commit returningChild insufficientBalance
      childInitialBalance completionFuel) fun terminal =>
    terminal.outcome == .trapped ContractCallFailure.insufficientBalance.code &&
      balance? terminal.finalWorld rootAddress == some insufficientBalance &&
      balance? terminal.finalWorld childAddress == some childInitialBalance &&
      valueStored? terminal.finalWorld == none

private def overflowFailsWithoutChildExecution : Bool :=
  terminalSatisfies
    (runValueScenario .commit returningChild rootInitialBalance maximumBalance
      completionFuel) fun terminal =>
    terminal.outcome == .trapped ContractCallFailure.balanceOverflow.code &&
      balance? terminal.finalWorld rootAddress == some rootInitialBalance &&
      balance? terminal.finalWorld childAddress == some maximumBalance &&
      valueStored? terminal.finalWorld == none

private def legacyZeroCallPreservesBalances : Bool :=
  terminalSatisfies (runLegacyScenario completionFuel) fun terminal =>
    balance? terminal.finalWorld rootAddress == some rootInitialBalance &&
      balance? terminal.finalWorld childAddress == some childInitialBalance &&
      balance? terminal.finalWorld untouchedAddress == some untouchedBalance

private def balanceDeltasAreExact : Bool :=
  terminalSatisfies
    (runValueScenario .commit returningChild rootInitialBalance
      childInitialBalance completionFuel) fun terminal =>
    terminal.committedDelta.balanceEndpoints rootAddress ==
        (some rootInitialBalance, some rootFinalBalance) &&
      terminal.committedDelta.balanceEndpoints childAddress ==
        (some childInitialBalance, some childFinalBalance) &&
      terminal.committedDelta.balanceEndpoints untouchedAddress ==
        (some untouchedBalance, some untouchedBalance) &&
      terminal.committedDelta.balanceChange? untouchedAddress == none

private def childPrefixFuel : Nat := 14

private def valueScenario (fuel : Nat) :=
  runValueScenario .commit returningChild rootInitialBalance
    childInitialBalance fuel

private def childOutOfFuelRetainsOneTransfer : Bool :=
  match (valueScenario childPrefixFuel).view with
  | .outOfFuel _ (.child frame) _ =>
      balance? frame.childContext.context.values.working.1 rootAddress ==
          some rootFinalBalance &&
        balance? frame.childContext.context.values.working.1 childAddress ==
          some childFinalBalance &&
        valueStored? frame.childContext.context.values.working.1 == none
  | _ => false

private abbrev ResumedObservation :=
  FrameOutcome Word × Option Word × Option Word × Option Word ×
    (Option Word × Option Word) × Option (Option Word × Option Word)

private def resumedObservation? (result := valueScenario completionFuel) :
    Option ResumedObservation :=
  match result.view with
  | .completed terminal => some
      (terminal.outcome,
        balance? terminal.finalWorld rootAddress,
        balance? terminal.finalWorld childAddress,
        valueStored? terminal.finalWorld,
        terminal.committedDelta.balanceEndpoints childAddress,
        terminal.committedDelta.slotChange? childAddress valueSlot)
  | .outOfFuel _ _ _ => none

private def childOutOfFuelResumesWithoutDoubleTransfer : Bool :=
  let split := resumeWithFuel (valueScenario childPrefixFuel) completionFuel
  let oneShot := valueScenario (childPrefixFuel + completionFuel)
  resumedObservation? split == resumedObservation? oneShot &&
    resumedObservation? split == some
      (.returned (encodeWordBytesBE transferValue),
        some rootFinalBalance, some childFinalBalance, some transferValue,
        (some childInitialBalance, some childFinalBalance),
        some (some Word.zero, some transferValue))

private def resumedRootPrefixFuel : Nat := 35

private def completedChildRootOutOfFuelRetainsEffects : Bool :=
  match (valueScenario resumedRootPrefixFuel).view with
  | .outOfFuel _ (.root frame) _ =>
      balance? frame.context.context.values.working.1 rootAddress ==
          some rootFinalBalance &&
        balance? frame.context.context.values.working.1 childAddress ==
          some childFinalBalance &&
        valueStored? frame.context.context.values.working.1 == some transferValue
  | _ => false

private def completedChildRootOutOfFuelResumesExactly : Bool :=
  let split := resumeWithFuel (valueScenario resumedRootPrefixFuel) completionFuel
  let oneShot := valueScenario (resumedRootPrefixFuel + completionFuel)
  resumedObservation? split == resumedObservation? oneShot &&
    resumedObservation? split == some
      (.returned (encodeWordBytesBE transferValue),
        some rootFinalBalance, some childFinalBalance, some transferValue,
        (some childInitialBalance, some childFinalBalance),
        some (some Word.zero, some transferValue))

private def childValueCallDepthFailsWithoutTransfer : Bool :=
  terminalSatisfies
    (runValueScenario .commit valueDepthChild rootInitialBalance
      childInitialBalance completionFuel) fun terminal =>
    terminal.outcome ==
        .returned (encodeWordBytesBE ContractCallFailure.depthExceeded.code) &&
      balance? terminal.finalWorld rootAddress == some rootFinalBalance &&
      balance? terminal.finalWorld childAddress == some childFinalBalance &&
      terminal.committedDelta.balanceEndpoints rootAddress ==
        (some rootInitialBalance, some rootFinalBalance) &&
      terminal.committedDelta.balanceEndpoints childAddress ==
        (some childInitialBalance, some childFinalBalance)

private def dispatchFailureIsIdentity
    (target : Word) (failure : ContractCallFailure) : Bool :=
  terminalSatisfies (runTargetScenario target completionFuel) fun terminal =>
    terminal.outcome == .trapped failure.code &&
      balance? terminal.finalWorld rootAddress == some rootInitialBalance &&
      balance? terminal.finalWorld childAddress == some childInitialBalance &&
      valueStored? terminal.finalWorld == none &&
      terminal.committedDelta.balanceEndpoints rootAddress ==
        (some rootInitialBalance, some rootInitialBalance) &&
      terminal.committedDelta.balanceEndpoints childAddress ==
        (some childInitialBalance, some childInitialBalance) &&
      terminal.committedDelta.balanceEndpoints untouchedAddress ==
        (some untouchedBalance, some untouchedBalance) &&
      terminal.committedDelta.balanceChange? rootAddress == none &&
      terminal.committedDelta.balanceChange? childAddress == none &&
      terminal.committedDelta.balanceChange? untouchedAddress == none &&
      terminal.committedDelta.slotChange? childAddress valueSlot == none

private def invalidValueCallIsIdentity : Bool :=
  dispatchFailureIsIdentity invalidTargetWord .invalidAddress

private def unavailableValueCallIsIdentity : Bool :=
  dispatchFailureIsIdentity unavailableTargetWord .unavailable

private def consumeSelfValueCall (call : Expr) : Expr :=
  .caseE call
    (returnedExpr
      (.apply (.var (HostFunction.storageRead.index + 1)) (.word valueSlot)))
    (.caseE (.var 0)
      (revertedExpr (.var 0))
      (.caseE (.var 0)
        (trappedExpr (.var 0))
        (.letE
          (.apply (.var (HostFunction.callValue.index + 3)) .unit)
          (.letE
            (.apply (.var (HostFunction.storageWrite.index + 4))
              (.pair (.word valueSlot) (.var 0)))
            (returnedExpr (.var 1))))))

private def selfValueProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body := consumeSelfValueCall
    (valueCallExpr rootTargetWord transferValue callInput)
}

private theorem selfValueProgram_checked :
    selfValueProgram.checkHost = true := by decide

private def selfValueContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨selfValueProgram, selfValueProgram_checked⟩ rfl

private def selfWorld : WorldState :=
  WorldState.empty.putAccount rootAddress
    (accountWithBalance selfValueContract rootInitialBalance)

private def selfInstalled :
    InstalledCheckedCoreContract selfWorld rootAddress selfValueContract := {
  account := accountWithBalance selfValueContract rootInitialBalance
  account_present := by rfl
  code_present := by rfl
}

private def selfRegistry : CheckedContractRegistry := {
  lookup := fun address =>
    if address = rootAddress then some selfValueContract else none
}

private def selfValueCallCommitsWithoutBalanceMovement : Bool :=
  terminalSatisfies
    (OneLevelNestedExecution.run selfValueContract invocation selfInstalled
      selfRegistry completionFuel) fun terminal =>
    terminal.outcome == .returned (encodeWordBytesBE transferValue) &&
      terminal.finalWorld.balance? rootAddress == some rootInitialBalance &&
      terminal.finalWorld.readStorage? rootAddress valueSlot == some transferValue

private theorem compileTimeNestedValueCalls :
    successfulValueCallCommits && revertingChildRollsBack &&
      trappingChildRollsBack && successfulChildThenRootRevertRollsBack &&
      successfulChildThenRootTrapRollsBack &&
      insufficientFailsWithoutChildExecution &&
      overflowFailsWithoutChildExecution && legacyZeroCallPreservesBalances &&
      selfValueCallCommitsWithoutBalanceMovement && balanceDeltasAreExact &&
      childOutOfFuelRetainsOneTransfer &&
      childOutOfFuelResumesWithoutDoubleTransfer &&
      completedChildRootOutOfFuelRetainsEffects &&
      completedChildRootOutOfFuelResumesExactly &&
      childValueCallDepthFailsWithoutTransfer && invalidValueCallIsIdentity &&
      unavailableValueCallIsIdentity = true := by
  native_decide

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def testAdr0147NestedValueExecution : IO Unit := do
  assertTrue successfulValueCallCommits "nested value-call commit failed"
  assertTrue revertingChildRollsBack "child revert did not roll back value call"
  assertTrue trappingChildRollsBack "child trap did not roll back value call"
  assertTrue successfulChildThenRootRevertRollsBack
    "root revert did not globally roll back child value call"
  assertTrue successfulChildThenRootTrapRollsBack
    "root trap did not globally roll back child value call"
  assertTrue insufficientFailsWithoutChildExecution
    "insufficient balance did not fail before child execution"
  assertTrue overflowFailsWithoutChildExecution
    "recipient overflow did not fail before child execution"
  assertTrue legacyZeroCallPreservesBalances "legacy call changed balances"
  assertTrue selfValueCallCommitsWithoutBalanceMovement
    "self value call changed balance or lost child storage"
  assertTrue balanceDeltasAreExact "nested value-call balance deltas were inexact"
  assertTrue childOutOfFuelRetainsOneTransfer
    "child out-of-fuel state did not retain exactly one transfer"
  assertTrue childOutOfFuelResumesWithoutDoubleTransfer
    "resumed child value call diverged or applied transfer/effects twice"
  assertTrue completedChildRootOutOfFuelRetainsEffects
    "root out-of-fuel after child completion lost transfer/effects"
  assertTrue completedChildRootOutOfFuelResumesExactly
    "resumed root after child completion diverged or replayed the child"
  assertTrue childValueCallDepthFailsWithoutTransfer
    "leaf value call did not return depth failure without a second transfer"
  assertTrue invalidValueCallIsIdentity
    "invalid value-call target changed world or committed delta"
  assertTrue unavailableValueCallIsIdentity
    "unavailable value-call target changed world or committed delta"

end Tests
