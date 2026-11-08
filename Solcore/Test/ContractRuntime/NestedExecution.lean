import Solcore.ContractRuntime.Internal.NestedLaws
import Solcore.ContractRuntime.Internal.WorldStateDeltaLaws
import Solcore.Test.ContractRuntime.Creation

/-!
# Nested execution tests

The depth-one nested scheduler, resumption, nested value calls and nested creation lifecycles.
-/

section
-- leanmerge: from Solcore.Test.Adr0147NestedValueSchedulerExternalProperties
/-! External compile consumers for nested value-call scheduler laws. -/

set_option autoImplicit false

namespace Tests.Adr0147NestedValueSchedulerExternalProperties

example :=
  Solcore.ContractRuntime.OneLevelNestedExecution.CallProfile.request_legacy
example :=
  Solcore.ContractRuntime.OneLevelNestedExecution.CallProfile.request_withValue
example :=
  Solcore.ContractRuntime.OneLevelNestedExecution.CallProfile.target_legacy
example :=
  Solcore.ContractRuntime.OneLevelNestedExecution.CallProfile.target_withValue
example :=
  Solcore.ContractRuntime.OneLevelNestedExecution.CallProfile.invocation_legacy
example :=
  Solcore.ContractRuntime.OneLevelNestedExecution.CallProfile.invocation_withValue

end Tests.Adr0147NestedValueSchedulerExternalProperties
end

section
-- leanmerge: from Solcore.Test.OneLevelNestedExecutionFixture
/-! Executable checked-contract fixtures for one-level nested calls. -/

set_option autoImplicit false

namespace Tests.OneLevelNestedExecutionFixture

open Solcore.Core
open Solcore.ContractRuntime

def rootAddress : Address := ⟨0x10, by decide⟩
def childAddress : Address := ⟨0x20, by decide⟩
def unavailableAddress : Address := ⟨0x30, by decide⟩
def callerAddress : Address := ⟨0x40, by decide⟩

def childTargetWord : Word := addressToWord childAddress
def unavailableTargetWord : Word := addressToWord unavailableAddress
def invalidTargetWord : Word := ⟨2 ^ 160, by decide⟩
def rootTargetWord : Word := addressToWord rootAddress

def callInput : Word := ⟨0x77, by decide⟩
def childSlot : Word := ⟨0x51, by decide⟩
def rootSlot : Word := ⟨0x52, by decide⟩
def childOldValue : Word := ⟨0x61, by decide⟩
def childNewValue : Word := ⟨0x62, by decide⟩
def childPayload : Word := ⟨0x71, by decide⟩
def childRevertPayload : Word := ⟨0x72, by decide⟩
def childTrapReason : Word := ⟨0x73, by decide⟩
def rootRevertPayload : Word := ⟨0x81, by decide⟩
def rootTrapReason : Word := ⟨0x82, by decide⟩

def returnedExpr (payload : Expr) : Expr :=
  .inLeft (.sum .word .word) payload

def revertedExpr (payload : Expr) : Expr :=
  .inRight .word (.inLeft .word payload)

def trappedExpr (reason : Expr) : Expr :=
  .inRight .word (.inRight .word reason)

/-- What the root does after receiving a successful child return. -/
inductive RootReturnPolicy where
  | commit
  | revert
  | trap
  deriving Repr, BEq, DecidableEq

def rootReturnedBranch : RootReturnPolicy → Expr
  | .commit => returnedExpr (.var 0)
  | .revert => revertedExpr (.word rootRevertPayload)
  | .trap => trappedExpr (.word rootTrapReason)

/--
Decode all four typed call-result branches. Child return follows the selected
root policy; child revert/trap propagate; dispatch failure becomes a root trap.
-/
def consumeCallResult (policy : RootReturnPolicy) (call : Expr) : Expr :=
  .caseE call
    (rootReturnedBranch policy)
    (.caseE (.var 0)
      (revertedExpr (.var 0))
      (.caseE (.var 0)
        (trappedExpr (.var 0))
        (trappedExpr (.var 0))))

def rootProgram (policy : RootReturnPolicy) (target : Word) : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body := consumeCallResult policy
    (.apply (.var HostFunction.callContractWord.index)
      (.pair (.word target) (.word callInput)))
}

theorem rootProgram_checked (policy : RootReturnPolicy) (target : Word) :
    (rootProgram policy target).checkHost = true := by
  cases policy <;> rfl

def rootContract
    (policy : RootReturnPolicy) (target : Word) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨rootProgram policy target, rootProgram_checked policy target⟩ rfl

def childTerminalExpr : CheckedCoreWordOutcome → Expr
  | .returned data => returnedExpr (.word data)
  | .reverted data => revertedExpr (.word data)
  | .trapped reason => trappedExpr (.word reason)

def childTerminalProgram (outcome : CheckedCoreWordOutcome) : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE
      (.apply (.var HostFunction.storageWrite.index)
        (.pair (.word childSlot) (.word childNewValue)))
      (childTerminalExpr outcome)
}

theorem childTerminalProgram_checked (outcome : CheckedCoreWordOutcome) :
    (childTerminalProgram outcome).checkHost = true := by
  cases outcome <;> rfl

def childTerminalContract
    (outcome : CheckedCoreWordOutcome) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨childTerminalProgram outcome, childTerminalProgram_checked outcome⟩
    rfl

def childReturnContract : CheckedCoreContract :=
  childTerminalContract (.returned childPayload)

def childRevertContract : CheckedCoreContract :=
  childTerminalContract (.reverted childRevertPayload)

def childTrapContract : CheckedCoreContract :=
  childTerminalContract (.trapped childTrapReason)

/-- Map a leaf-level depth failure back into a successful Word result. -/
def consumeDepthProbe (call : Expr) : Expr :=
  .caseE call
    (returnedExpr (.var 0))
    (.caseE (.var 0)
      (returnedExpr (.var 0))
      (.caseE (.var 0)
        (returnedExpr (.var 0))
        (returnedExpr (.var 0))))

/-- Write child storage, then attempt a forbidden grandchild call. -/
def childDepthProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE
      (.apply (.var HostFunction.storageWrite.index)
        (.pair (.word childSlot) (.word childNewValue)))
      (consumeDepthProbe
        (.apply (.var (HostFunction.callContractWord.index + 1))
          (.pair (.word rootTargetWord) (.word callInput))))
}

theorem childDepthProgram_checked :
    childDepthProgram.checkHost = true := by
  decide

def childDepthContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨childDepthProgram, childDepthProgram_checked⟩ rfl

def rootAccount (root : CheckedCoreContract) : Account :=
  Account.empty.withCode root.code

def childAccount (child : CheckedCoreContract) : Account :=
  (Account.empty.withCode child.code).storageWrite childSlot childOldValue

def initialWorld
    (root child : CheckedCoreContract) : WorldState :=
  WorldState.empty
    |>.putAccount rootAddress (rootAccount root)
    |>.putAccount childAddress (childAccount child)

def installedRoot
    (root child : CheckedCoreContract) :
    InstalledCheckedCoreContract (initialWorld root child) rootAddress root := {
  account := rootAccount root
  account_present := by rfl
  code_present := by rfl
}

def registry
    (root child : CheckedCoreContract) : CheckedContractRegistry := {
  lookup := fun address =>
    if address = rootAddress then some root
    else if address = childAddress then some child
    else none
}

def invocation : TopLevelInvocation := {
  target := rootAddress
  caller := callerAddress
  callValue := Word.zero
  inputData := HostStorageDriver.InputData.ofWord callInput
}

def runScenario
    (root child : CheckedCoreContract) (fuel : Nat) :
    OneLevelNestedExecution.Result (initialWorld root child) root invocation :=
  OneLevelNestedExecution.run root invocation (installedRoot root child)
    (registry root child) fuel

def childStorageValue?
    (world : WorldState) : Option Word :=
  (world.account? childAddress).bind fun account =>
    account.storageValue? childSlot

def rootStorageValue?
    (world : WorldState) : Option Word :=
  (world.account? rootAddress).bind fun account =>
    account.storageValue? rootSlot

end Tests.OneLevelNestedExecutionFixture
end

section
-- leanmerge: from Solcore.Test.Adr0147NestedValueExecutionFixture
/-! Actual checked-Core fixtures for depth-one value-bearing calls. -/

set_option autoImplicit false

namespace Tests.Adr0147NestedValueExecutionFixture

open Solcore.Core
open Solcore.ContractRuntime
open Tests.OneLevelNestedExecutionFixture

def transferValue : Word := ⟨3, by decide⟩
def rootInitialBalance : Word := ⟨10, by decide⟩
def rootFinalBalance : Word := ⟨7, by decide⟩
def childInitialBalance : Word := ⟨4, by decide⟩
def childFinalBalance : Word := ⟨7, by decide⟩
def insufficientBalance : Word := ⟨2, by decide⟩
def maximumBalance : Word := ⟨2 ^ 256 - 1, by decide⟩
def untouchedAddress : Address := ⟨0x90, by decide⟩
def untouchedBalance : Word := ⟨9, by decide⟩
def valueSlot : Word := ⟨0xa1, by decide⟩
def sentinel : Word := ⟨0xa2, by decide⟩

def valueCallExpr (target value input : Word) : Expr :=
  .apply (.var HostFunction.callContractWordWithValue.index)
    (.pair (.word target) (.pair (.word value) (.word input)))

def valueRootProgram (policy : RootReturnPolicy) (target value : Word) : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body := consumeCallResult policy (valueCallExpr target value callInput)
}

theorem valueRootProgram_checked
    (policy : RootReturnPolicy) (target value : Word) :
    (valueRootProgram policy target value).checkHost = true := by
  cases policy <;> rfl

def valueRootContract
    (policy : RootReturnPolicy) (target value : Word) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨valueRootProgram policy target value,
      valueRootProgram_checked policy target value⟩ rfl

def valueChildProgram (outcome : CheckedCoreWordOutcome) : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE
      (.apply (.var HostFunction.callValue.index) .unit)
      (.letE
        (.apply (.var (HostFunction.storageWrite.index + 1))
          (.pair (.word valueSlot) (.var 0)))
        (match outcome with
        | .returned _ => returnedExpr (.var 1)
        | .reverted data => revertedExpr (.word data)
        | .trapped reason => trappedExpr (.word reason)))
}

theorem valueChildProgram_checked (outcome : CheckedCoreWordOutcome) :
    (valueChildProgram outcome).checkHost = true := by
  cases outcome <;> rfl

def valueChildContract (outcome : CheckedCoreWordOutcome) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨valueChildProgram outcome, valueChildProgram_checked outcome⟩ rfl

def returningChild : CheckedCoreContract :=
  valueChildContract (.returned sentinel)
def revertingChild : CheckedCoreContract :=
  valueChildContract (.reverted childRevertPayload)
def trappingChild : CheckedCoreContract :=
  valueChildContract (.trapped childTrapReason)

/-- A leaf value-call is handled flat and returns the depth failure code. -/
def valueDepthChildProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body := consumeDepthProbe
    (valueCallExpr rootTargetWord transferValue callInput)
}

theorem valueDepthChildProgram_checked :
    valueDepthChildProgram.checkHost = true := by decide

def valueDepthChild : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨valueDepthChildProgram, valueDepthChildProgram_checked⟩ rfl

def accountWithBalance (contract : CheckedCoreContract) (balance : Word) : Account :=
  (Account.empty.withCode contract.code).withBalance balance

def scenarioWorld (root child : CheckedCoreContract)
    (rootBalance childBalance : Word) : WorldState :=
  WorldState.empty
    |>.putAccount rootAddress (accountWithBalance root rootBalance)
    |>.putAccount childAddress (accountWithBalance child childBalance)
    |>.putAccount untouchedAddress (Account.empty.withBalance untouchedBalance)

def scenarioInstalled (root child : CheckedCoreContract)
    (rootBalance childBalance : Word) :
    InstalledCheckedCoreContract
      (scenarioWorld root child rootBalance childBalance) rootAddress root := {
  account := accountWithBalance root rootBalance
  account_present := by rfl
  code_present := by rfl
}

def runValueScenario (policy : RootReturnPolicy) (child : CheckedCoreContract)
    (rootBalance childBalance : Word) (fuel : Nat) :=
  let root := valueRootContract policy childTargetWord transferValue
  OneLevelNestedExecution.run root invocation
    (scenarioInstalled root child rootBalance childBalance)
    (registry root child) fuel

def runTargetScenario (target : Word) (fuel : Nat) :=
  let root := valueRootContract .commit target transferValue
  OneLevelNestedExecution.run root invocation
    (scenarioInstalled root returningChild rootInitialBalance
      childInitialBalance)
    (registry root returningChild) fuel

def legacyWorld (root child : CheckedCoreContract) : WorldState :=
  scenarioWorld root child rootInitialBalance childInitialBalance

def runLegacyScenario (fuel : Nat) :=
  let root := rootContract .commit childTargetWord
  OneLevelNestedExecution.run root invocation
    (scenarioInstalled root childReturnContract rootInitialBalance
      childInitialBalance)
    (registry root childReturnContract) fuel

def balance? (world : WorldState) (address : Address) : Option Word :=
  world.balance? address

def valueStored? (world : WorldState) : Option Word :=
  (world.account? childAddress).bind fun account =>
    account.storageValue? valueSlot

end Tests.Adr0147NestedValueExecutionFixture
end

section
-- leanmerge: from Solcore.Test.Adr0147NestedValueExecution
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
end

section
-- leanmerge: from Solcore.Test.Adr0148NestedCreationLifecycleFixture
/-! Actual checked root fixture for prepared initializer lifecycle helpers. -/

set_option autoImplicit false

namespace Tests.Adr0148NestedCreationLifecycleFixture

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.ContractRuntime.OneLevelNestedExecution
open Tests.OneLevelNestedExecutionFixture
open Tests.Adr0148CheckedCreationPreflightFixture

def creationExpr : Expr :=
  .apply (.var HostFunction.createContractWord.index)
    (.pair (.word templateId) (.pair (.word value) (.word initializerPayload)))

def rootProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body := consumeCallResult .commit creationExpr
}

theorem rootProgram_checked : rootProgram.checkHost = true := by decide

def rootContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨rootProgram, rootProgram_checked⟩ rfl

def rootAccount : Account :=
  (creatorAccount creatorBalance oldNonce).withCode rootContract.code

def initialWorld : WorldState :=
  WorldState.empty
    |>.putAccount unrelated unrelatedAccount
    |>.putAccount creator rootAccount

def rootInstalled :
    InstalledCheckedCoreContract initialWorld creator rootContract := {
  account := rootAccount
  account_present := by rfl
  code_present := by rfl
}

def rootInvocation : TopLevelInvocation := {
  target := creator
  caller := unrelated
  callValue := Word.zero
  inputData := HostStorageDriver.InputData.ofWord initializerPayload
}

def initialFrame : RootFrame initialWorld rootContract rootInvocation :=
  RootFrame.initial rootContract rootInvocation rootInstalled

/-- Execute real typed root steps until its first creation suspension. -/
def seekCreation : (fuel : Nat) →
    (frame : RootFrame initialWorld rootContract rootInvocation) →
    frame.context.context.storageAddress = creator →
    Option { root : SuspendedCreationRoot initialWorld rootContract rootInvocation //
      root.parentContext.context.storageAddress = creator }
  | 0, _, _ => none
  | fuel + 1, frame, anchored =>
      match advanced : Solcore.Core.hostAdvance frame.state with
      | .next next => seekCreation fuel (frame.afterNext next advanced) anchored
      | .suspended ⟨request, continuation, store⟩ =>
          match request with
          | .createContractWord actualTemplate actualValue actualInput =>
              some ⟨frame.suspendCreation
                ⟨actualTemplate, actualValue, actualInput⟩ continuation store
                advanced, anchored⟩
          | _ => none
      | _ => none

def suspendedRoot? := seekCreation 128 initialFrame rfl

def completionObservation (outcome : CheckedCoreWordOutcome) : Bool :=
  match suspendedRoot? with
  | none => false
  | some suspendedWithAnchor =>
      let suspended := suspendedWithAnchor.1
      match CheckedCreationPreflight.prepare
          suspended.parentContext.context.values.working.1 validEnvironment
          rootInvocation.executionInputs.currentAddress
          suspended.profile.templateId suspended.profile.value with
      | .error _ => false
      | .ok prepared =>
          -- The fixture's initializer uses a one-Word convention.
          if oneWord : prepared.template.initializer.entryProfile.returnsOneWord = true then
            let frame := suspended.startInitializer validEnvironment prepared oneWord
              suspendedWithAnchor.2.symm
            match frame.complete outcome with
            | .returned deployed =>
                (deployed.deployedWorld.code? created).map
                    CheckedHostCoreProgram.program == some runtime.code.program &&
                  deployed.deployedAccount.storageValue? initializerPayload ==
                    deployed.latestCreatedAccount.storageValue? initializerPayload &&
                  deployed.deployedAccount.balance ==
                    deployed.latestCreatedAccount.balance &&
                  deployed.deployedAccount.nonce ==
                    deployed.latestCreatedAccount.nonce &&
                  (deployed.resumedRoot.context.context.values.working.1.code?
                      created).map CheckedHostCoreProgram.program ==
                    some runtime.code.program
            | .reverted data root _ _ =>
                data == initializerPayload &&
                  root.context.context.values.working.1.nonce? creator ==
                    some nextNonce &&
                  (root.context.context.values.working.1.account? created).isNone
            | .trapped reason root _ _ =>
                reason == initializerPayload &&
                  root.context.context.values.working.1.nonce? creator ==
                    some nextNonce &&
                  (root.context.context.values.working.1.account? created).isNone
          else false

end Tests.Adr0148NestedCreationLifecycleFixture
end

section
-- leanmerge: from Solcore.Test.Adr0148NestedCreationLifecycle
/-! External consumers and executable initializer-lifecycle regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.ContractRuntime.OneLevelNestedExecution
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

def testAdr0148NestedCreationLifecycle : IO Unit := do
  assertTrue returnInstallsRuntime
    "initializer return did not install runtime or preserve payload state"
  assertTrue revertSelectsPostNonce
    "initializer revert did not select post-nonce world or preserve payload"
  assertTrue trapSelectsPostNonce
    "initializer trap did not select post-nonce world or preserve reason"

end Tests
end

section
-- leanmerge: from Solcore.Test.OneLevelNestedExecution
/-! Runtime regressions for the one-level shared-fuel nested executor. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open OneLevelNestedExecutionFixture

private def completionFuel_variant : Nat := 512

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
  match result.view with
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
    (runScenario rootCommitContract childReturnContract completionFuel_variant)
    (.returned (encodeWordBytesBE childPayload))
    (some childNewValue) (some childNewValue)

private def childRevertRollsBack : Bool :=
  terminalMatches
    (runScenario rootCommitContract childRevertContract completionFuel_variant)
    (.reverted (encodeWordBytesBE childRevertPayload))
    (some childOldValue) (some childOldValue)

private def childTrapRollsBack : Bool :=
  terminalMatches
    (runScenario rootCommitContract childTrapContract completionFuel_variant)
    (.trapped childTrapReason)
    (some childOldValue) (some childOldValue)

private def rootRevertRollsBackSuccessfulChild : Bool :=
  terminalMatches
    (runScenario rootRevertContract childReturnContract completionFuel_variant)
    (.reverted (encodeWordBytesBE rootRevertPayload))
    (some childNewValue) (some childOldValue)

private def rootTrapRollsBackSuccessfulChild : Bool :=
  terminalMatches
    (runScenario rootTrapContract childReturnContract completionFuel_variant)
    (.trapped rootTrapReason)
    (some childNewValue) (some childOldValue)

private def invalidAddressIsTotalFailure : Bool :=
  terminalMatches
    (runScenario invalidAddressRoot childReturnContract completionFuel_variant)
    (.trapped ContractCallFailure.invalidAddress.code)
    (some childOldValue) (some childOldValue)

private def unavailableIsTotalFailure : Bool :=
  terminalMatches
    (runScenario unavailableRoot childReturnContract completionFuel_variant)
    (.trapped ContractCallFailure.unavailable.code)
    (some childOldValue) (some childOldValue)

private def depthExceededIsTypedLeafResponse : Bool :=
  terminalMatches
    (runScenario rootCommitContract childDepthContract completionFuel_variant)
    (.returned (encodeWordBytesBE ContractCallFailure.depthExceeded.code))
    (some childNewValue) (some childNewValue)

private def initialRegistryResolvesChild : Bool :=
  ((registry rootCommitContract childReturnContract).resolve?
    (initialWorld rootCommitContract childReturnContract)
    childAddress).isSome

private def rootOutOfFuelVisible : Bool :=
  match (runScenario rootCommitContract childReturnContract 0).view with
  | .outOfFuel _ (.root _) _ => true
  | _ => false

private def childOutOfFuelAt (fuel : Nat) : Bool :=
  match (runScenario rootCommitContract childReturnContract fuel).view with
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
end

section
-- leanmerge: from Solcore.Test.OneLevelNestedExecutionExtended
/-! Extended executable regressions for the depth-one nested scheduler. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open OneLevelNestedExecutionFixture

private def one : Word := ⟨1, by decide⟩
private def two : Word := ⟨2, by decide⟩
private def sequentialSlot : Word := ⟨0x91, by decide⟩
private def selfLeafPayload : Word := ⟨0x92, by decide⟩
private def selfWrittenValue : Word := ⟨0x93, by decide⟩
private def rootWrittenValue : Word := ⟨0x94, by decide⟩
private def untouchedAddress : Address := ⟨0x99, by decide⟩
private def untouchedSlot : Word := ⟨0x9a, by decide⟩

/-!
The same code runs as root and child. The root receives `returned` and reads
the slot. Its child receives the depth-limit `failed` branch, writes the slot,
and returns. The root read therefore observes whether self-call rebasing
refreshed the cached storage Account.
-/
private def consumeSelfCall (call : Expr) : Expr :=
  .caseE call
    (returnedExpr
      (.apply (.var (HostFunction.storageRead.index + 1))
        (.word rootSlot)))
    (.caseE (.var 0)
      (revertedExpr (.var 0))
      (.caseE (.var 0)
        (trappedExpr (.var 0))
        (.letE
          (.apply (.var (HostFunction.storageWrite.index + 3))
            (.pair (.word rootSlot) (.word selfWrittenValue)))
          (returnedExpr (.word selfLeafPayload)))))

private def selfCallProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body := consumeSelfCall
    (.apply (.var HostFunction.callContractWord.index)
      (.pair (.word rootTargetWord) (.word callInput)))
}

private theorem selfCallProgram_checked :
    selfCallProgram.checkHost = true := by
  decide

private def selfCallContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨selfCallProgram, selfCallProgram_checked⟩ rfl

private def selfCallRebasesStorage : Bool :=
  match (runScenario selfCallContract selfCallContract completionFuel).view with
  | .completed terminal =>
      terminal.outcome ==
          FrameOutcome.returned (encodeWordBytesBE selfWrittenValue) &&
        rootStorageValue?
          terminal.terminalContext.context.values.working.1 ==
            some selfWrittenValue &&
        rootStorageValue? terminal.finalWorld == some selfWrittenValue
  | .outOfFuel _ _ _ => false

private theorem compileTimeSelfCallRebase :
    selfCallRebasesStorage = true := by
  native_decide

/-! One leaf call increments a persistent slot and returns its new value. -/
private def incrementChildProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE
      (.apply (.var HostFunction.storageRead.index)
        (.word sequentialSlot))
      (.letE
        (.apply (.var (HostFunction.storageWrite.index + 1))
          (.pair (.word sequentialSlot)
            (.binary .wordAdd (.var 0) (.word one))))
        (returnedExpr (.binary .wordAdd (.var 1) (.word one))))
}

private theorem incrementChildProgram_checked :
    incrementChildProgram.checkHost = true := by
  decide

private def incrementChildContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨incrementChildProgram, incrementChildProgram_checked⟩ rfl

/-! Ignore the first typed result, then issue a second call in sequence. -/
private def sequentialRootProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE
      (.apply (.var HostFunction.callContractWord.index)
        (.pair (.word childTargetWord) (.word callInput)))
      (consumeCallResult .commit
        (.apply (.var (HostFunction.callContractWord.index + 1))
          (.pair (.word childTargetWord) (.word callInput))))
}

private theorem sequentialRootProgram_checked :
    sequentialRootProgram.checkHost = true := by
  decide

private def sequentialRootContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨sequentialRootProgram, sequentialRootProgram_checked⟩ rfl

private def sequentialCallsShareWorkingWorld : Bool :=
  match (runScenario sequentialRootContract incrementChildContract
      completionFuel).view with
  | .completed terminal =>
      terminal.outcome == FrameOutcome.returned (encodeWordBytesBE two) &&
        terminal.finalWorld.readStorage? childAddress sequentialSlot ==
          some two &&
        terminal.committedDelta.storageEndpoints childAddress sequentialSlot ==
          (some Word.zero, some two)
  | .outOfFuel _ _ _ => false

private theorem compileTimeSequentialCalls :
    sequentialCallsShareWorkingWorld = true := by
  native_decide

/-! The registry advertises code different from the code installed in world. -/
private def mismatchRootContract : CheckedCoreContract :=
  rootContract .commit childTargetWord

private def mismatchWorld : WorldState :=
  initialWorld mismatchRootContract childReturnContract

private def mismatchRegistry : CheckedContractRegistry := {
  lookup := fun address =>
    if address = rootAddress then some mismatchRootContract
    else if address = childAddress then some childRevertContract
    else none
}

private def mismatchRun :
    OneLevelNestedExecution.Result mismatchWorld mismatchRootContract invocation :=
  OneLevelNestedExecution.run mismatchRootContract invocation
    (installedRoot mismatchRootContract childReturnContract)
    mismatchRegistry completionFuel

private def registryCodeMismatchFails : Bool :=
  (mismatchRegistry.resolve? mismatchWorld childAddress).isNone &&
    match mismatchRun.view with
    | .completed terminal =>
        terminal.outcome ==
            FrameOutcome.trapped ContractCallFailure.unavailable.code &&
          childStorageValue? terminal.finalWorld == some childOldValue
    | .outOfFuel _ _ _ => false

private theorem compileTimeRegistryCodeMismatch :
    registryCodeMismatchFails = true := by
  native_decide

private def missingAccountRoot : CheckedCoreContract :=
  rootContract .commit unavailableTargetWord

private def missingAccountRegistry : CheckedContractRegistry := {
  lookup := fun address =>
    if address = rootAddress then some missingAccountRoot
    else if address = unavailableAddress then some childReturnContract
    else none
}

private def missingAccountRun :=
  OneLevelNestedExecution.run missingAccountRoot invocation
    (installedRoot missingAccountRoot childReturnContract)
    missingAccountRegistry completionFuel

private def registeredMissingAccountFails : Bool :=
  match missingAccountRun.view with
  | .completed terminal =>
      terminal.outcome ==
        FrameOutcome.trapped ContractCallFailure.unavailable.code
  | .outOfFuel _ _ _ => false

private theorem compileTimeRegisteredMissingAccount :
    registeredMissingAccountFails = true := by
  native_decide

private def missingCodeRoot : CheckedCoreContract :=
  rootContract .commit childTargetWord

private def missingCodeWorld : WorldState :=
  WorldState.empty
    |>.putAccount rootAddress (rootAccount missingCodeRoot)
    |>.putAccount childAddress Account.empty

private def missingCodeInstalled :
    InstalledCheckedCoreContract missingCodeWorld rootAddress missingCodeRoot := {
  account := rootAccount missingCodeRoot
  account_present := by rfl
  code_present := by rfl
}

private def missingCodeRun :=
  OneLevelNestedExecution.run missingCodeRoot invocation missingCodeInstalled
    (registry missingCodeRoot childReturnContract) completionFuel

private def registeredMissingCodeFails : Bool :=
  match missingCodeRun.view with
  | .completed terminal =>
      terminal.outcome ==
        FrameOutcome.trapped ContractCallFailure.unavailable.code
  | .outOfFuel _ _ _ => false

private theorem compileTimeRegisteredMissingCode :
    registeredMissingCodeFails = true := by
  native_decide

/-! Write root storage, commit a child write speculatively, then root-revert. -/
private def rollbackRootProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE
      (.apply (.var HostFunction.storageWrite.index)
        (.pair (.word rootSlot) (.word rootWrittenValue)))
      (consumeCallResult .revert
        (.apply (.var (HostFunction.callContractWord.index + 1))
          (.pair (.word childTargetWord) (.word callInput))))
}

private theorem rollbackRootProgram_checked :
    rollbackRootProgram.checkHost = true := by
  decide

private def rollbackRootContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨rollbackRootProgram, rollbackRootProgram_checked⟩ rfl

private def rollbackDeltaQueriesExact : Bool :=
  match (runScenario rollbackRootContract childReturnContract completionFuel).view with
  | .completed terminal =>
      terminal.outcome ==
          FrameOutcome.reverted (encodeWordBytesBE rootRevertPayload) &&
        terminal.workingDelta.storageEndpoints rootAddress rootSlot ==
          (some Word.zero, some rootWrittenValue) &&
        terminal.workingDelta.slotChange? rootAddress rootSlot ==
          some (some Word.zero, some rootWrittenValue) &&
        terminal.workingDelta.storageEndpoints childAddress childSlot ==
          (some childOldValue, some childNewValue) &&
        terminal.workingDelta.slotChange? childAddress childSlot ==
          some (some childOldValue, some childNewValue) &&
        terminal.workingDelta.storageEndpoints untouchedAddress untouchedSlot ==
          (none, none) &&
        terminal.workingDelta.slotChange? untouchedAddress untouchedSlot == none &&
        terminal.committedDelta.storageEndpoints rootAddress rootSlot ==
          (some Word.zero, some Word.zero) &&
        terminal.committedDelta.slotChange? rootAddress rootSlot == none &&
        terminal.committedDelta.storageEndpoints childAddress childSlot ==
          (some childOldValue, some childOldValue) &&
        terminal.committedDelta.slotChange? childAddress childSlot == none &&
        terminal.committedDelta.storageEndpoints untouchedAddress untouchedSlot ==
          (none, none) &&
        terminal.committedDelta.slotChange? untouchedAddress untouchedSlot == none
  | .outOfFuel _ _ _ => false

private theorem compileTimeRollbackDeltaQueries :
    rollbackDeltaQueriesExact = true := by
  native_decide

/-- Runtime counterparts for all extended nested-execution regressions. -/
def testOneLevelNestedExecutionExtended : IO Unit := do
  assertTrue selfCallRebasesStorage
    "self-call return did not refresh the root storage Account"
  assertTrue sequentialCallsShareWorkingWorld
    "sequential child calls did not share the committed working world"
  assertTrue registryCodeMismatchFails
    "registry/world code mismatch did not produce unavailable"
  assertTrue registeredMissingAccountFails
    "registered target with no Account did not produce unavailable"
  assertTrue registeredMissingCodeFails
    "registered Account with no code did not produce unavailable"
  assertTrue rollbackDeltaQueriesExact
    "root rollback did not expose exact root/child/untouched delta queries"

end Tests
end

section
-- leanmerge: from Solcore.Test.OneLevelNestedExecutionResumption
/-! Executable and external-consumer regressions for nested resumption. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open OneLevelNestedExecutionFixture

/-!
The child increments instead of assigning a constant. A resume that replayed
the completed write prefix would therefore leave `childNewValue + 1`.
-/
private def incrementChildProgram_variant : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE
      (.apply (.var HostFunction.storageRead.index) (.word childSlot))
      (.letE
        (.apply (.var (HostFunction.storageWrite.index + 1))
          (.pair (.word childSlot)
            (.binary .wordAdd (.var 0) (.word one))))
        (returnedExpr (.binary .wordAdd (.var 1) (.word one))))
}

private theorem incrementChildProgram_checked_variant :
    incrementChildProgram_variant.checkHost = true := by
  decide

private def incrementChildContract_variant : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨incrementChildProgram_variant, incrementChildProgram_checked_variant⟩ rfl

private def scenario (fuel : Nat) :
    OneLevelNestedExecution.Result
      (initialWorld rootCommitContract incrementChildContract_variant)
      rootCommitContract invocation :=
  runScenario rootCommitContract incrementChildContract_variant fuel

private def additionalFuel : Nat := 64
private def rootPrefixFuel : Nat := 0
private def writtenChildPrefixFuel : Nat := 31
private def resumedRootPrefixFuel_variant : Nat := 39

private abbrev TerminalObservation :=
  FrameOutcome Word × Option Word × Option Word

private def terminalObservation? (result := scenario additionalFuel) :
    Option TerminalObservation :=
  match result.view with
  | .completed terminal =>
      some
        (terminal.outcome,
          childStorageValue?
            terminal.terminalContext.context.values.working.1,
          childStorageValue? terminal.finalWorld)
  | .outOfFuel _ _ _ => none

private def expectedObservation : Option TerminalObservation :=
  some
    (.returned (encodeWordBytesBE childNewValue),
      some childNewValue, some childNewValue)

private def splitMatchesOneShot (prefixFuel : Nat) : Bool :=
  let split :=
    OneLevelNestedExecution.resumeWithFuel (scenario prefixFuel)
      additionalFuel
  let oneShot := scenario (prefixFuel + additionalFuel)
  terminalObservation? split == terminalObservation? oneShot &&
    terminalObservation? split == expectedObservation

private def rootOutOfFuelAt
    (fuel : Nat) (expectedChild : Option Word) : Bool :=
  match (scenario fuel).view with
  | .outOfFuel _ (.root frame) _ =>
      childStorageValue?
          frame.context.context.values.working.1 == expectedChild
  | _ => false

private def childOutOfFuelAt_variant
    (fuel : Nat) (expectedChild : Option Word) : Bool :=
  match (scenario fuel).view with
  | .outOfFuel _ (.child frame) _ =>
      childStorageValue?
          frame.childContext.context.values.working.1 == expectedChild
  | _ => false

private def rootOutOfFuelResumesExactly : Bool :=
  rootOutOfFuelAt rootPrefixFuel (some childOldValue) &&
    splitMatchesOneShot rootPrefixFuel

private def writtenChildOutOfFuelResumesWithoutReplay : Bool :=
  childOutOfFuelAt_variant writtenChildPrefixFuel (some childNewValue) &&
    splitMatchesOneShot writtenChildPrefixFuel

private def childCompletedRootOutOfFuelResumesExactly : Bool :=
  rootOutOfFuelAt resumedRootPrefixFuel_variant (some childNewValue) &&
    splitMatchesOneShot resumedRootPrefixFuel_variant

private theorem compileTimeRootOutOfFuelResumption :
    rootOutOfFuelResumesExactly = true := by
  native_decide

private theorem compileTimeWrittenChildOutOfFuelResumption :
    writtenChildOutOfFuelResumesWithoutReplay = true := by
  native_decide

private theorem compileTimeChildCompletedRootResumption :
    childCompletedRootOutOfFuelResumesExactly = true := by
  native_decide

/-- Runtime counterparts for the three actual-run split boundaries. -/
def testOneLevelNestedExecutionResumption : IO Unit := do
  assertTrue rootOutOfFuelResumesExactly
    "root out-of-fuel resumption disagreed with one-shot execution"
  assertTrue writtenChildOutOfFuelResumesWithoutReplay
    "child resumption replayed or lost its non-idempotent storage prefix"
  assertTrue childCompletedRootOutOfFuelResumesExactly
    "post-child root resumption disagreed with one-shot execution"

end Tests

namespace ExternalOneLevelNestedExecutionResumptionConsumer

open Solcore.ContractRuntime
open OneLevelNestedExecution

example
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : ExecutionEnvironment)
    (fuel additional : Nat)
    (mode : Mode initialWorld rootContract rootInvocation)
    (reachable : Reachable registry mode) :
    resumeWithFuel (runMode registry fuel mode reachable) additional =
      runMode registry (fuel + additional) mode reachable :=
  resumeWithFuel_runMode registry fuel additional mode reachable

example
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : ExecutionEnvironment)
    (fuel : Nat)
    (mode : Mode initialWorld rootContract rootInvocation)
    (reachable : Reachable registry mode) :
    resumeWithFuel (runMode registry fuel mode reachable) 0 =
      runMode registry fuel mode reachable :=
  resumeWithFuel_runMode_zero registry fuel mode reachable

example
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (first second : Nat) :
    resumeWithFuel (resumeWithFuel result first) second =
      resumeWithFuel result (first + second) :=
  resumeWithFuel_add result first second

example
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : ExecutionEnvironment)
    (fuel first second : Nat)
    (mode : Mode initialWorld rootContract rootInvocation)
    (reachable : Reachable registry mode) :
    resumeWithFuel
        (resumeWithFuel (runMode registry fuel mode reachable) first) second =
      runMode registry (fuel + first + second) mode reachable :=
  resumeWithFuel_runMode_add registry fuel first second mode reachable

example
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (terminal : TerminalResult initialWorld rootContract rootInvocation)
    (completed : result.view = .completed terminal)
    (additional : Nat) :
    resumeWithFuel result additional = result :=
  resumeWithFuel_completed result terminal completed additional

example
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : ExecutionEnvironment)
    (mode : Mode initialWorld rootContract rootInvocation)
    (reachable : Reachable registry mode)
    (result : Result initialWorld rootContract rootInvocation)
    (exhausted : result.view = .outOfFuel registry mode reachable)
    (additional : Nat) :
    resumeWithFuel result additional =
      runMode registry additional mode reachable :=
  resumeWithFuel_outOfFuel registry mode reachable result exhausted additional

example
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (registry : CheckedContractRegistry)
    (fuel additional : Nat) :
    resumeWithFuel
        (run rootContract rootInvocation installed registry fuel) additional =
      run rootContract rootInvocation installed registry
        (fuel + additional) :=
  resumeWithFuel_run rootContract rootInvocation installed registry
    fuel additional

example
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (registry : CheckedContractRegistry)
    (fuel : Nat) :
    resumeWithFuel
        (run rootContract rootInvocation installed registry fuel) 0 =
      run rootContract rootInvocation installed registry fuel :=
  resumeWithFuel_run_zero rootContract rootInvocation installed registry fuel

example
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (registry : CheckedContractRegistry)
    (fuel first second : Nat) :
    resumeWithFuel
        (resumeWithFuel
          (run rootContract rootInvocation installed registry fuel) first)
        second =
      run rootContract rootInvocation installed registry
        (fuel + first + second) :=
  resumeWithFuel_run_add rootContract rootInvocation installed registry
    fuel first second

end ExternalOneLevelNestedExecutionResumptionConsumer
end
