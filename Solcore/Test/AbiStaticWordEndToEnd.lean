import Solcore.Test.AbiStaticWordEndToEndFixture
import Solcore.ContractRuntime.BalancedTopLevelExecution

/-! Executable vertical checks for Static Word ABI routing and finalization. -/

set_option autoImplicit false

namespace Tests.AbiStaticWordEndToEnd

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.ContractRuntime.BalancedTopLevelExecution
open Solcore.ContractRuntime.OneLevelNestedExecution
open Solcore.Abi.V1
open Tests.AbiStaticWordEndToEndFixture

private def storageAt?
    (world : WorldState) (slot : Word) : Option Word :=
  world.readStorage? target slot

private def terminal?
    {initial : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initial root invocation) :
    Option (TerminalResult initial root invocation) :=
  match result.view with
  | .rejected _ => none
  | .execution execution =>
      match execution.view with
      | .completed terminal => some terminal
      | .outOfFuel _ _ _ => none

/-- A proof-irrelevant projection used to compare dependent raw/convenience runs. -/
private structure TerminalObservation where
  outcome : FrameOutcome Word
  callerFinal : Option Word
  targetFinal : Option Word
  storedFinal : Option Word
  logs : List CheckedCoreWordLog
  committedLogs : List CheckedCoreWordLog
  storageEndpoints : Option Word × Option Word
  callerBalanceEndpoints : Option Word × Option Word
  targetBalanceEndpoints : Option Word × Option Word
  deriving BEq

private def observeTerminal?
    {initial : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initial root invocation) :
    Option TerminalObservation := do
  let terminal ← terminal? result
  some {
    outcome := terminal.outcome
    callerFinal := terminal.finalWorld.balance? caller
    targetFinal := terminal.finalWorld.balance? target
    storedFinal := storageAt? terminal.finalWorld storageSlot
    logs := terminal.workingJournal.logList
    committedLogs := terminal.committedJournal.logList
    storageEndpoints :=
      terminal.committedDelta.storageEndpoints target storageSlot
    callerBalanceEndpoints :=
      terminal.committedDelta.balanceEndpoints caller
    targetBalanceEndpoints :=
      terminal.committedDelta.balanceEndpoints target
  }

private def successChecksFor
    {initial : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initial root invocation) : Bool :=
  match terminal? result with
  | none => false
  | some terminal =>
      terminal.outcome == .returned (encodeResult argument) &&
        terminal.finalWorld.balance? caller == some callerBalanceAfter &&
        terminal.finalWorld.balance? target == some targetBalanceAfter &&
        storageAt? terminal.finalWorld storageSlot == some argument &&
        terminal.workingJournal.logList == [expectedLog] &&
        terminal.committedJournal.logList == [expectedLog] &&
        terminal.committedJournal.createdContractList == [] &&
        terminal.committedDelta.storageEndpoints target storageSlot ==
          (some Word.zero, some argument) &&
        terminal.committedDelta.slotChange? target storageSlot ==
          some (some Word.zero, some argument) &&
        terminal.committedDelta.balanceEndpoints caller ==
          (some callerBalance, some callerBalanceAfter) &&
        terminal.committedDelta.balanceEndpoints target ==
          (some targetBalance, some targetBalanceAfter)

private def canonicalAndSuffixCommit : Bool :=
  let canonical := runCanonical completionFuel
  let rawCanonical := runRaw canonicalInput completionFuel
  let suffixed := runRaw suffixedInput completionFuel
  successChecksFor canonical && successChecksFor rawCanonical &&
    successChecksFor suffixed &&
    observeTerminal? canonical == observeTerminal? rawCanonical &&
    observeTerminal? canonical == observeTerminal? suffixed

private def rollbackChecks
    (input : HostStorageDriver.InputData) (reason : Word) : Bool :=
  match terminal? (runRaw input completionFuel) with
  | none => false
  | some terminal =>
      let checkpoint :=
        terminal.terminalContext.context.values.checkpoint.state
      terminal.outcome == .reverted (encodeResult reason) &&
        terminal.finalWorld.balance? caller == some callerBalance &&
        terminal.finalWorld.balance? target == some targetBalance &&
        storageAt? terminal.finalWorld storageSlot == some Word.zero &&
        checkpoint.balance? caller == some callerBalance &&
        checkpoint.balance? target == some targetBalance &&
        storageAt? checkpoint storageSlot == some Word.zero &&
        terminal.terminalContext.context.values.checkpoint.effects.rollback.logList ==
          [] &&
        terminal.workingJournal.logList == [] &&
        terminal.committedJournal.logList == [] &&
        terminal.committedJournal.createdContractList == [] &&
        terminal.committedDelta.storageEndpoints target storageSlot ==
          (some Word.zero, some Word.zero) &&
        terminal.committedDelta.slotChange? target storageSlot == none &&
        terminal.committedDelta.balanceEndpoints caller ==
          (some callerBalance, some callerBalance) &&
        terminal.committedDelta.balanceEndpoints target ==
          (some targetBalance, some targetBalance) &&
        terminal.committedDelta.balanceChange? caller == none &&
        terminal.committedDelta.balanceChange? target == none

private def routingRollback : Bool :=
  rollbackChecks shortInput malformedCalldataReason &&
    rollbackChecks unknownInput unknownSelectorReason

private structure InFlightObservation where
  callerWorking : Option Word
  targetWorking : Option Word
  storedWorking : Option Word
  logs : List CheckedCoreWordLog
  deriving BEq

private def observeRootOutOfFuel?
    {initial : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initial root invocation) :
    Option InFlightObservation :=
  match result.view with
  | .rejected _ => none
  | .execution execution =>
      match execution.view with
      | .completed _ => none
      | .outOfFuel _ (.root frame) _ =>
          let working := frame.context.context.values.working.1
          some {
            callerWorking := working.balance? caller
            targetWorking := working.balance? target
            storedWorking := storageAt? working storageSlot
            logs := frame.context.workingJournal.logList
          }
      | .outOfFuel _ (.child _) _ => none
      | .outOfFuel _ (.initializer _) _ => none

private def transferredBeforeMethod : InFlightObservation := {
  callerWorking := some callerBalanceAfter
  targetWorking := some targetBalanceAfter
  storedWorking := some Word.zero
  logs := []
}

private def afterSingleLog : InFlightObservation := {
  callerWorking := some callerBalanceAfter
  targetWorking := some targetBalanceAfter
  storedWorking := some argument
  logs := [expectedLog]
}

private def findSplit
    (expected : InFlightObservation) : Nat → Nat → Option Nat
  | _, 0 => none
  | fuel, remaining + 1 =>
      if observeRootOutOfFuel? (runCanonical fuel) == some expected then
        some fuel
      else
        findSplit expected (fuel + 1) remaining

private def zeroFuelIsGenuine : Bool :=
  (observeRootOutOfFuel? (runCanonical 0)).isSome

/-- Recognize the exact scheduler boundary after selector routing has entered
the selected method but before its first storage effect is handled.  The
result itself must be root fuel exhaustion; the retained Core control must be
ready to emit the fixture's first `storageWrite` suspension. -/
def beforeFirstMethodEffect (fuel : Nat) : Bool :=
  let result := runCanonical fuel
  match result.view with
  | .rejected _ => false
  | .execution execution =>
      match execution.view with
      | .completed _ => false
      | .outOfFuel _ (.root frame) _ =>
          match frame.state.control, frame.state.continuation,
              hostAdvance frame.state with
          | .ret (.pair (.word slot) (.word value)),
              .hostApply .storageWrite :: _,
              HostAdvanceResult.suspended suspension =>
              match suspension.request with
              | .storageWrite requestedSlot requestedValue =>
                  slot == storageSlot && value == argument &&
                    requestedSlot == storageSlot &&
                    requestedValue == argument &&
                    observeRootOutOfFuel? result ==
                      some transferredBeforeMethod
              | _ => false
          | _, _, _ => false
      | .outOfFuel _ (.child _) _ => false
      | .outOfFuel _ (.initializer _) _ => false

private def findBeforeFirstMethodEffect : Nat → Nat → Option Nat
  | _, 0 => none
  | fuel, remaining + 1 =>
      if beforeFirstMethodEffect fuel then
        some fuel
      else
        findBeforeFirstMethodEffect (fuel + 1) remaining

def beforeFirstMethodEffectFound : Bool :=
  match findBeforeFirstMethodEffect 1 512 with
  | some fuel => beforeFirstMethodEffect fuel
  | none => false

/-- Kernel-checkable evidence that the bounded fixture reaches precisely the
post-dispatch/pre-effect boundary, rather than merely sharing its world-state
observation with an earlier Core control point. -/
theorem beforeFirstMethodEffect_found_exact :
    beforeFirstMethodEffectFound = true := by
  native_decide

/-- The ABI wrapper consumes, without weakening, the balanced runner's exact
split-fuel equality.  In particular the value-transfer preflight and every
dispatcher or method effect occur exactly once. -/
theorem runCanonical_split_fuel (fuel additional : Nat) :
    BalancedTopLevelExecution.resumeWithFuel (runCanonical fuel) additional =
      runCanonical (fuel + additional) := by
  simpa [runCanonical, StaticWordContract.run, StaticWordContract.runRaw,
    StaticWordContract.callInvocation,
    Tests.AbiStaticWordEndToEndFixture.runRaw] using
    BalancedTopLevelExecution.resumeWithFuel_runWithEnvironment
      contract.checkedCore
      (StaticWordContract.callInvocation target caller callValue selected
        argument)
      installed environment fuel additional

private def resumedMatchesOneShot (splitFuel : Nat) : Bool :=
  let prefixRun := runCanonical splitFuel
  let resumed :=
    BalancedTopLevelExecution.resumeWithFuel prefixRun completionFuel
  let oneShot := runCanonical (splitFuel + completionFuel)
  successChecksFor resumed &&
    observeTerminal? resumed == observeTerminal? oneShot

private def dispatchAndLogResumption : Bool :=
  match findBeforeFirstMethodEffect 1 512,
      findSplit afterSingleLog 1 512 with
  | some dispatchFuel, some logFuel =>
      dispatchFuel < logFuel &&
        resumedMatchesOneShot dispatchFuel && resumedMatchesOneShot logFuel
  | _, _ => false

private def allChecks : Bool :=
  canonicalAndSuffixCommit && routingRollback && zeroFuelIsGenuine &&
    dispatchAndLogResumption

private theorem allChecks_exact : allChecks = true := by
  native_decide

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def testAbiStaticWordEndToEnd : IO Unit := do
  assertTrue canonicalAndSuffixCommit
    "canonical, suffixed, raw, or convenience ABI execution diverged"
  assertTrue routingRollback
    "malformed or unknown ABI routing did not roll value and state back"
  assertTrue zeroFuelIsGenuine
    "zero fuel did not retain a resumable ABI execution"
  assertTrue beforeFirstMethodEffectFound
    "ABI execution did not expose the exact post-dispatch/pre-effect boundary"
  assertTrue dispatchAndLogResumption
    "ABI resumption replayed dispatch, balance, storage, or the emitted log"

end Tests.AbiStaticWordEndToEnd
