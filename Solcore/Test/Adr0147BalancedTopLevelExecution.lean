import Solcore.Test.Adr0147BalancedTopLevelExecutionFixture

/-! Runtime regressions for atomic balance-aware checked root execution. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics
open TopLevelExecutionFixture
open Adr0147BalancedTopLevelExecutionFixture

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private inductive ObservedStatus where
  | rejected (failure : BalanceTransferFailure)
  | completed (outcome : FrameOutcome Word)
  deriving BEq

private def observedStatus
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initialWorld root invocation) :
    Option ObservedStatus :=
  match result.terminalStatus? with
  | none => none
  | some (.error failure) => some (.rejected failure)
  | some (.ok outcome) => some (.completed outcome)

private def finalBalance?
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initialWorld root invocation)
    (address : Address) : Option (Option Word) :=
  result.finalWorld?.map fun world => world.balance? address

private def committedBalanceChangesMatch
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initialWorld root invocation)
    (caller : Address)
    (callerChange targetChange : Option (Option Word × Option Word)) : Bool :=
  match result.committedWorld? with
  | none => false
  | some ⟨_, delta⟩ =>
      delta.balanceChange? caller == callerChange &&
        delta.balanceChange? targetAddress == targetChange

private def completedWorkingMatches
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initialWorld root invocation)
    (caller : Address)
    (callerBalance targetBalance : Option Word)
    (targetStorage : Option Word) : Bool :=
  match result.view with
  | .rejected _ => false
  | .execution execution =>
      match execution.view with
      | .outOfFuel _ _ _ => false
      | .completed terminal =>
          let working := terminal.terminalContext.context.values.working.1
          working.balance? caller == callerBalance &&
            working.balance? targetAddress == targetBalance &&
            storageValueAt? working targetAddress targetSlot == targetStorage

private def rejectedMatches
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initialWorld root invocation)
    (failure : BalanceTransferFailure)
    (caller target : Address)
    (callerBalance targetBalance : Option Word) : Bool :=
  match result.view with
  | .execution _ => false
  | .rejected rejected =>
      rejected.failure == failure &&
        observedStatus result == some (.rejected failure) &&
        rejected.finalWorld.balance? caller == callerBalance &&
        rejected.finalWorld.balance? target == targetBalance &&
        rejected.committedDelta.balanceChange? caller == none &&
        rejected.committedDelta.balanceChange? target == none

private def terminalObservation
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : BalancedTopLevelExecution.Result initialWorld root invocation) :
    Option
      (ObservedStatus × (Option Word × Option Word)) :=
  match observedStatus result, result.finalWorld? with
  | some status, some world =>
      some (status,
        (world.balance? callerAddress, world.balance? targetAddress))
  | _, _ => none

private def zeroAbsentCallerRun :=
  BalancedTopLevelExecution.run contract returnedInvocation installed
    emptyRegistry completionFuel

private def zeroValueKeepsLegacyExecution : Bool :=
  initialWorld.balance? callerAddress == none &&
    observedStatus zeroAbsentCallerRun ==
      some (.completed (.returned (encodeWordBytesBE returnPayload))) &&
    finalBalance? zeroAbsentCallerRun callerAddress == some none &&
    match zeroAbsentCallerRun.finalWorld? with
    | none => false
    | some finalWorld =>
        storageValueAt? finalWorld targetAddress targetSlot == some writtenValue

private def returnedRun :=
  runWithBalances returningContract ten three one completionFuel

private def nonzeroReturnCommitsTransfer : Bool :=
  observedStatus returnedRun ==
      some (.completed (.returned (encodeWordBytesBE returnPayload))) &&
    finalBalance? returnedRun callerAddress == some (some nine) &&
    finalBalance? returnedRun targetAddress == some (some four) &&
    committedBalanceChangesMatch returnedRun callerAddress
      (some (some ten, some nine)) (some (some three, some four))

private def revertedRun :=
  runWithBalances contract ten three one completionFuel

private def rootRevertRollsBackTransfer : Bool :=
  observedStatus revertedRun ==
      some (.completed (.reverted (encodeWordBytesBE revertPayload))) &&
    completedWorkingMatches revertedRun callerAddress
      (some nine) (some four) (some writtenValue) &&
    finalBalance? revertedRun callerAddress == some (some ten) &&
    finalBalance? revertedRun targetAddress == some (some three) &&
    committedBalanceChangesMatch revertedRun callerAddress none none &&
    match revertedRun.finalWorld? with
    | none => false
    | some finalWorld =>
        storageValueAt? finalWorld targetAddress targetSlot == some oldValue

private def trappedRun :=
  runWithBalances contract ten three two completionFuel

private def rootTrapRollsBackTransfer : Bool :=
  observedStatus trappedRun == some (.completed (.trapped trapCode)) &&
    completedWorkingMatches trappedRun callerAddress
      (some eight) (some five) (some writtenValue) &&
    finalBalance? trappedRun callerAddress == some (some ten) &&
    finalBalance? trappedRun targetAddress == some (some three) &&
    committedBalanceChangesMatch trappedRun callerAddress none none &&
    match trappedRun.finalWorld? with
    | none => false
    | some finalWorld =>
        storageValueAt? finalWorld targetAddress targetSlot == some oldValue

private def absentSenderRejected : Bool :=
  rejectedMatches
    (runWithoutCaller returningContract three callerAddress one completionFuel)
    .senderAbsent callerAddress targetAddress none (some three)

private def insufficientSenderRejected : Bool :=
  rejectedMatches
    (runWithBalances returningContract zero three one completionFuel)
    .insufficientBalance callerAddress targetAddress (some zero) (some three)

private def overflowingRecipientRejected : Bool :=
  rejectedMatches
    (runWithBalances returningContract ten Word.maximum one completionFuel)
    .recipientOverflow callerAddress targetAddress
    (some ten) (some Word.maximum)

private def fundedSelfCallIsBalanceIdentity : Bool :=
  let result :=
    runWithoutCaller returningContract three targetAddress one completionFuel
  observedStatus result ==
      some (.completed (.returned (encodeWordBytesBE returnPayload))) &&
    finalBalance? result targetAddress == some (some three) &&
    committedBalanceChangesMatch result targetAddress none none

private def unfundedSelfCallRejected : Bool :=
  rejectedMatches
    (runWithoutCaller returningContract zero targetAddress one completionFuel)
    .insufficientBalance targetAddress targetAddress (some zero) (some zero)

private def splitStart :=
  runWithBalances returningContract ten three one 0

private def resumed :=
  BalancedTopLevelExecution.resumeWithFuel splitStart completionFuel

private def oneShot :=
  runWithBalances returningContract ten three one completionFuel

private def zeroFuelRetainsSingleTransfer : Bool :=
  (observedStatus splitStart).isNone && splitStart.finalWorld?.isNone &&
    match splitStart.view with
    | .rejected _ => false
    | .execution execution =>
        match execution.view with
        | .completed _ => false
        | .outOfFuel _ (.root frame) _ =>
            let working := frame.context.context.values.working.1
            working.balance? callerAddress == some nine &&
              working.balance? targetAddress == some four
        | .outOfFuel _ (.child _) _ => false

private def resumedMatchesOneShotWithoutDoubleTransfer : Bool :=
  terminalObservation resumed == terminalObservation oneShot &&
    terminalObservation resumed ==
      some (.completed (.returned (encodeWordBytesBE returnPayload)),
        (some nine, some four)) &&
    committedBalanceChangesMatch resumed callerAddress
      (some (some ten, some nine)) (some (some three, some four))

private def allScenarios : Bool :=
  zeroValueKeepsLegacyExecution &&
    nonzeroReturnCommitsTransfer &&
    rootRevertRollsBackTransfer &&
    rootTrapRollsBackTransfer &&
    absentSenderRejected &&
    insufficientSenderRejected &&
    overflowingRecipientRejected &&
    fundedSelfCallIsBalanceIdentity &&
    unfundedSelfCallRejected &&
    zeroFuelRetainsSingleTransfer &&
    resumedMatchesOneShotWithoutDoubleTransfer

private theorem compileTimeBalancedTopLevelScenarios :
    allScenarios = true := by
  native_decide

def testAdr0147BalancedTopLevelExecution : IO Unit := do
  assertTrue zeroValueKeepsLegacyExecution
    "zero call value did not preserve legacy execution with an absent caller"
  assertTrue nonzeroReturnCommitsTransfer
    "root return did not commit the exact preflight debit and credit"
  assertTrue rootRevertRollsBackTransfer
    "root revert did not roll balance and storage back to the initial world"
  assertTrue rootTrapRollsBackTransfer
    "root trap did not roll balance and storage back to the initial world"
  assertTrue absentSenderRejected
    "an absent sender was not rejected before Core execution"
  assertTrue insufficientSenderRejected
    "an insufficient sender balance was not rejected atomically"
  assertTrue overflowingRecipientRejected
    "recipient overflow was not rejected atomically"
  assertTrue fundedSelfCallIsBalanceIdentity
    "a funded self-call changed its account balance"
  assertTrue unfundedSelfCallRejected
    "an unfunded self-call bypassed the sufficient-balance check"
  assertTrue zeroFuelRetainsSingleTransfer
    "fuel zero did not retain exactly one prepared balance transfer"
  assertTrue resumedMatchesOneShotWithoutDoubleTransfer
    "resumption differed from one-shot execution or repeated the transfer"

end Tests
