import Solcore.Semantics.HostStorageDriverProperties
import Solcore.Semantics.HostStorageDriverSafetyProperties
import Solcore.Semantics.TopLevelExecution

/-! Fixed-input resumption for exhausted checked-Core top-level execution. -/

set_option autoImplicit false

namespace Solcore.Semantics.TopLevelExecution

/-- Extend an exact initial-to-working delta through one handled execution suffix. -/
def extendWorkingDelta
    {initialWorld : WorldState}
    {target : Address}
    (context : HostStorageDriver.Context Unit Unit)
    (storageAddress_eq : context.context.storageAddress = target)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 target)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    TopLevelStorageDelta initialWorld
      (HostStorageDriver.run context inputs fuel state).context.context.values.working.1
      target := {
  initialAccount := delta.initialAccount
  finalAccount :=
    (HostStorageDriver.run context inputs fuel state).context.storageAccount
  initialAccount_present := delta.initialAccount_present
  finalAccount_present := by
    have finalAddress := HostStorageDriver.run_storageAddress
      context inputs fuel state
    have present :=
      (HostStorageDriver.run context inputs fuel state).context.storageAccount_present
    rw [finalAddress, storageAddress_eq] at present
    exact present
  code_preserved := by
    have currentPresent :
        context.context.values.working.1.account? target =
          some context.storageAccount := by
      simpa [storageAddress_eq] using context.storageAccount_present
    have finalAddress := HostStorageDriver.run_storageAddress
      context inputs fuel state
    have finalPresent :=
      (HostStorageDriver.run context inputs fuel state).context.storageAccount_present
    rw [finalAddress, storageAddress_eq] at finalPresent
    have currentAccount_eq :
        delta.finalAccount = context.storageAccount := by
      apply Option.some.inj
      exact delta.finalAccount_present.symm.trans currentPresent
    have suffix := HostStorageDriver.run_workingCode?
      context inputs fuel state target
    have suffix' :
        (HostStorageDriver.run context inputs fuel state).context.storageAccount.code? =
          context.storageAccount.code? := by
      change
        (HostStorageDriver.run context inputs fuel state).context.context.values.working.1.code?
            target =
          context.context.values.working.1.code? target at suffix
      simp [WorldState.code?, finalPresent, currentPresent] at suffix
      exact suffix
    exact suffix'.trans (by
      rw [← currentAccount_eq]
      exact delta.code_preserved)
  otherAccounts_preserved := by
    intro address different
    have differentCurrent : address ≠ context.context.storageAddress := by
      intro same
      apply different
      rw [← storageAddress_eq]
      exact same
    exact
      (HostStorageDriver.run_workingAccount?_of_ne_storageAddress
        context inputs fuel state address differentCurrent).trans
        (delta.otherAccounts_preserved address different)
}

/-- Package one resumed suffix with the invariants retained by exhaustion. -/
def validatedResumedRawResult
    {initialWorld : WorldState}
    {contract : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (context : HostStorageDriver.Context Unit Unit)
    (state : Core.State)
    (storageAddress_eq : context.context.storageAddress = invocation.target)
    (stateTyping :
      Core.HostStateHasType state contract.code.program.resultType
        contract.code.program.dataDefinitions)
    (delta :
      TopLevelStorageDelta initialWorld
        context.context.values.working.1 invocation.target)
    (additional : Nat) :
    ValidatedRawResult initialWorld contract invocation :=
  let result :=
    HostStorageDriver.run context invocation.executionInputs additional state
  {
    result := result
    resultTyping := by
      exact HostStorageDriver.run_hasType
        context invocation.executionInputs additional state stateTyping
    storageAddress_eq := by
      have preserved := HostStorageDriver.run_storageAddress
        context invocation.executionInputs additional state
      change result.context.context.storageAddress = invocation.target
      exact preserved.trans storageAddress_eq
    workingDelta :=
      extendWorkingDelta context storageAddress_eq delta
        invocation.executionInputs additional state
  }

/-- Resume only the out-of-fuel branch under the same contract invocation. -/
def resumeWithFuel
    {initialWorld : WorldState}
    {contract : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (execution : TopLevelRunResult initialWorld contract invocation)
    (additional : Nat) :
    TopLevelRunResult initialWorld contract invocation :=
  match execution with
  | .completed result => .completed result
  | .outOfFuel context state storageAddress_eq stateTyping delta =>
      classifyRawResult contract invocation
        (validatedResumedRawResult context state storageAddress_eq stateTyping
          delta additional)

end Solcore.Semantics.TopLevelExecution
