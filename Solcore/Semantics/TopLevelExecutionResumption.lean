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
      let result :=
        HostStorageDriver.run context invocation.executionInputs additional state
      let nextDelta := extendWorkingDelta context storageAddress_eq delta
        invocation.executionInputs additional state
      match outcomeEq : result.outcome with
      | .done value store =>
          have typed := HostStorageDriver.run_hasType
            context invocation.executionInputs additional state stateTyping
          have decodedNeNone :
              contract.decodeCompletion? value ≠ none := by
            rw [outcomeEq] at typed
            obtain ⟨world, _storeTyping, valueTyping⟩ := typed
            apply contract.entryProfile.decode?_ne_none_of_hasType
            rw [← contract.resultType_eq]
            exact valueTyping
          match decodedEq : contract.decodeCompletion? value with
          | some outcome =>
              .completed
                (finalize invocation delta.initialAccount
                  delta.initialAccount_present result.context value store outcome
                  nextDelta)
          | none => False.elim (decodedNeNone decodedEq)
      | .outOfFuel exhausted =>
          have typed :
              Core.HostStateHasType exhausted
                contract.code.program.resultType
                contract.code.program.dataDefinitions := by
            have resultTyping := HostStorageDriver.run_hasType
              context invocation.executionInputs additional state stateTyping
            rw [outcomeEq] at resultTyping
            exact resultTyping
          have nextStorageAddress_eq :
              result.context.context.storageAddress = invocation.target := by
            have preserved := HostStorageDriver.run_storageAddress
              context invocation.executionInputs additional state
            change result.context.context.storageAddress = invocation.target
            exact preserved.trans storageAddress_eq
          .outOfFuel result.context exhausted nextStorageAddress_eq typed nextDelta
      | .fault error faultState =>
          False.elim
            (HostStorageDriver.run_ne_fault
              context invocation.executionInputs additional state faultState error
              stateTyping (by simpa [result] using outcomeEq))

end Solcore.Semantics.TopLevelExecution
