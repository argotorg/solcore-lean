import Solcore.Semantics.TopLevelExecutionResumption
import Solcore.Semantics.TopLevelStorageDeltaProperties
import Solcore.Semantics.TransactionHostStorageDriverFuelProperties

/-! Exact split-fuel laws for executable checked-Core top-level runs. -/

set_option autoImplicit false

namespace Solcore.Semantics.TopLevelExecution

namespace ValidatedRawResult

/-- A validated raw result is uniquely determined by its driver result. -/
theorem eq_of_result_eq
    {initialWorld : WorldState}
    {contract : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (left right : ValidatedRawResult initialWorld contract invocation)
    (result_eq : left.result = right.result) :
    left = right := by
  cases left with
  | mk leftResult leftTyping leftAddress leftDelta leftCheckpointJournal =>
      cases right with
      | mk rightResult rightTyping rightAddress rightDelta rightCheckpointJournal =>
          dsimp only at result_eq
          subst rightResult
          have delta_eq := TopLevelStorageDelta.unique leftDelta rightDelta
          subst rightDelta
          rfl

end ValidatedRawResult

/-- Classifying one driver result is independent of invariant witnesses. -/
theorem classifyRawResult_unique
    {initialWorld : WorldState}
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (left right : ValidatedRawResult initialWorld contract invocation)
    (result_eq : left.result = right.result) :
    classifyRawResult contract invocation left =
      classifyRawResult contract invocation right := by
  have raw_eq := ValidatedRawResult.eq_of_result_eq left right result_eq
  subst right
  rfl

/-- A terminal total result remains terminal under every additional budget. -/
@[simp] theorem resumeWithFuel_completed
    {initialWorld : WorldState}
    {contract : CheckedCoreContract}
    {invocation : TopLevelInvocation}
    (result : TopLevelTerminalResult initialWorld invocation.target)
    (additional : Nat) :
    resumeWithFuel
        (TopLevelRunResult.completed (contract := contract) result)
        additional =
      TopLevelRunResult.completed result := by
  rfl

/-- Resuming an initial run agrees exactly with one summed-fuel run. -/
theorem resumeWithFuel_run
    {initialWorld : WorldState}
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld invocation.target contract)
    (fuel additional : Nat) :
    resumeWithFuel (run contract invocation installed fuel) additional =
      run contract invocation installed (fuel + additional) := by
  cases prefixEq : validatedRawRun contract invocation installed fuel with
  | mk result resultTyping storageAddress_eq delta checkpointJournal_eq =>
      cases result with
      | mk context outcome =>
          cases outcome with
          | done value store =>
              have rawPrefixEq :
                  rawRun contract invocation installed fuel =
                    ⟨context, .done value store⟩ := by
                simpa [validatedRawRun] using
                  congrArg ValidatedRawResult.result prefixEq
              have summedEq :
                  rawRun contract invocation installed (fuel + additional) =
                    ⟨context, .done value store⟩ := by
                apply contract.code.runWithTransactionStorage_done_stable
                  (context := initialTransactionContext installed)
                  (inputs := invocation.executionInputs)
                  (by simpa [rawRun] using rawPrefixEq)
                omega
              have validatedEq :
                  validatedRawRun contract invocation installed fuel =
                    validatedRawRun contract invocation installed
                      (fuel + additional) := by
                apply ValidatedRawResult.eq_of_result_eq
                simpa [validatedRawRun] using rawPrefixEq.trans summedEq.symm
              have decodedNeNone :
                  contract.decodeCompletion? value ≠ none := by
                obtain ⟨_world, _storeTyping, valueTyping⟩ := resultTyping
                apply contract.entryProfile.decode?_ne_none_of_hasType
                rw [← contract.resultType_eq]
                exact valueTyping
              unfold run
              rw [← validatedEq, prefixEq]
              unfold classifyRawResult
              dsimp only [ValidatedRawResult.result,
                ValidatedRawResult.workingDelta]
              split
              · rfl
              · rename_i decodedEq
                exact False.elim (decodedNeNone decodedEq)
          | outOfFuel exhausted =>
              have rawPrefixEq :
                  rawRun contract invocation installed fuel =
                    ⟨context, .outOfFuel exhausted⟩ := by
                simpa [validatedRawRun] using
                  congrArg ValidatedRawResult.result prefixEq
              have summedEq :
                  rawRun contract invocation installed (fuel + additional) =
                    TransactionHostStorageDriver.run context
                      invocation.executionInputs
                      additional exhausted := by
                apply TransactionHostStorageDriver.run_additional_of_outOfFuel
                  (context := initialTransactionContext installed)
                  (nextContext := context)
                  (inputs := invocation.executionInputs)
                  (fuel := fuel)
                  (additional := additional)
                  (state := Core.State.initial contract.code.program.body
                    Core.hostEnvironment)
                  (exhausted := exhausted)
                simpa [rawRun,
                  CheckedHostCoreProgram.runWithTransactionStorage] using
                  rawPrefixEq
              have resumedEq :
                  validatedResumedRawResult context exhausted storageAddress_eq
                      resultTyping delta checkpointJournal_eq additional =
                    validatedRawRun contract invocation installed
                      (fuel + additional) := by
                apply ValidatedRawResult.eq_of_result_eq
                simpa [validatedResumedRawResult, validatedRawRun] using
                  summedEq.symm
              unfold run
              rw [prefixEq]
              change
                classifyRawResult contract invocation
                    (validatedResumedRawResult context exhausted
                      storageAddress_eq resultTyping delta checkpointJournal_eq
                      additional) =
                  classifyRawResult contract invocation
                    (validatedRawRun contract invocation installed
                      (fuel + additional))
              rw [resumedEq]
          | fault error faultState =>
              exact False.elim resultTyping

/-- Adding zero fuel to an actual initial run leaves its total result unchanged. -/
@[simp] theorem resumeWithFuel_run_zero
    {initialWorld : WorldState}
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld invocation.target contract)
    (fuel : Nat) :
    resumeWithFuel (run contract invocation installed fuel) 0 =
      run contract invocation installed fuel := by
  simpa using resumeWithFuel_run contract invocation installed fuel 0

/-- Repeated resumptions of an initial run agree with one total fuel budget. -/
theorem resumeWithFuel_run_add
    {initialWorld : WorldState}
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld invocation.target contract)
    (fuel first second : Nat) :
    resumeWithFuel
        (resumeWithFuel (run contract invocation installed fuel) first)
        second =
      run contract invocation installed (fuel + first + second) := by
  rw [resumeWithFuel_run, resumeWithFuel_run]

end Solcore.Semantics.TopLevelExecution
