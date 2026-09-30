import Solcore.ContractRuntime.CoreLanguageResult

/-! An ordinary sum failure after actual storage and log requests rolls back
through the existing top-level finalizer. Fuel exhaustion retains its checkpoint. -/

set_option autoImplicit false

namespace Tests.ContractLanguageResult

open Solcore.Core
open Solcore.ContractRuntime

private def word (value : Nat) : Word := Word.ofNatModulo value
private def target : Address := ⟨17, by decide⟩
private def caller : Address := ⟨19, by decide⟩
private def slot : Word := word 3
private def oldValue : Word := word 5
private def writtenValue : Word := word 7
private def topic : Word := word 11
private def payload : Word := word 13
private def reason : Word := word 23

private def account : Account := Account.empty.storageWrite slot oldValue
private def initialWorld : WorldState := WorldState.empty.putAccount target account
private theorem present : initialWorld.account? target = some account :=
  WorldState.account?_putAccount_same _ _ _

private def context : TransactionHostStorageDriver.Context :=
  ⟨⟨target, TopLevelExecution.initialTransactionValues initialWorld⟩, account, present⟩

private def invocation : TopLevelInvocation := {
  target := target
  caller := caller
  callValue := Word.zero
  inputData := { bytes := ByteArray.empty, size_lt_wordModulus := by decide }
}

private def failureBody : Expr := LanguageResult.failure .word (.word reason)
private def afterWrite : Expr := .letE
  (.apply (.var (HostFunction.emitLogWord.index + 1)) (.pair (.word topic) (.word payload)))
  failureBody

private def program : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE
    (.apply (.var HostFunction.storageWrite.index) (.pair (.word slot) (.word writtenValue)))
    afterWrite
}

private theorem program_checked : program.checkHost = true := by decide

private def initialState : State := State.initial program.body hostEnvironment

private def raw (fuel : Nat) : HostDriverResult TransactionHostStorageDriver.Context :=
  TransactionHostStorageDriver.run context invocation.executionInputs fuel initialState

/-- The caller's total entry decoder is supplied unchanged to the adapter. -/
private def successCodec (_ : TransactionHostStorageDriver.Context)
    (value : Value) (_ : Store) : FrameOutcome Word :=
  (CoreContractEntryProfile.returnWord.decode? value).getD (.trapped Word.zero)

private def adapted (fuel : Nat) : CoreLanguageResult.Result TransactionHostStorageDriver.Context :=
  CoreLanguageResult.decode successCodec (raw fuel)

private theorem adapted_typed (fuel : Nat) : (adapted fuel).outcome.HasType .word :=
  CoreLanguageResult.decode_hasType successCodec _
    (TransactionHostStorageDriver.run_hasType context invocation.executionInputs fuel initialState
      (.eval .nil (hostEnvironment_hasTypes [] [])
        (Program.checkHost_sound program_checked) .nil))

private theorem invalid_impossible (fuel : Nat) (value : Value) (store : Store) :
    (adapted fuel).outcome ≠ .invalidCarrier value store := by
  intro invalid
  have typed := adapted_typed fuel
  rw [invalid] at typed
  exact typed

private theorem internal_fault_impossible (fuel : Nat) (error : MachineFault) (state : State) :
    (adapted fuel).outcome ≠ .fault error state := by
  intro fault
  have typed := adapted_typed fuel
  rw [fault] at typed
  exact typed

private def expectedLog : CheckedCoreWordLog := {
  emitter := target
  topic := topic
  payload := payload
}

private def writeSuspension : HostSuspension :=
  ⟨.storageWrite slot writtenValue, [.letBody afterWrite hostEnvironment], []⟩

private def writeHandled :=
  TransactionHostStorageDriver.handleSuspension invocation.executionInputs context writeSuspension

private def logSuspension : HostSuspension :=
  ⟨.emitLogWord topic payload, [.letBody failureBody (.unit :: hostEnvironment)], []⟩

private def effectsHandled := TransactionHostStorageDriver.handleSuspension
  invocation.executionInputs writeHandled.1 logSuspension

private theorem raw_after_effects (fuel : Nat) :
    raw (fuel + 21) = TransactionHostStorageDriver.run effectsHandled.1
      invocation.executionInputs fuel effectsHandled.2 := by
  unfold raw
  rw [TransactionHostStorageDriver.run_of_suspended context invocation.executionInputs
    (fuel + 21) (fuel + 11) initialState writeSuspension (by rfl)]
  change TransactionHostStorageDriver.run writeHandled.1 invocation.executionInputs
    (fuel + 11) writeHandled.2 = _
  rw [TransactionHostStorageDriver.run_of_suspended writeHandled.1 invocation.executionInputs
    (fuel + 11) fuel writeHandled.2 logSuspension (by rfl)]
  rfl

private theorem raw_done : raw 40 =
    ⟨effectsHandled.1, .done (.inLeft .word (.word reason)) []⟩ := by
  rw [show 40 = 19 + 21 from rfl, raw_after_effects]
  exact TransactionHostStorageDriver.run_of_done _ _ _ _ _ _ (by rfl)

private theorem raw_checkpoint : raw 21 = ⟨effectsHandled.1, .outOfFuel effectsHandled.2⟩ := by
  rw [show 21 = 0 + 21 from rfl, raw_after_effects]
  exact TransactionHostStorageDriver.run_of_outOfFuel _ _ _ _ _ (by rfl)

private theorem adapted_trap : (adapted 40).outcome =
      .completed (.inLeft .word (.word reason)) [] (.trapped reason) := by
  simp only [adapted, raw_done]
  rfl

private theorem storage_written :
    (adapted 40).context.storageAccount.storageRead slot = writtenValue := by
  simp only [adapted, raw_done]
  rfl

private theorem log_recorded :
    (adapted 40).context.workingJournal.logList = [expectedLog] := by
  simp only [adapted, raw_done]
  rfl

private theorem checkpoint_retained (fuel : Nat) :
    (adapted fuel).context.context.values.checkpoint = context.context.values.checkpoint :=
  TransactionHostStorageDriver.run_checkpoint context invocation.executionInputs fuel initialState

/-- This is the same state-delta obligation used by the existing finalizer. -/
private def delta (fuel : Nat) : TopLevelStorageDelta initialWorld
    (adapted fuel).context.context.values.working.1 target where
  initialAccount := account
  finalAccount := (raw fuel).context.storageAccount
  initialAccount_present := present
  finalAccount_present := by
    have retained := TransactionHostStorageDriver.run_storageAddress context
      invocation.executionInputs fuel initialState
    have finalPresent := (raw fuel).context.storageAccount_present
    change (raw fuel).context.context.storageAddress = target at retained
    rw [retained] at finalPresent
    exact finalPresent
  code_preserved := by
    have finalPresent := (raw fuel).context.storageAccount_present
    have retained := TransactionHostStorageDriver.run_storageAddress context
      invocation.executionInputs fuel initialState
    change (raw fuel).context.context.storageAddress = target at retained
    have finalPresent' : (raw fuel).context.context.values.working.1.account? target =
        some (raw fuel).context.storageAccount := by
      rw [retained] at finalPresent
      exact finalPresent
    have preserved := TransactionHostStorageDriver.run_workingCode? context
      invocation.executionInputs fuel initialState target
    change (raw fuel).context.context.values.working.1.code? target =
      initialWorld.code? target at preserved
    simpa [WorldState.code?, finalPresent', present] using preserved
  otherAccounts_preserved := by
    intro address different
    exact TransactionHostStorageDriver.run_workingAccount?_of_ne_storageAddress
      context invocation.executionInputs fuel initialState address different

private theorem checkpoint_empty (fuel : Nat) :
    (adapted fuel).context.context.values.checkpoint.effects.rollback =
      TransactionJournal.empty := by
  rw [checkpoint_retained]
  rfl

private def finalized (fuel : Nat) : Option (TopLevelTerminalResult initialWorld target) :=
  (adapted fuel).finalize? invocation account present (delta fuel) (checkpoint_empty fuel)

private theorem failure_rolls_back :
    (finalized 40).map (·.finalWorld) = some initialWorld ∧
      (finalized 40).map (·.committedJournal) = some TransactionJournal.empty ∧
      (finalized 40).map (·.workingJournal.logList) = some [expectedLog] := by
  have final_eq : finalized 40 = some (TopLevelExecution.finalize invocation account present
      (adapted 40).context (.inLeft .word (.word reason)) [] (.trapped reason)
      (delta 40) (checkpoint_empty 40)) := by
    unfold finalized CoreLanguageResult.Result.finalize?
    rw [adapted_trap]
  rw [final_eq]
  exact ⟨rfl, congrArg some (checkpoint_empty 40), congrArg some log_recorded⟩

private theorem fuel_preserves_effects_without_finalizing :
    (adapted 21).outcome = .outOfFuel effectsHandled.2 ∧
      (adapted 21).context.storageAccount.storageRead slot = writtenValue ∧
      (adapted 21).context.workingJournal.logList = [expectedLog] ∧
      finalized 21 = none := by
  have exhausted : (adapted 21).outcome = .outOfFuel effectsHandled.2 := by
    simp only [adapted, raw_checkpoint]
    rfl
  refine ⟨exhausted, ?_, ?_, ?_⟩
  · simp only [adapted, raw_checkpoint]
    rfl
  · simp only [adapted, raw_checkpoint]
    rfl
  · unfold finalized CoreLanguageResult.Result.finalize?
    rw [exhausted]
    rfl

/-- A successful outer carrier hands the payload to the exact existing codec. -/
private theorem success_uses_existing_codec :
    CoreLanguageResult.decodeDone? successCodec context (.inRight .word (.word payload)) [] =
      CoreContractEntryProfile.returnWord.decode? (.word payload) := rfl

private theorem malformed_is_distinct :
    (CoreLanguageResult.decode successCodec ⟨context, .done .unit []⟩).outcome =
      .invalidCarrier .unit [] := rfl

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def test : IO Unit := do
  match (adapted 40).outcome with
  | .completed carrier store frame =>
      assertTrue (carrier == .inLeft .word (.word reason) && store == [] && frame == .trapped reason)
        "a returned language failure must retain its carrier and decode to the exact frame trap"
  | _ => throw (IO.userError "the checked language failure must complete after its host requests")
  assertTrue ((adapted 40).context.storageAccount.storageRead slot == writtenValue &&
      (adapted 40).context.workingJournal.logList == [expectedLog])
    "storage and log requests before the language failure must occur"
  match finalized 40 with
  | some result =>
      assertTrue ((result.finalWorld.account? target).map (·.storageRead slot) == some oldValue &&
          result.committedJournal.logList == [] && result.workingJournal.logList == [expectedLog])
        "the existing trap finalizer must roll back storage and committed logs while retaining working evidence"
  | none => throw (IO.userError "the completed language failure must have a terminal result")
  match (adapted 21).outcome with
  | .outOfFuel state =>
      assertTrue (state == effectsHandled.2 &&
          (adapted 21).context.storageAccount.storageRead slot == writtenValue &&
          (adapted 21).context.workingJournal.logList == [expectedLog])
        "fuel exhaustion must retain the exact post-effect Core state and host context"
  | _ => throw (IO.userError "21 fuel must stop before the language result completes")
  assertTrue (finalized 21 |>.isNone)
    "fuel exhaustion must not be finalized as a language failure or a completed frame"
  assertTrue (CoreLanguageResult.decodeDone? successCodec context
      (.inRight .word (.word payload)) [] == CoreContractEntryProfile.returnWord.decode? (.word payload))
    "the success branch must delegate to the existing entry codec unchanged"

end Tests.ContractLanguageResult
