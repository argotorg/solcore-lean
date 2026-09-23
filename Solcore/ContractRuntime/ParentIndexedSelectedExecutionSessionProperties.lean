import Solcore.ContractRuntime.ParentIndexedSelectedExecutionSessionResumption

/-! Canonicality and fuel algebra for certified selected sessions. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ParentIndexedSelectedExecutionSession

universe u v w

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

/-- Computational fields determine a certified session; its proof is irrelevant. -/
@[ext] theorem ext
    (left right : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (initialization : left.initialization = right.initialization)
    (storageAddress : left.storageAddress = right.storageAddress)
    (inputs : left.inputs = right.inputs)
    (doneOutcome : left.doneOutcome = right.doneOutcome)
    (providedFuel : left.providedFuel = right.providedFuel)
    (result : left.result = right.result) :
    left = right := by
  cases left
  cases right
  cases initialization
  cases storageAddress
  cases inputs
  cases doneOutcome
  cases providedFuel
  cases result
  rfl

/-- A certified session is exactly the canonical start at its stored budget. -/
theorem eq_start
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking) :
    session = start session.initialization session.storageAddress
      session.inputs session.doneOutcome session.providedFuel := by
  apply ext <;> simp
  exact session.result_eq_run

/-- Resuming a session is the canonical one-shot session at summed fuel. -/
theorem resumeWithFuel_eq_start
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (additional : Nat) :
    session.resumeWithFuel additional =
      start session.initialization session.storageAddress session.inputs
        session.doneOutcome (session.providedFuel + additional) := by
  exact eq_start (session.resumeWithFuel additional)

/-- Starting and then resuming agrees as a complete certified value. -/
theorem start_resumeWithFuel
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason)
    (providedFuel additional : Nat) :
    (start initialization storageAddress inputs doneOutcome providedFuel).resumeWithFuel
        additional =
      start initialization storageAddress inputs doneOutcome
        (providedFuel + additional) :=
  resumeWithFuel_eq_start _ additional

/-- Offering zero additional budget preserves the entire certified session. -/
@[simp] theorem resumeWithFuel_zero
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking) :
    session.resumeWithFuel 0 = session := by
  rw [resumeWithFuel_eq_start]
  simpa using (eq_start session).symm

/-- Two closed resumptions equal one resumption by their summed budget. -/
theorem resumeWithFuel_add
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (first second : Nat) :
    (session.resumeWithFuel first).resumeWithFuel second =
      session.resumeWithFuel (first + second) := by
  apply ext <;>
    simp only [resumeWithFuel_initialization, resumeWithFuel_storageAddress,
      resumeWithFuel_inputs, resumeWithFuel_doneOutcome,
      resumeWithFuel_providedFuel, resumeWithFuel_result]
  · rw [Nat.add_assoc]
  · exact ParentIndexedSelectedExecutionResult.resumeWithFuel_add
      session.result session.initialization session.inputs
      session.doneOutcome first second

end Solcore.ContractRuntime.ParentIndexedSelectedExecutionSession
