import Solcore.Semantics.ParentIndexedFrameInitializationSelectedExecutionResumptionProperties
import Solcore.Semantics.ParentIndexedSelectedExecutionSession

/-! Closed resumption for certified parent-indexed selected sessions. -/

set_option autoImplicit false

namespace Solcore.Semantics.ParentIndexedSelectedExecutionSession

universe u v w

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

/--
Offer more fuel without accepting any replacement for the session's fixed
configuration. The stored proof is advanced by the actual-run split law.
-/
def resumeWithFuel
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (additional : Nat) : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking := {
  initialization := session.initialization
  storageAddress := session.storageAddress
  inputs := session.inputs
  doneOutcome := session.doneOutcome
  providedFuel := session.providedFuel + additional
  result := session.result.resumeWithFuel
    session.initialization session.inputs session.doneOutcome additional
  result_eq_run := by
    rw [session.result_eq_run]
    exact
      ParentIndexedFrameInitialization.runCodeWithStorageParentIndexedResult_resumeWithFuel
        session.initialization session.storageAddress session.inputs
        session.providedFuel additional session.doneOutcome
}

@[simp] theorem resumeWithFuel_initialization
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (additional : Nat) :
    (session.resumeWithFuel additional).initialization =
      session.initialization :=
  rfl

@[simp] theorem resumeWithFuel_storageAddress
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (additional : Nat) :
    (session.resumeWithFuel additional).storageAddress =
      session.storageAddress :=
  rfl

@[simp] theorem resumeWithFuel_inputs
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (additional : Nat) :
    (session.resumeWithFuel additional).inputs = session.inputs :=
  rfl

@[simp] theorem resumeWithFuel_doneOutcome
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (additional : Nat) :
    (session.resumeWithFuel additional).doneOutcome =
      session.doneOutcome :=
  rfl

@[simp] theorem resumeWithFuel_providedFuel
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (additional : Nat) :
    (session.resumeWithFuel additional).providedFuel =
      session.providedFuel + additional :=
  rfl

@[simp] theorem resumeWithFuel_result
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (additional : Nat) :
    (session.resumeWithFuel additional).result =
      session.result.resumeWithFuel session.initialization session.inputs
        session.doneOutcome additional :=
  rfl

/-- Every resumed session still denotes its fixed one-shot run exactly. -/
theorem resumeWithFuel_result_eq_run
    (session : ParentIndexedSelectedExecutionSession
      RollbackState Event TrapReason parentWorking)
    (additional : Nat) :
    (session.resumeWithFuel additional).result =
      session.initialization.runCodeWithStorageParentIndexedResult
        session.storageAddress session.inputs
        (session.providedFuel + additional) session.doneOutcome :=
  (session.resumeWithFuel additional).result_eq_run

end Solcore.Semantics.ParentIndexedSelectedExecutionSession
