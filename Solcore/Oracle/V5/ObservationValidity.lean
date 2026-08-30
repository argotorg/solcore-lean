import Solcore.Oracle.V5.Observation

/-! Executable rollback invariants for published Oracle v5 observations. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5

namespace ProbeObservation

/-- A rollback-selected probe must expose the same endpoint twice. -/
def EndpointsEqual : ProbeObservation → Prop
  | .accountPresence _ initial committed => initial = committed
  | .storage _ _ initial committed => initial = committed
  | .balance _ initial committed => initial = committed
  | .nonce _ initial committed => initial = committed
  | .code _ initial committed => initial = committed

def endpointsEqual : ProbeObservation → Bool
  | .accountPresence _ initial committed => decide (initial = committed)
  | .storage _ _ initial committed => decide (initial = committed)
  | .balance _ initial committed => decide (initial = committed)
  | .nonce _ initial committed => decide (initial = committed)
  | .code _ initial committed => decide (initial = committed)

@[simp] theorem endpointsEqual_eq_true_iff
    (probe : ProbeObservation) :
    probe.endpointsEqual = true ↔ probe.EndpointsEqual := by
  cases probe <;> simp [endpointsEqual, EndpointsEqual]

end ProbeObservation

namespace JournalObservation

/-- Failed root outcomes publish neither logs nor created addresses. -/
def Empty (journal : JournalObservation) : Prop :=
  journal.logs = [] ∧ journal.createdAddresses = []

def isEmpty (journal : JournalObservation) : Bool :=
  journal.logs.isEmpty && journal.createdAddresses.isEmpty

@[simp] theorem isEmpty_eq_true_iff
    (journal : JournalObservation) :
    journal.isEmpty = true ↔ journal.Empty := by
  simp [isEmpty, Empty]

end JournalObservation

namespace StateObservation

/-- Every selected probe observes an unchanged checkpoint endpoint. -/
def RollbackExact (state : StateObservation) : Prop :=
  ∀ probe ∈ state.probes, probe.EndpointsEqual

def isRollbackExact (state : StateObservation) : Bool :=
  state.probes.all ProbeObservation.endpointsEqual

@[simp] theorem isRollbackExact_eq_true_iff
    (state : StateObservation) :
    state.isRollbackExact = true ↔ state.RollbackExact := by
  simp [isRollbackExact, RollbackExact]

end StateObservation

namespace ExecutionObservation

/--
Return commits the working endpoint. Every other terminal outcome selects the
empty rollback journal and unchanged checkpoint probes.
-/
def Valid (observation : ExecutionObservation) : Prop :=
  match observation.outcome with
  | .returned _ => True
  | .preflightRejected _
  | .reverted _
  | .trapped _ =>
      observation.journal.Empty ∧ observation.state.RollbackExact

def isValid (observation : ExecutionObservation) : Bool :=
  match observation.outcome with
  | .returned _ => true
  | .preflightRejected _
  | .reverted _
  | .trapped _ =>
      observation.journal.isEmpty && observation.state.isRollbackExact

@[simp] theorem isValid_eq_true_iff
    (observation : ExecutionObservation) :
    observation.isValid = true ↔ observation.Valid := by
  cases observation with
  | mk outcome journal state =>
      cases outcome <;> simp [isValid, Valid]

end ExecutionObservation

/-- An execution observation whose rollback selection is part of its type. -/
structure ValidExecutionObservation where
  value : ExecutionObservation
  valid : value.Valid

namespace ValidExecutionObservation

instance : BEq ValidExecutionObservation :=
  ⟨fun left right => left.value == right.value⟩

/-- Seal exactly the observations accepted by the executable invariant. -/
def of? (value : ExecutionObservation) : Option ValidExecutionObservation :=
  if valid : value.isValid = true then
    some ⟨value,
      (ExecutionObservation.isValid_eq_true_iff value).mp valid⟩
  else
    none

@[simp] theorem of?_eq_some_iff
    (value : ExecutionObservation) :
    (of? value).isSome = true ↔ value.Valid := by
  simp [of?, ExecutionObservation.isValid_eq_true_iff]

end ValidExecutionObservation

end Solcore.Oracle.V5
