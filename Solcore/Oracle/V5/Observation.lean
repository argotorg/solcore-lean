import Solcore.Oracle.V5.Input
import Solcore.ContractRuntime.BalancedTopLevelExecution
import Solcore.Oracle.V5.Wire.Scalar

/-! Total Oracle v5 observations of terminal balanced execution. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5

open Solcore.ContractRuntime

/-- The four terminal outcomes published by the execution Oracle. -/
inductive TerminalOutcome where
  | preflightRejected (reason : BalanceTransferFailure)
  | returned (returndata : Bytes)
  | reverted (revertdata : Bytes)
  | trapped (reason : Solcore.Core.Word)
  deriving BEq, DecidableEq

namespace TerminalOutcome

def ofStatus :
    Except BalanceTransferFailure (FrameOutcome Solcore.Core.Word) →
      TerminalOutcome
  | .error reason => .preflightRejected reason
  | .ok (.returned returndata) => .returned returndata
  | .ok (.reverted revertdata) => .reverted revertdata
  | .ok (.trapped reason) => .trapped reason

end TerminalOutcome

/-- One committed checked-Core word log. -/
structure LogObservation where
  emitter : Address
  topic : Solcore.Core.Word
  payload : Solcore.Core.Word
  deriving Repr, BEq, DecidableEq

namespace LogObservation

def ofSemantic (entry : CheckedCoreWordLog) : LogObservation := {
  emitter := entry.emitter
  topic := entry.topic
  payload := entry.payload
}

end LogObservation

/-- The rollback-selected journal, preserving chronology and duplicates. -/
structure JournalObservation where
  logs : List LogObservation
  createdAddresses : List Address
  deriving Repr, BEq, DecidableEq

namespace JournalObservation

def ofSemantic (journal : TransactionJournal) : JournalObservation := {
  logs := journal.logList.map LogObservation.ofSemantic
  createdAddresses := journal.createdContractList
}

end JournalObservation

/-- One pointwise initial/committed world observation. -/
inductive ProbeObservation where
  | accountPresence
      (address : Address)
      (initial committed : Bool)
  | storage
      (address : Address)
      (slot : Solcore.Core.Word)
      (initial committed : Option Solcore.Core.Word)
  | balance
      (address : Address)
      (initial committed : Option Solcore.Core.Word)
  | nonce
      (address : Address)
      (initial committed : Option Solcore.Core.Word)
  | code
      (address : Address)
      (initial committed : Option ContractId)
  deriving Repr, BEq, DecidableEq

/-- A package-owned reverse lookup for checked code observed in WorldState. -/
abbrev CodeIdResolver := Solcore.Core.Program → Option ContractId

private def resolveCode?
    (resolveCode : CodeIdResolver) :
    Option CheckedHostCoreProgram →
      Except InternalError (Option ContractId)
  | none => .ok none
  | some code =>
      match resolveCode code.program with
      | some id => .ok (some id)
      | none => .error .worldCodeReferenceInvariant

namespace ProbeObservation

/-- Observe one requested key at the exact endpoints carried by a delta. -/
def ofProbe
    {initialWorld finalWorld : WorldState}
    (resolveCode : CodeIdResolver)
    (delta : WorldStateDelta initialWorld finalWorld) :
    Probe → Except InternalError ProbeObservation
  | .accountPresence address =>
      let endpoints := delta.accountEndpoints address
      .ok (.accountPresence address endpoints.1.isSome endpoints.2.isSome)
  | .storage address slot =>
      let endpoints := delta.storageEndpoints address slot
      .ok (.storage address slot endpoints.1 endpoints.2)
  | .balance address =>
      let endpoints := delta.balanceEndpoints address
      .ok (.balance address endpoints.1 endpoints.2)
  | .nonce address =>
      let endpoints := delta.nonceEndpoints address
      .ok (.nonce address endpoints.1 endpoints.2)
  | .code address => do
      let endpoints := delta.codeEndpoints address
      let initial ← resolveCode? resolveCode endpoints.1
      let committed ← resolveCode? resolveCode endpoints.2
      .ok (.code address initial committed)

end ProbeObservation

/-- Exact observations for the caller-selected finite probe list. -/
structure StateObservation where
  probes : List ProbeObservation
  deriving Repr, BEq, DecidableEq

namespace StateObservation

private def observeAll
    {initialWorld finalWorld : WorldState}
    (resolveCode : CodeIdResolver)
    (delta : WorldStateDelta initialWorld finalWorld) :
    List Probe → Except InternalError (List ProbeObservation)
  | [] => .ok []
  | probe :: rest => do
      let observed ← ProbeObservation.ofProbe resolveCode delta probe
      let tail ← observeAll resolveCode delta rest
      .ok (observed :: tail)

def ofDelta
    {initialWorld finalWorld : WorldState}
    (resolveCode : CodeIdResolver)
    (delta : WorldStateDelta initialWorld finalWorld)
    (probes : List Probe) : Except InternalError StateObservation := do
  .ok { probes := ← observeAll resolveCode delta probes }

end StateObservation

/-- The complete terminal value beneath `solcore-contract-execution/v1`. -/
structure ExecutionObservation where
  outcome : TerminalOutcome
  journal : JournalObservation
  state : StateObservation
  deriving BEq, DecidableEq

/--
Total projection of a sealed balanced run. Fuel exhaustion deliberately has no
fabricated terminal observation, while an impossible package/code mismatch is
kept distinct from semantic execution.
-/
inductive ExecutionProjection where
  | executed (observation : ExecutionObservation)
  | outOfFuel
  | internalError (error : InternalError)
  deriving BEq, DecidableEq

namespace ExecutionProjection

private def ofTerminal
    {initialWorld finalWorld : WorldState}
    (resolveCode : CodeIdResolver)
    (probes : List Probe)
    (status : Except BalanceTransferFailure (FrameOutcome Solcore.Core.Word))
    (journal : TransactionJournal)
    (delta : WorldStateDelta initialWorld finalWorld) : ExecutionProjection :=
  match StateObservation.ofDelta resolveCode delta probes with
  | .error error => .internalError error
  | .ok state => .executed {
      outcome := TerminalOutcome.ofStatus status
      journal := JournalObservation.ofSemantic journal
      state := state
    }

/--
Project every constructor of the sealed balanced executor without inspecting
or reconstructing its private proof payloads.
-/
def ofBalancedResult
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (resolveCode : CodeIdResolver)
    (probes : List Probe)
    (result :
      BalancedTopLevelExecution.Result initialWorld rootContract
        rootInvocation) : ExecutionProjection :=
  match result.view with
  | .rejected rejected =>
      ofTerminal resolveCode probes (.error rejected.failure)
        rejected.committedJournal rejected.committedDelta
  | .execution execution =>
      match execution.view with
      | .completed terminal =>
          ofTerminal resolveCode probes (.ok terminal.outcome)
            terminal.committedJournal terminal.committedDelta
      | .outOfFuel _environment _mode _reachable => .outOfFuel

end ExecutionProjection

end Solcore.Oracle.V5

/-!
## Consolidated module: `Solcore.Oracle.V5.ObservationValidity`
-/

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

/-!
## Consolidated module: `Solcore.Oracle.V5.ObservationCodec`
-/

/-! Canonical JSON encoding for total Oracle v5 execution observations. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5

open Solcore.ContractRuntime

/-- Encode one runtime address with its exact 160-bit lowercase spelling. -/
def encodeAddress (address : Address) : Lean.Json :=
  Wire.encodeAddress address

/-- Encode one Core word with its exact 256-bit lowercase spelling. -/
def encodeWord (word : Solcore.Core.Word) : Lean.Json :=
  Wire.encodeWord word

/-- Encode an arbitrary byte sequence with two lowercase digits per byte. -/
def encodeBytes (bytes : Bytes) : Lean.Json :=
  Wire.encodeBytes bytes

/-- Contract identifiers have already passed the closed v5 grammar. -/
def encodeContractId (id : ContractId) : Lean.Json :=
  id.value

private def encodeOptional {α : Type}
    (encode : α → Lean.Json) : Option α → Lean.Json
  | none => .null
  | some value => encode value

def encodeBalanceTransferFailure : BalanceTransferFailure → Lean.Json
  | .senderAbsent => "senderAbsent"
  | .recipientAbsent => "recipientAbsent"
  | .insufficientBalance => "insufficientBalance"
  | .recipientOverflow => "recipientOverflow"

/-- Encode all four terminal outcomes without an ABI-length assumption. -/
def encodeTerminalOutcome : TerminalOutcome → Lean.Json
  | .preflightRejected reason => .mkObj [
      ("kind", "preflightRejected"),
      ("reason", encodeBalanceTransferFailure reason)
    ]
  | .returned returndata => .mkObj [
      ("kind", "returned"),
      ("returndata", encodeBytes returndata)
    ]
  | .reverted revertdata => .mkObj [
      ("kind", "reverted"),
      ("revertdata", encodeBytes revertdata)
    ]
  | .trapped reason => .mkObj [
      ("kind", "trapped"),
      ("reason", encodeWord reason)
    ]

def encodeLogObservation (log : LogObservation) : Lean.Json :=
  .mkObj [
    ("emitter", encodeAddress log.emitter),
    ("topic", encodeWord log.topic),
    ("payload", encodeWord log.payload)
  ]

def encodeJournalObservation (journal : JournalObservation) : Lean.Json :=
  .mkObj [
    ("logs", .arr <| journal.logs.toArray.map encodeLogObservation),
    ("createdAddresses",
      .arr <| journal.createdAddresses.toArray.map encodeAddress)
  ]

/-- Encode every probe while preserving the requested order and null endpoints. -/
def encodeProbeObservation : ProbeObservation → Lean.Json
  | .accountPresence address initial committed => .mkObj [
      ("kind", "accountPresence"),
      ("address", encodeAddress address),
      ("initial", initial),
      ("committed", committed)
    ]
  | .storage address slot initial committed => .mkObj [
      ("kind", "storage"),
      ("address", encodeAddress address),
      ("slot", encodeWord slot),
      ("initial", encodeOptional encodeWord initial),
      ("committed", encodeOptional encodeWord committed)
    ]
  | .balance address initial committed => .mkObj [
      ("kind", "balance"),
      ("address", encodeAddress address),
      ("initial", encodeOptional encodeWord initial),
      ("committed", encodeOptional encodeWord committed)
    ]
  | .nonce address initial committed => .mkObj [
      ("kind", "nonce"),
      ("address", encodeAddress address),
      ("initial", encodeOptional encodeWord initial),
      ("committed", encodeOptional encodeWord committed)
    ]
  | .code address initial committed => .mkObj [
      ("kind", "code"),
      ("address", encodeAddress address),
      ("initial", encodeOptional encodeContractId initial),
      ("committed", encodeOptional encodeContractId committed)
    ]

/-- State observations always carry the fixed v1 schema marker. -/
def encodeStateObservation (state : StateObservation) : Lean.Json :=
  .mkObj [
    ("schema", stateObservationSchema),
    ("probes", .arr <| state.probes.toArray.map encodeProbeObservation)
  ]

private def encodeExecutionObservationValue
    (observation : ExecutionObservation) : Lean.Json :=
  .mkObj [
    ("outcome", encodeTerminalOutcome observation.outcome),
    ("journal", encodeJournalObservation observation.journal),
    ("state", encodeStateObservation observation.state)
  ]

/-- Encode the complete value beneath an `executed` verdict. -/
def encodeExecutionObservation
    (observation : ValidExecutionObservation) : Lean.Json :=
  .mkObj [
    ("schema", executionSchema),
    ("value", encodeExecutionObservationValue observation.value)
  ]

end Solcore.Oracle.V5
