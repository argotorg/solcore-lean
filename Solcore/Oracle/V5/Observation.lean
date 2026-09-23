import Solcore.Oracle.V5.Input
import Solcore.ContractRuntime.BalancedTopLevelExecution

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
