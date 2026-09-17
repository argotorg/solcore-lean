import VersoManual
import Solcore.Core.HostProgress
import Solcore.Semantics.FrameStateResolutionProperties
import Solcore.Semantics.FrameRunEffectResolutionProperties
import Solcore.Semantics.TransactionJournalProperties
import Solcore.Semantics.BalancedTopLevelExecutionProperties

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Contracts, rollback, and external effects" =>
%%%
tag := "contracts"
file := "contracts"
%%%

A contract needs more than a pure expression evaluator. It needs an account
world, an invocation, and a definition of what storage reads, calls, logs, and
creation mean. Solcore keeps those inputs explicit so execution is reproducible.

# Typed requests connect Core to the host

{name Solcore.Core.HostFunction}`HostFunction` describes capabilities supplied
by a host: storage access, address and call-value queries, input-data access,
Word calls, creation, and Word logs. A Core application evaluates its argument
and emits a typed request. The host handles it and resumes the saved machine
continuation with a result of the required type.

{name Solcore.Core.host_state_progress}`host_state_progress`
allows a typed state to finish, take an ordinary step, or emit a host request.
{name Solcore.Core.well_typed_host_state_never_faults}`well_typed_host_state_never_faults`
excludes an immediate raw host-machine fault from such a state. These are
machine safety guarantees. They do not say that a requested contract call
must succeed or that a host operation cannot produce a defined failure.

Storage address, code address, current address, caller, and call value have
distinct roles. Input data is explicit bytes. A handler does not consult an
ambient blockchain or silently invent account state.

# Return, revert, and trap

A {name Solcore.Semantics.FrameOutcome}`FrameOutcome` is returned data,
reverted data, or a trap reason. At the root execution boundary, return commits
the working world; revert and trap select the checkpoint. A balance-preflight
rejection happens before execution and also leaves the initial world intact.

The generic frame helper deliberately stops short of selecting a trap policy.
Its return and revert laws are already precise:

```lean
open Solcore.Semantics

example (checkpoint working : WorldState) (data : Bytes) :
    FrameOutcome.resolvedWorldState? checkpoint working
      (.reverted (TrapReason := Unit) data)
      = some checkpoint := by
  rfl
```

{name Solcore.Semantics.FrameOutcome.resolvedWorldState?_returned}`FrameOutcome.resolvedWorldState?_returned`
selects the working world, while
{name Solcore.Semantics.FrameOutcome.resolvedWorldState?_trapped}`FrameOutcome.resolvedWorldState?_trapped`
returns `none`. Here `none` means the generic helper leaves trap disposition to
its caller. It does not mean that the root runner loses its rollback guarantee.
This distinction matters when reading a low-level theorem in isolation.

# State and journals must agree

A rollback that restores storage but commits the failed frame's logs would
produce an inconsistent observation. The model resolves state and rollback
journals together.
{name Solcore.Semantics.FrameRunResult.resolvedWorldStateAndEffects?_reverted}`FrameRunResult.resolvedWorldStateAndEffects?_reverted`
selects the checkpoint world and rollback journal, while retaining the working
trace component. A diagnostic trace can describe attempted work without making
that work a committed contract effect.

{name Solcore.Semantics.TransactionJournal.logList_record_two}`TransactionJournal.logList_record_two`
retains logs in order, including duplicates. Created-address observations are
recorded in completion order. These sequences are not sets that can be sorted
or deduplicated without changing the observation.

# Calls and value transfer

The published checked runtime supports a depth-one nested-call profile. The
scenario supplies a registry of checked contracts. Calls use an explicit Word
argument and a tagged result distinguishing the modeled success and failure
cases. A callee's failure and the caller's eventual outcome are separate events:
the caller can receive a failed call result and continue.

Value transfer has an explicit preflight. Missing accounts, insufficient funds,
or arithmetic constraints cannot be repaired by silently changing the initial
world. At the root boundary,
{name Solcore.Semantics.BalancedTopLevelExecution.RejectedResult.ofFailure_finalWorld}`RejectedResult.ofFailure_finalWorld`
proves that the canonical rejected result keeps the initial world, and
{name Solcore.Semantics.BalancedTopLevelExecution.RejectedResult.committedJournal_eq_empty}`RejectedResult.committedJournal_eq_empty`
proves it commits no rollback-scoped journal entries.

The restriction to depth one is a real interface boundary. These results do
not establish arbitrary recursive call stacks, unrestricted reentrancy, or all
EVM call modes.

# Creation and contract admission

Creation uses checked templates and an explicit address policy and registry.
The model tracks balances, nonces, installation, and the selected rollback
outcome. A created address becomes a committed observation only when the
transaction's outcome retains the corresponding journal.

A checked Core expression is not automatically an admitted contract. Entry
profiles impose an additional calling and result convention. The static Word
ABI profile uses a four-byte selector, one 32-byte argument, and one 32-byte
result. Dynamic ABI values, general events, and fallback or receive dispatch
are outside that profile.

# Exhaustion does not fabricate a transaction result

{name Solcore.Semantics.BalancedTopLevelExecution.Result.finalWorld?}`Result.finalWorld?`
returns no final world for an exhausted execution. The saved execution state
can be resumed. The root resumption laws preserve the actual context and
machine state, including work already performed; they do not replay the
invocation from scratch and duplicate effects.

Use the {ref "oracle"}[Oracle chapter] to construct the complete explicit
scenario and inspect the selected observations.
