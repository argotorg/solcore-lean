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

{includeDocstring Solcore.Core.host_state_progress}

{name Solcore.Core.well_typed_host_state_never_faults}`well_typed_host_state_never_faults`

{includeDocstring Solcore.Core.well_typed_host_state_never_faults}

Storage address, code address, current address, caller, and call value have
distinct roles. Input data is explicit bytes. A handler does not consult an
ambient blockchain or silently invent account state.

# Return, revert, and trap

A {name Solcore.Semantics.FrameOutcome}`FrameOutcome` is returned data,
reverted data, or a trap reason. At the root execution boundary, return commits
the working world; revert and trap select the checkpoint. A balance-preflight
rejection happens before execution and also leaves the initial world intact.

{includeDocstring Solcore.Semantics.FrameOutcome.resolvedWorldState?}

For example, the revert branch can be checked directly:

```lean
open Solcore.Semantics

example (checkpoint working : WorldState) (data : Bytes) :
    FrameOutcome.resolvedWorldState? checkpoint working
      (.reverted (TrapReason := Unit) data)
      = some checkpoint := by
  rfl
```

The example selects a world; it does not execute a contract. The root runner
provides the surrounding execution and rollback policy.

# State and journals must agree

A rollback that restores storage but commits the failed frame's logs would
produce an inconsistent observation. The model resolves state and rollback
journals together.
{name Solcore.Semantics.FrameRunResult.resolvedWorldStateAndEffects?_reverted}`FrameRunResult.resolvedWorldStateAndEffects?_reverted`

{includeDocstring Solcore.Semantics.FrameRunResult.resolvedWorldStateAndEffects?_reverted}

{name Solcore.Semantics.TransactionJournal.logList_record_two}`TransactionJournal.logList_record_two`

{includeDocstring Solcore.Semantics.TransactionJournal.logList_record_two}

{includeDocstring Solcore.Semantics.TransactionJournal.createdContractList_record_two}

# Calls and value transfer

The published checked runtime supports a depth-one nested-call profile. The
scenario supplies a registry of checked contracts. Calls use an explicit Word
argument and a tagged result distinguishing the modeled success and failure
cases. A callee's failure and the caller's eventual outcome are separate events:
the caller can receive a failed call result and continue.

{includeDocstring Solcore.Semantics.BalancedTopLevelExecution.RejectedResult}

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

{includeDocstring Solcore.Semantics.BalancedTopLevelExecution.Result.finalWorld?}

{includeDocstring Solcore.Semantics.BalancedTopLevelExecution.resumeWithFuel}

Use the {ref "oracle"}[Oracle chapter] to construct the complete explicit
scenario and inspect the selected observations.
