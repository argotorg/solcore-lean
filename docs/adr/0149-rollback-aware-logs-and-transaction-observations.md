# ADR-0149: Rollback-aware checked-Core logs and transaction observations

- Status: Accepted
- Decision date: 2026-08-30
- Scope: ordered contract logs and successful-creation observations in executable checked-Core runs
- Implementation: Complete

## Context

ADR-0145 through ADR-0148 provide an executable checked-Core lifecycle with an
explicit initial `WorldState`, total return/revert/trap results, nested calls,
checked balance transfer, checked creation, and sealed fuel resumption. The
Before this milestone, the result was still incomplete for semantic
differential testing: a contract could not emit an observable log, and a
successful creation could not be enumerated without already knowing its
derived Address.

The repository already has two useful generic foundations. `FrameTrace`
records a finite chronological sequence, preserves duplicates, and exposes
ordered observation through `toList`. `FrameEffectJournal` separates a
rollback-scoped value from a trace that survives frame revert. ADR-0061 and
ADR-0075 deliberately reserve the rollback component for future contract logs;
the surviving trace is not a contract-log policy.

This milestone connects those foundations to the authoritative top-level and
one-level nested executors. It does not resume parser proof work and does not
publish a Wire or Oracle schema.

## Decision

### Internal word-log boundary

Add one ABI-independent internal value:

```lean
structure CheckedCoreWordLog where
  emitter : Address
  topic : Core.Word
  payload : Core.Word
```

The emitter is supplied by the active invocation's immutable
`ExecutionInputs.currentAddress`; Core cannot forge it as an argument. Topic
and payload remain raw Words. Multiple topics, arbitrary byte payloads, event
signatures, and encoding rules belong to the later ABI milestone.

Add one append-only checked-Core host capability:

```text
emitLogWord : (word × word) -> unit
```

Its `HostRequest` carries `(topic, payload)`. A well-typed request is total and
records exactly one log before returning unit. Only a raw ill-shaped Core
argument can produce the existing `invalidHostArgument` machine fault.

The capability is appended at host index 13. Indexes 0 through 12 retain their
meaning, both canonical host tables have length 14, and index 14 becomes the
first unbound position. The frozen Wire language continues to reject internal
host values and applications.

### Rollback-scoped transaction journal

Add one concrete rollback payload:

```lean
structure TransactionJournal where
  logs : FrameTrace CheckedCoreWordLog
  createdContracts : FrameTrace Address
```

Both fields start empty. A log appends to `logs`. A created Address appends to
`createdContracts` only after its initializer returns and checked runtime code
is installed successfully. Failed preflight and reverted or trapped
initializers do not create an observation.

Executable contexts use:

```text
FrameEffectJournal TransactionJournal Unit
```

The journal is the rollback component. The existing revert-surviving `trace`
component remains `Unit`; this milestone does not silently redefine diagnostic
trace policy as contract-log policy.

The generic storage driver remains available for legacy proof infrastructure
over code refined to the earlier 13 capabilities. Every production checked
execution path uses the transaction-aware handler. No authoritative executor
acknowledges `emitLogWord` while silently discarding it.

### Frame rules

The exact journal selection is:

| Boundary | Selected journal |
| --- | --- |
| root start | empty checkpoint and empty working journal |
| log emission | append once to the active working log trace |
| child start | seed checkpoint and working journal from the parent at suspension |
| child return | adopt the child's working journal |
| child revert or trap | restore the suspended parent's journal |
| initializer start | seed from the parent immediately before creation |
| initializer return | adopt initializer logs, then append the created Address |
| initializer revert or trap | restore the pre-creation parent journal while retaining the already-consumed creator nonce |
| root return | commit the working journal |
| root revert or trap | restore the root checkpoint journal |

Thus parent log `P`, returned-child log `C`, and resumed-parent log `R` are
observed as `[P, C, R]`. If the child reverts or traps, the committed sequence
is `[P, R]`. If a later root revert or trap occurs, neither sequence is
committed.

Successful creation observations are rollback-scoped in the same way. Two
successful creations are listed in completion order. A successful creation
followed by root revert or trap leaves the committed creation list empty.

World replacement and effect replacement must happen together when a returned
child or initializer is adopted. The existing world-only `rebaseWorking`
operation is not sufficient for those transitions.

### Total result observations

Terminal top-level and nested results expose both:

- the speculative working journal, and
- the externally committed journal selected by the root outcome.

The committed journal supplies ordered `logs` and `createdContracts` through
their `FrameTrace.toList` observations. It accompanies the existing terminal
outcome, return/revert/trap data, final WorldState, and queryable WorldState
delta. `WorldStateDelta` remains a persistent-state observation and does not
absorb logs.

An out-of-fuel result remains nonterminal. Its sealed active mode retains the
exact checkpoint and working journal. Resumption accepts only additional fuel,
so it cannot replace, erase, or replay an already-recorded observation.

Balanced top-level preflight rejection returns the initial WorldState,
identity state delta, and empty committed journal without beginning Core
execution.

## Required invariants and proofs

Implementation establishes:

- empty root checkpoint and working journals at initial execution;
- log emission changes only the working journal and preserves WorldState,
  selected Account, storage selector, and frame checkpoint;
- exact emitter, topic, payload, tail order, and duplicate retention;
- parent-journal seeding for child and initializer contexts;
- child return adoption and child revert/trap rollback;
- initializer return adoption plus one created-Address record;
- initializer revert/trap log rollback with nonce retention;
- root return commit and root revert/trap rollback;
- exact working and committed terminal observations;
- fixed-environment reachability with journal-bearing modes;
- one-shot/split-fuel equality including the complete journal; and
- terminal stability and zero/additive resumption without duplicate emission
  or duplicate creation recording.

The Core boundary also retains the standard host progress, suspension typing,
resume typing, transition safety, checked no-fault, registry order, and frozen
Wire rejection obligations.

## Required executable tests

Checked Core programs and boundary fixtures cover:

- two root logs, including a duplicate, in exact order with the root emitter;
- root log commit on return and empty committed logs on revert and trap;
- parent-before, returned-child, and parent-after order;
- removal of child logs on child revert and trap;
- removal of successful child logs after a later root revert or trap;
- initializer log adoption and successful created-Address observation;
- removal of initializer logs and creation observation on initializer revert
  and trap while retaining the creator nonce;
- removal of successful initializer effects after a later root revert or trap;
- identity journal on unavailable template, collision, insufficient balance,
  and top-level value-transfer rejection;
- sequential successful creations in completion order;
- root, child, initializer, and resumed-parent fuel boundaries;
- exhaustion immediately before and after emission, proving exactly-once
  resumption; and
- host indexes 0 through 12 unchanged, new index 13, length 14, first-unbound
  14, checker acceptance/rejection, raw machine suspension, and frozen-Wire
  rejection.

## Publication and exclusions

This is an internal executable-semantics milestone. It adds no source syntax,
parser rule or parser proof, Solidity event declaration policy, ABI signature,
selector, indexed-argument rule, multi-topic or byte-array log operation,
serialization, public Profile, public Oracle request/result, or Wire tag.

It also does not add gas charging, log limits, bloom filters, receipts, block
context, EVM revision selection, recursive calls, reentrancy, delegate/static
call policy, enumerable touched storage keys, or a revert-surviving external
call trace. Those omissions must not be described as implemented by this ADR.

The next milestone may connect ABI rules only after this word-level execution
path and its rollback behavior are complete. Public Oracle exposure remains a
separate final boundary.

## Commit discipline

Implementation is split into reviewable commits around 300 changed lines or
less: decision record; journal carrier and algebra; Core host boundary;
transaction-aware handler and contexts; top-level integration; child and
initializer integration; terminal observation API; executable regressions;
proof/audit closure; and documentation completion.

## Implementation outcome

The implementation now follows this decision end to end. `emitLogWord` is the
append-only capability at index 13; both canonical host tables have 14 entries
and index 14 is unbound. Frozen Wire v1 and v2 reject the internal host value.

Terminal execution returns ordered, duplicate-preserving logs and successful
creation Addresses alongside the existing state result. A returned root
commits its working journal. Root revert or trap selects the empty root
checkpoint. Returned children and initializers contribute their observations;
reverted or trapped ones do not. Initializer failure still retains the creator
nonce consumption fixed by ADR-0148, while failed balance and creation
preflights leave the journal unchanged.

Fuel exhaustion retains the exact journal-bearing scheduler mode. Zero-fuel,
split-fuel, and one-shot executions agree without repeating a log or successful
creation observation. Full builds, executable tests, strict Lean validation,
metadata checks, semantic-kernel checks, and diff hygiene pass.
