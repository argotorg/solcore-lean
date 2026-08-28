# ADR-0105: Present working storage Account refinement

- Status: Accepted
- Decision date: 2026-08-29
- Scope: refine an address-bound working context with exact Account presence
- Implementation: Planned

## Context

ADR-0093 retains one storage selector beside checkpointed working values.
Its read and write operations remain conditional because the selected Account
may be absent from the working WorldState. ADR-0095 and ADR-0093 already expose
present-Account laws, but each consumer must carry the selected Account and its
lookup equality separately.

ADR-0096 anticipates a present-Account refinement before total frame-local
storage operations. The refinement must perform one working-state lookup,
retain the exact existing context, and make its evidence reusable without
creating an Account or assigning an address role.

## Decision

Add exactly one refinement carrier:

```lean
namespace Solcore.Semantics

universe u v

structure FrameCheckpointedWorkingPairWithPresentStorageAccount
    (RollbackState : Type u) (TraceState : Type v) : Type (max u v) where
  context :
    FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState
  storageAccount : Account
  storageAccount_present :
    context.values.working.1.account? context.storageAddress =
      some storageAccount

end Solcore.Semantics
```

The explicit `context` field retains the whole existing carrier without adding
promoted projections, a coercion, or duplicated address and values fields. The
evidence is indexed by that exact immutable context snapshot.

Add exactly one partial producer:

```lean
namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

def withPresentStorageAccount?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState) :
    Option
      (FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState) :=
  match present :
      context.values.working.1.account? context.storageAddress with
  | none => none
  | some account => some ⟨context, account, present⟩

end Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress
```

The producer consults only the working WorldState at the retained selector. It
returns `none` for an absent Account and otherwise stores the exact Account and
lookup evidence. It does not consult the checkpoint or substitute
`Account.empty`.

## Required proof interface

Publish exactly two simp branch laws:

```lean
@[simp] theorem withPresentStorageAccount?_of_absent
    {RollbackState : Type u} {TraceState : Type v}
    (context : FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (absent :
      context.values.working.1.account? context.storageAddress = none) :
    context.withPresentStorageAccount? = none

@[simp] theorem withPresentStorageAccount?_of_present
    {RollbackState : Type u} {TraceState : Type v}
    (context : FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (account : Account)
    (present :
      context.values.working.1.account? context.storageAddress = some account) :
    context.withPresentStorageAccount? =
      some ⟨context, account, present⟩
```

Both rules remove the producer under exclusive lookup hypotheses and have no
reverse form or loop. Their proofs split only the same lookup used by the
producer and add no helper or direct WorldState reasoning.

The carrier, its generated declarations, the producer and generated equation,
and both public laws must report exactly `[propext]`. Add no custom constructor,
coercion, instance, default, validity predicate, second producer, success
existence theorem, inverse, or equality between independently refined values.

## Required regressions

Add one definition-only runtime module with exactly three assertions:

1. a selected Account present only in the checkpoint remains unavailable when
   the working state contains only another Account;
2. a present empty selected working Account refines successfully and reads
   missing slots as zero while retaining context sentinels; and
3. two selectors over one working state recover their two exact, distinct
   Accounts and retain the original checkpoint and working journal.

The runtime module imports only the new definition, exposes one public test
function, and does not import the proof laws.

Add one compile-only module with exactly three private examples: the named
absent law, the named exact present result, and a conjunction showing that the
stored Account and evidence discharge the existing address-bound read and
write present laws. It imports the new properties plus only those two existing
properties modules. It adds no public or runtime declaration.

The runner imports both modules exactly once, calls the runtime test exactly
once, and adds no call for the compile-only module.

## Dependency boundary

`FrameCheckpointedWorkingPairWithPresentStorageAccount.lean` imports only
`FrameCheckpointedWorkingPairWithStorageAddress`.
`FrameCheckpointedWorkingPairWithPresentStorageAccountProperties.lean` imports
only the new definition.

The semantic umbrella imports both modules after ADR-0103 write coherence and
before the initialization storage-address adapter. The runner places both tests
after ADR-0103's compile regression and before address-bound write algebra.
Existing definitions and theorem statements remain unchanged.

## What this slice does not decide

Presence is local to the retained address in one immutable working-state
snapshot. A later transformed context needs new evidence. The carrier proves
nothing about checkpoint presence, currentness, account freshness, provenance,
ownership, authorization, invocation identity, or lifetime.

This slice adds no total read or write operation; those are the immediate
consumer slices after this refinement. It adds no Account creation, balance,
nonce, code, value transfer, call data, outcome, trace event, rollback,
scheduling, transaction, concurrency, reentrancy, atomicity, cost, or gas rule.

It adds no parser or source syntax, Core expression, Wire or Oracle field,
Profile, ABI, storage layout, serialization, or published observation.

## Staged implementation plan

Keep each of five commits below 300 changed lines: this decision and targeted
internal documentation; the exact carrier and producer plus one umbrella
import; the exact two laws plus one umbrella import; runtime and compile-only
regressions plus runner wiring; independent audit and completion evidence.

## Publication and consequences

This internal refinement changes no frozen or published boundary. Its evidence
feeds the existing present read and write laws immediately and will support
separate total read and write operations without repeating an absence branch.
