# ADR-0113: Present working storage Account total-write sparse preservation

- Status: Accepted
- Decision date: 2026-08-29
- Scope: preserve a distinct sparse-storage observation across one write
- Implementation: Complete

## Context

ADR-0112 distinguishes the two representation outcomes at the selected slot:
zero deletes the sparse entry, while a nonzero write stores `some value`.
Together with a distinct-slot preservation law, those cases form the complete
single-write truth table for `Account.storageValue?`.

The existing read-after-write laws preserve only the total value returned by a
read. They do not state that the underlying optional sparse entry is unchanged.
That representation fact should be available both at the Account boundary and
through the proven-present working-storage carrier.

## Decision

Publish exactly two named, non-simp laws. The base law is:

```lean
theorem Account.storageValue?_storageWrite_other
    (account : Account)
    (writtenSlot value otherSlot : Core.Word)
    (different : otherSlot ≠ writtenSlot) :
    (account.storageWrite writtenSlot value).storageValue? otherSlot =
      account.storageValue? otherSlot
```

The refined lift is:

```lean
theorem
    FrameCheckpointedWorkingPairWithPresentStorageAccount.storageValue?_writeStorage_other
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (writtenSlot value otherSlot : Core.Word)
    (different : otherSlot ≠ writtenSlot) :
    (context.writeStorage writtenSlot value).storageAccount.storageValue?
        otherSlot =
      context.storageAccount.storageValue? otherSlot
```

The inequality orientation matches the existing distinct-slot read laws. The
base theorem covers both zero deletion and nonzero insertion at the selected
slot: neither changes the optional entry at any other slot. The refined theorem
exposes exactly the same fact without unfolding the evidence carrier.

Keep both laws out of the simp registry. ADR-0111 already simplifies the
stored-Account projection first. Registering only the outer theorem would
therefore be shadowed, while registering the base theorem would broaden the
deliberately controlled Account sparse-observation policy. Callers select these
representation laws explicitly.

The Account proof splits on whether `value` is zero and unfolds only
`Account.storageWrite` and `Account.storageValue?`. The refined proof first
rewrites with ADR-0111 `storageAccount_writeStorage`, then applies the Account
law. Both public theorems must report exactly `[propext]`.

Add no combined conditional theorem, same-slot duplicate, helper, operation,
carrier, coercion, or instance. In particular, do not extend
`WorldStateProperties`: ADR-0056 fixes that module's public proof interface at
exactly twelve laws.

## Required regressions

Add one compile-only module with exactly two private examples. One applies the
fully qualified Account law directly; the other applies the fully qualified
refined law directly. Neither example may use `rfl`, simplification, unfolding,
ADR-0111's projection, or a lower-level substitute for the public theorem it is
testing.

This proof-only slice adds no runtime module, assertion, fixture, or runner
call. Existing WorldState storage-write runtime coverage already observes an
unchanged distinct sparse entry after a zero write. ADR-0107 separately runs
distinct-slot behavior through the total refined writer. The new laws add no
executable behavior.

## Dependency boundary

Create a small base module,
`AccountStorageWriteSparsePreservationProperties.lean`, importing only
`Solcore.Semantics.WorldState`. Keeping the Account theorem below refined-frame
types lets lower semantic layers reuse it without importing a carrier that they
do not need.

Create a refined module,
`FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteSparsePreservationProperties.lean`,
importing exactly the base module and ADR-0111's projection properties. It does
not need total reads, read-after-write, algebra, isolation, optional-write, or
ADR-0112 modules merely for chronology.

The semantic umbrella imports the base module immediately after
`WorldStateProperties` and the refined module immediately after ADR-0112's
presence module. The compile regression imports only the refined module. The
test runner places it immediately after ADR-0112's regression and before the
older address-bound optional read/write regression, with no call.

## What this slice does not decide

This is a one-write, one-distinct-slot representation law. Optional/total
multi-step coherence remains a separate decision. The theorem does not turn
sparse representation into a public serialization contract and does not expose
the private storage function.

The slice adds no Account creation, address role, authority, authorization,
provenance, lifetime, checkpoint, rollback, outcome, trace event, scheduling,
transaction, concurrency, reentrancy, atomicity, cost, or gas rule.

It adds no parser or source syntax, Core expression, Wire or Oracle field,
Profile, ABI, storage layout, serialization, or published observation.

## Staged implementation plan

Keep each of four commits below 300 changed lines: this decision and targeted
internal documentation; the two proof modules plus two semantic umbrella
imports; the exact two compile regressions plus one runner import and no call;
independent audit and completion evidence.

## Implementation record

The completed proof-only slice adds a 20-line Account properties module and a
27-line refined-carrier properties module, plus two semantic umbrella imports.
It publishes exactly the two required named non-simp laws and adds no helper,
operation, carrier, coercion, or instance. Both laws report exactly `[propext]`.

The 32-line compile-only module plus one runner import contains exactly two
private examples. Each uses a fully qualified direct application of its target
public theorem. The test layer adds no runtime declaration, assertion, fixture,
or runner call because existing suites already execute both underlying
distinct-slot behaviors.

The implementation commits are `28d8b35` (179 changed lines), `35c04a5` (49),
and `38774f3` (33), all below 300 changed lines; this completion update is the
fourth staged commit. Focused trust-zero checks, the 573-job full build, the
1034-job full test run, metadata and kernel checks, diff checks, declaration,
axiom, dependency, simp-registration, proof-masking, and critical-pair
inventories, and independent P0-P3 audits pass.

## Publication and consequences

This proof-only layer changes no frozen or published boundary. Semantic
consumers can state the full single-write sparse-storage behavior by name at
either the Account or proven-present carrier boundary while retaining the
existing controlled simp policy.
