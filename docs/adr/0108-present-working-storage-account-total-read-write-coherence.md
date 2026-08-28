# ADR-0108: Present working storage Account total read/write coherence

- Status: Accepted
- Decision date: 2026-08-29
- Scope: prove same-slot and distinct-slot observations of total working writes
- Implementation: Complete

## Context

ADR-0106 exposes a total slot read from a proven-present working Account.
ADR-0107 synchronously updates that Account, its selected working-state entry,
and the evidence carrier without another lookup or failure branch.

The two operations now need their direct observational laws. These laws should
be stated on the refined carrier, delegate to the existing Account semantics,
and avoid reintroducing the older optional WorldState boundary.

## Decision

Publish exactly two simp laws:

```lean
namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

@[simp] theorem readStorage_writeStorage_same
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage slot value).readStorage slot = value

@[simp] theorem readStorage_writeStorage_other
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (writtenSlot value readSlot : Core.Word)
    (different : readSlot ≠ writtenSlot) :
    (context.writeStorage writtenSlot value).readStorage readSlot =
      context.readStorage readSlot

end Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
```

The same-slot law exposes the written value, including zero after deletion.
The distinct-slot law preserves the prior total read under the explicit
orientation `readSlot ≠ writtenSlot`. Both proofs apply the corresponding
Account laws to `context.storageAccount`; they perform no WorldState lookup and
do not inspect or transport the carrier's presence proof.

Both public laws must report exactly `[propext]` and be registered in the stated
simp direction. Their right-hand sides contain no write, so they terminate and
cannot form a simp loop. Add no reverse law, storage-value law, optional-read
law, context-projection law, zero/nonzero specialization, multi-write algebra,
helper, operation, carrier, coercion, or instance.

## Required regressions

Add one compile-only module with exactly three private examples. The first
names the same-slot law directly. The second names the distinct-slot law with
an arbitrary inequality hypothesis. The third composes the ADR-0106
conditional-read coherence with the new same-slot law so the updated context's
optional read is `some value`. No example may use broad simplification, so
existing Account or optional read/write laws cannot mask a missing refined law.

This proof-only slice adds no runtime module or assertion. ADR-0107's three
runtime assertions already execute nonzero, zero, sequential same-slot, and
distinct-slot cases through the total operation. The runner imports the new
compile-only module exactly once after ADR-0107's properties test and adds no
call.

## Dependency boundary

`FrameCheckpointedWorkingPairWithPresentStorageAccountStorageReadWriteProperties.lean`
imports exactly the ADR-0106 total-read definition, the ADR-0107 total-write
definition, and `WorldStateProperties` for the two Account laws. It does not
import the optional read/write coherence modules or either total-operation
properties module.

The semantic umbrella imports the new properties module immediately after
`WorldStateProperties`; both total operations are already imported above that
boundary. The compile regression imports the new module and ADR-0106 total-read
properties. The runner places it after ADR-0107's compile regression and before
the older address-bound optional read/write coherence regression. Existing
definitions and theorem statements remain unchanged.

## What this slice does not decide

These laws observe one total write through one total read. They add no new
mutation, Account creation, address role, current-contract identity, ownership,
authorization, provenance, lifetime, checkpoint, rollback, outcome, trace,
scheduling, transaction, concurrency, reentrancy, atomicity, cost, or gas rule.

Overwrite idempotence, two-write commutation, write preservation projections,
storage-value presence after zero or nonzero writes, and optional/total
multi-step coherence remain separate decisions.

This slice adds no parser or source syntax, Core expression, Wire or Oracle
field, Profile, ABI, storage layout, serialization, or published observation.

## Staged implementation plan

Keep each of four commits below 300 changed lines: this decision and targeted
internal documentation; the exact two laws plus one umbrella import; the exact
three compile regressions plus one runner import and no call; independent audit
and completion evidence.

## Implementation record

The completed proof-only slice adds a 37-line properties module plus one
semantic umbrella import. It publishes exactly the two required simp laws and
adds no helper, operation, carrier, coercion, or instance. Both laws report
exactly `[propext]`, are registered with the intended orientation, and
normalize nested writes without a loop.

The 48-line compile-only module plus one runner import contains exactly three
private examples. Two name the laws directly; the third composes ADR-0106
conditional-read coherence with the same-slot law. The test layer adds no
runtime or public declaration, fixture, helper, assertion, or runner call.

The implementation commits are `e251f1d` (161 changed lines), `5ef2212` (38),
and `bda0eba` (49), all below 300 changed lines; this completion update is the
fourth staged commit. Focused trust-zero checks, the 561-job full build, the
1012-job full test run, metadata and kernel checks, diff checks, declaration
and simp-registration inventories, named composition checks, and independent
P0-P3 audits pass.

## Publication and consequences

This proof-only layer changes no frozen or published boundary. Refined storage
consumers can normalize reads after a total write without unfolding the carrier
or returning to optional WorldState operations.
