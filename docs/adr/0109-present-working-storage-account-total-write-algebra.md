# ADR-0109: Present working storage Account total-write algebra

- Status: Accepted
- Decision date: 2026-08-29
- Scope: normalize overwrite and commute distinct total working-storage writes
- Implementation: Complete

## Context

ADR-0107 makes a proven-present working-storage write total and returns another
coherent evidence carrier. ADR-0108 fixes the immediate read observations of
one such write. Sequential consumers can now remain entirely inside the total
carrier, but no public law yet normalizes repeated writes themselves.

The next algebraic boundary should lift the existing Account overwrite and
distinct-slot commutation laws without returning to optional WorldState
operations or exposing carrier construction details.

## Decision

Publish exactly two laws:

```lean
namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

@[simp] theorem writeStorage_overwrite
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot first second : Core.Word) :
    (context.writeStorage slot first).writeStorage slot second =
      context.writeStorage slot second

theorem writeStorage_commute_slots
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftSlot ≠ rightSlot) :
    (context.writeStorage leftSlot leftValue).writeStorage
        rightSlot rightValue =
      (context.writeStorage rightSlot rightValue).writeStorage
        leftSlot leftValue

end Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
```

The overwrite law is a simp rule because it removes one write and has one
canonical direction. The commutation law remains non-simp because its equality
is symmetric and no slot ordering policy exists.

Both proofs unfold only the total carrier write and reuse the existing Account
and WorldState update algebra. They preserve the whole returned carrier,
including its synchronized stored Account, working-state entry, selector,
checkpoint, journal, and new evidence.

Both laws must report exactly `[propext, Quot.sound]`. Add no helper, reverse
commutation law, three-write law, read observation, optional-write law,
projection law, operation, carrier, coercion, instance, or slot ordering.

## Required regressions

Add one compile-only module with exactly two private examples. The first names
the overwrite law directly. The second names the commutation law with an
arbitrary `leftSlot ≠ rightSlot` hypothesis. Neither example may use broad
simplification, so existing Account, WorldState, optional-write, or generated
equations cannot mask a missing refined-carrier law.

This proof-only slice adds no runtime module or assertion. ADR-0107 already
executes sequential same-slot overwrite and distinct-slot preservation, while
the new carrier equalities quantify over arbitrary contexts, slots, and values.
The runner imports the compile-only module exactly once after ADR-0108's test
and adds no call.

## Dependency boundary

`FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteAlgebraProperties.lean`
imports exactly the ADR-0107 total-write definition and
`WorldStateUpdateAlgebraProperties`. It does not import total reads,
read-after-write laws, optional-write algebra, or total-write coherence.

The semantic umbrella imports the new module immediately after
`WorldStateUpdateAlgebraProperties`. The compile regression imports only the
new module; the runner places it after ADR-0108's compile regression and before
the older address-bound optional read/write coherence regression. Existing
definitions and theorem statements remain unchanged.

## What this slice does not decide

These laws reorder or eliminate total writes only at one already selected,
proven-present Account. They add no Account creation, other-address write,
current-contract identity, address authority, ownership, authorization,
provenance, lifetime, checkpoint, rollback, outcome, trace, scheduling,
transaction, concurrency, reentrancy, atomicity, cost, or gas rule.

Non-selected Account isolation, individual structural preservation projections,
storage-value presence after zero or nonzero writes, and optional/total
multi-step coherence remain separate decisions.

This slice adds no parser or source syntax, Core expression, Wire field,
ABI, storage layout, serialization, or published observation.

## Staged implementation plan

Keep each of four commits below 300 changed lines: this decision and targeted
internal documentation; the exact two laws plus one umbrella import; the exact
two compile regressions plus one runner import and no call; independent audit
and completion evidence.

## Implementation record

The completed proof-only slice adds a 39-line properties module plus one
semantic umbrella import. It publishes exactly the two required laws and adds
no helper, operation, carrier, coercion, or instance. The overwrite law is a
simp rule, the commutation law is not, and both report exactly
`[propext, Quot.sound]`.

The 36-line compile-only module plus one runner import contains exactly two
private examples. Each applies its fully qualified public law directly, so
existing Account and WorldState algebra cannot mask a missing refined-carrier
declaration. The test layer adds no runtime or public declaration, fixture,
helper, assertion, or runner call.

The implementation commits are `2ae2256` (163 changed lines), `de4fd39` (40),
and `09aa0d0` (37), all below 300 changed lines; this completion update is the
fourth staged commit. Focused trust-zero checks, the 564-job full build, the
1016-job full test run, kernel checks, diff checks, declaration,
axiom, and simp-registration inventories, proof-masking checks, and independent
P0-P3 audit pass.

## Publication and consequences

This proof-only layer changes no frozen or published boundary. Sequential total
storage updates can be normalized without unfolding the evidence carrier or
reintroducing optional failure stages.
