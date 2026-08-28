# ADR-0101: Address-bound working storage-write algebra

- Status: Accepted
- Decision date: 2026-08-29
- Scope: specialize sequential storage-write algebra through one retained address
- Implementation: Planned

## Context

ADR-0093 stores one caller-supplied storage address beside checkpointed working
values and provides `writeStorage?` without a fresh address argument. ADR-0099
constructs that carrier directly from parent-indexed initialization. ADR-0100
now proves overwrite and independent-write commutation for the underlying
address-parameterized `writeWorkingStorage?` operation.

The retained-address operation does not yet expose those laws directly.
Callers must unfold two layers of `Option.map` wrapping before they can reason
about repeated writes. A thin proof lift can make the existing consumer
boundary complete without changing its data or behavior.

## Decision

Add no executable operation, carrier, instance, or public helper. Add exactly
one private proof helper that rewrites a bind of two retained-address writes
into the corresponding bind of two ADR-0092 writes, mapped back with the same
retained address.

Publish exactly two laws:

```lean
namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

theorem writeStorage?_overwrite
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot first second : Core.Word) :
    (context.writeStorage? slot first).bind
        (fun next => next.writeStorage? slot second) =
      context.writeStorage? slot second

theorem writeStorage?_commute_slots
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftSlot ≠ rightSlot) :
    (context.writeStorage? leftSlot leftValue).bind
        (fun next => next.writeStorage? rightSlot rightValue) =
      (context.writeStorage? rightSlot rightValue).bind
        (fun next => next.writeStorage? leftSlot leftValue)

end Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress
```

Both laws remain non-simp. Although overwrite reduces two writes to one, the
existing present-Account branch rule can simplify the first write before the
surrounding bind is visited. Registering both rules would therefore give
different normal forms depending on the available hypotheses. Slot
commutation also has no canonical rewrite direction.

The stored selector is unchanged across either successful sequence. A
two-write sequence returns `none` exactly when the retained address is absent
from the original working WorldState. In that case the first write fails; a
successful first write preserves the Account, so the second cannot newly fail.
The optional result carries no runtime-action provenance.

## Proof boundary

The private helper uses only the retained-address write definition and the
standard `Option.bind_map` and `Option.map_bind` equalities. The public proofs
reuse the matching ADR-0100 laws and do not unfold `WorldState.writeStorage?`
or repeat its Account-presence cases.

Both public laws must report exactly `[propext, Quot.sound]`. Add no classical
choice, custom axiom, unchecked declaration, second private helper, public
normalization theorem, or direct WorldState proof.

There is no distinct-address law at this boundary: `writeStorage?` always uses
the single retained selector and accepts no address argument. Add no new
address parameter merely to restate ADR-0100.

## Required compile regressions

Add exactly two private compile examples importing only the new properties
module:

1. same-slot overwrite through the named non-simp law; and
2. distinct-slot commutation through the named non-simp law.

There is no public test function, runtime declaration, runtime assertion,
fixture, helper, or runner call. The runner imports the compile-only module
exactly once.

## Dependency boundary

`FrameCheckpointedWorkingPairWithStorageAddressStorageWriteAlgebraProperties.lean`
imports exactly `FrameCheckpointedWorkingPairWithStorageAddress` and
`FrameCheckpointedWorkingPairStorageWriteAlgebraProperties`. It does not
import the address-bound branch properties or WorldState algebra directly.

The semantic umbrella imports the new module immediately after the ADR-0100
generic algebra and before WorldState read-after-write properties. The compile
regression imports only the new module; the runner adds one import and no call.
Existing definitions and theorem statements remain unchanged.

## What this slice does not decide

The retained address remains only a caller-supplied storage selector. It is not
a current contract, caller, callee, code address, owner, or authorized
principal. The laws add no address role, Account creation, checkpoint capture
or lifetime, rollback, outcome, trap, scheduling, transaction, concurrency,
reentrancy, atomicity, or external-effect policy.

Commutation does not claim that runtime actions may be reordered, execute
exactly once, have equal costs, or produce the same external observations. It
only equates the existing immutable optional-value expressions.

The slice adds no distinct-address duplicate, zero-deletion witness,
read-after-write law, address-preservation projection, initialization-specific
law, parser or source syntax, Core expression, Wire or Oracle field, Profile,
ABI, storage layout, gas rule, or published observation.

## Staged implementation plan

Keep each of four commits below 300 changed lines: this decision and targeted
internal documentation; the exact private helper and two laws plus one
umbrella import; the exact two compile regressions plus one runner import and
no call; independent audit and completion evidence.

## Publication and consequences

This proof-only layer is internal and changes no frozen or published boundary.
ADR-0093 writers, including values constructed by ADR-0099, can use the
sequential algebra without exposing their retained selector or nested carrier.

Further contract-entry inputs still wait for concrete consumers and lifetime
rules.
