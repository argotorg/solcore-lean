# ADR-0102: Address-bound working storage-write preservation

- Status: Accepted
- Decision date: 2026-08-29
- Scope: stage-preserving structural observations of retained-address writes
- Implementation: Complete

## Context

ADR-0093 defines a conditional write on checkpointed working values carrying
one retained storage address. Its present-Account branch visibly rebuilds the
result with the same address, checkpoint, and working effect journal. The
absent branch returns `none`.

Those facts are currently available only after supplying an Account witness
and selecting a branch law. Consumers that compose the optional write result
cannot name the three preserved observations without repeating branch analysis.
ADR-0099 makes this gap relevant on the canonical initialization path, while
ADR-0101 now supports repeated writes on the same carrier.

## Decision

Add no executable operation, carrier, instance, or helper. Publish exactly
three stage-preserving observation laws:

```lean
namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

@[simp] theorem storageAddress_writeStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map
        (fun next => next.storageAddress) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => context.storageAddress)

@[simp] theorem checkpoint_writeStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map
        (fun next => next.values.checkpoint) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => context.values.checkpoint)

@[simp] theorem workingEffects_writeStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map
        (fun next => next.values.working.2) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => context.values.working.2)

end Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress
```

Each right side retains the original Account-presence stage. If the working
Account is absent, both sides are `none`. If it is present, the result is
`some` of the exact original address, checkpoint, or complete working effect
journal. The laws do not turn a conditional write into a total operation.

All three laws are simp rules. They remove a write-result projection in favor
of an Account lookup and constant observation. Existing absent and present
branch simp rules reach the same `none` or `some` normal form, so there is no
rewrite loop or divergent critical overlap.

## Proof boundary

Each proof performs only the two cases of the existing working Account lookup
and reuses the ADR-0093 branch laws. Add no private helper, direct WorldState
proof, custom axiom, classical choice, or unchecked declaration.

All three laws must report exactly `[propext]`. Do not add success-existence,
inverse, whole-result, or equality-of-carriers laws.

## Required compile regressions

Add exactly three private compile examples importing only the new properties
module:

1. the abstract address observation simplifies while retaining its unresolved
   Account-presence stage;
2. under a present-Account hypothesis, checkpoint observation simplifies to
   `some` of the exact original checkpoint; and
3. under an absent-Account hypothesis, working-effect observation simplifies
   to `none`.

There is no public test function, runtime declaration, runtime assertion,
fixture, helper, or runner call. The runner imports the compile-only module
exactly once.

## Dependency boundary

`FrameCheckpointedWorkingPairWithStorageAddressStorageWritePreservationProperties.lean`
imports only `FrameCheckpointedWorkingPairWithStorageAddressProperties`.

The semantic umbrella imports the new module immediately after those
address-bound branch properties and before the initialization adapter. The
compile regression imports only the new module; the runner adds one import and
no call. Existing definitions and theorem statements remain unchanged.

## What this slice does not decide

The working WorldState is not preserved as a whole: its selected Account may
change. Storage-value observations remain owned by ADR-0097, and sequential
write algebra remains owned by ADR-0101. Add no duplicate read, write,
overwrite, commutation, zero-deletion, or Account-presence law.

The retained address remains only a caller-supplied selector. The laws add no
current-contract identity, ownership, authorization, Account creation,
checkpoint capture or lifetime, rollback, outcome, trap, scheduling,
transaction, concurrency, reentrancy, atomicity, gas, or external-effect
policy.

They add no parser or source syntax, Core expression, Wire or Oracle field,
Profile, ABI, storage layout, serialization, or published observation.

## Staged implementation plan

Keep each of four commits below 300 changed lines: this decision and targeted
internal documentation; the exact three laws plus one umbrella import; the
exact three compile regressions plus one runner import and no call; independent
audit and completion evidence.

## Implementation record

The completed slice adds a 53-line properties module plus one semantic
umbrella import. It publishes exactly the three required simp observation laws
and adds no helper, executable operation, carrier, or instance. All three laws
report exactly `[propext]`.

A 48-line compile-only test module plus one runner import contains exactly
three private examples. The abstract address example exercises simp directly;
the present checkpoint and absent working-effect examples name their new law
before reducing the Account stage. This prevents the older branch laws from
masking a missing preservation law. The test layer adds no runtime or public
declaration, fixture, helper, assertion, or runner call.

The implementation commits are `9745854` (189 changed lines), `8e4e248` (54),
and `6f22a09` (49), all below 300 changed lines; this completion update is the
fourth staged commit. Focused trust-zero checks, the 544-job full build, the
976-job full test run, metadata and kernel checks, diff checks, declaration
inventory, abstract/present/absent critical-path checks, and independent P0-P3
audits pass.

## Publication and consequences

This proof-only layer is internal and changes no frozen or published boundary.
Optional-write consumers can observe the three immutable structural fields
without destructuring a success witness or repeating Account cases.

Further contract-entry inputs still wait for concrete consumers and lifetime
rules.
