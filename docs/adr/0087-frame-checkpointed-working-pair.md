# ADR-0087: Frame checkpointed working pair

- Status: Accepted
- Decision date: 2026-08-28
- Scope: structural pairing of one checkpoint snapshot with independent working values
- Implementation: Complete

## Context

ADR-0086 gives a caller-designated synchronized checkpoint pair a nominal
type. The runtime foundation still has no pre-outcome carrier that keeps that
snapshot beside a separate synchronized working pair. Existing carriers start
later or describe different information: `FrameRunResult` has working state
and an outcome, `FrameContinuationContext` is a completed-frame bundle, and
ADR-0073 additionally requires trace and parent-index evidence.

The missing boundary is purely structural. It must allow checkpoint and
working values to differ without proving equality, inequality, derivation, or
initialization order. Calling it active state or frame inputs would imply a
runtime phase or provenance that the carrier cannot establish.

## Decision

Add exactly one public carrier:

```lean
namespace Solcore.Semantics

universe u v

/-- One checkpoint snapshot paired with independent state-and-effects working values. -/
structure FrameCheckpointedWorkingPair
    (RollbackState : Type u) (TraceState : Type v) : Type (max u v) where
  checkpoint : FrameCheckpointSnapshot RollbackState TraceState
  working : WorldState × FrameEffectJournal RollbackState TraceState

end Solcore.Semantics
```

The two fields are caller-supplied values. `checkpointed` means only that the
working pair is stored beside a nominal checkpoint snapshot. It does not mean
that the checkpoint was derived from the working pair or that an execution
performed a checkpoint action.

Keep `working` as the repository's existing synchronized raw pair. Splitting
it into state and effects would add a third projection and require consumers
to rebuild the pair already used by resolution and continuation APIs.

The carrier, generated constructor, and generated projections must report
exactly `[propext]`. Add no custom operation or custom theorem. In particular,
do not add a named constructor that is definitionally identical to `mk`,
duplicate projection laws, a properties module, coercion, tuple conversion,
equality proof, validity predicate, owner, identity, or default value.

## Required compile regressions

Add exactly three private definition-only compile examples. Import only the
new carrier module. Cover:

1. universe-polymorphic direct construction of the whole carrier from an
   arbitrary checkpoint and working pair, closed by `rfl`;
2. exact checkpoint projection from a concrete nonempty checkpoint snapshot;
   and
3. exact whole working-pair projection from separately supplied concrete
   working values.

The concrete checkpoint and working fixtures must use distinct nonzero storage
values, rollback sentinels, and nonempty traces. Their difference is visible in
the terms but is not promoted to an inequality theorem.

The test module must contain no public declaration, runtime assertion, test
function, or runtime call. Add exactly one import to the existing test runner
and no call site. Do not import a properties module because this slice has
none.

## Dependency boundary

`FrameCheckpointedWorkingPair.lean` imports exactly
`Solcore.Semantics.FrameCheckpointSnapshot`. `WorldState` and
`FrameEffectJournal` are direct field types but are already provided by that
required dependency; do not duplicate its imports.

The semantic umbrella imports the carrier immediately after the ADR-0086
definition and properties modules. The compile-regression module imports only
the new carrier, and the test runner imports that module exactly once. Existing
raw-pair resolvers, completed-frame contexts, and parent-indexed carriers remain
unchanged.

## What this carrier does not decide

The carrier asserts no equality or inequality between checkpoint and working
values. It does not say that either is current, fresh, valid, captured at
entry, copied from a parent, or owned by a particular frame. It supplies no
time, lifetime, lineage, parent/child identity, or invocation evidence.

It does not initialize or mutate working state or effects, seed rollback data,
append or relate traces, create an account, transfer value, or choose an order
among those actions.

It carries no outcome and does not run or complete a frame, resolve or
continue a result, schedule nested work, deliver return or revert data, handle
or propagate a trap, enforce depth or reentrancy, or decide transaction commit,
rollback, or atomicity.

It adds no parser or source syntax, Core expression, resource-limit rule, fuel
or gas policy, Wire field, ABI, serialization, EVM revision, opcode
behavior, canonical delta, or published observation.

## Staged implementation plan

Keep each of four commits below 300 changed lines: this decision and internal
roadmap update; the exact carrier and one umbrella import; the exact three
definition-only compile regressions and one runner import; independent audit
and completion evidence.

The immediately following ADR must consume every field through exactly one
`FrameContinuationContext.fromCheckpointedWorkingPair` adapter taking this
carrier and a caller-supplied `FrameOutcome`. It will construct the existing
completed continuation context without claiming that execution occurred. This
requirement prevents the structural carrier from becoming an orphan API.

## Publication and exclusions

This internal carrier is not published. It adds no balance, code, call data,
transferred value, host call/create behavior, concrete event taxonomy, storage
layout, frozen artifact, or public format.

## Consequences

Later APIs can carry one nominal checkpoint snapshot and one independent
synchronized working pair without a dependent index or relationship proof.
The generated constructor and projections are the complete API for this
structural boundary.

The next adapter can turn these values plus an outcome into the existing
continuation context. Checkpoint creation, initialization, execution,
scheduling, diagnostics, and transaction policy remain separate decisions.

## Implementation record

The completed slice adds exactly one `FrameCheckpointedWorkingPair` carrier in
a 17-line definition module plus one umbrella import. Its only intentional API
is the generated constructor and the `checkpoint` and `working` projections;
there is no custom operation, theorem, properties module, instance, coercion,
or validity predicate.

The carrier, constructor, and both projections report exactly `[propext]`. The
carrier imports only ADR-0086 and keeps the existing synchronized working pair
whole.

A 53-line definition-only test module plus one runner import contains exactly
three private compile examples and no runtime declaration, assertion, or call.
They cover universe-polymorphic construction, exact checkpoint projection, and
exact working-pair projection. Concrete checkpoint and working fixtures use
storage values `0x56` and `0x78`, rollback sentinels `10` and `20`, and traces
`[1]` and `[1, 2]` respectively.

The implementation commits are `e3ee763` (186 changed lines), `8791470` (18),
and `e765508` (54), all below 300 changed lines; this completion update is the
fourth staged commit. Focused and full builds, tests, trust-zero, axiom,
semantic-kernel, diff, and independent P0-P3 audits pass.

The carrier establishes no checkpoint/working relationship, capture or entry
event, currentness, initialization, lifecycle, ownership, execution,
scheduling, or transaction policy.
