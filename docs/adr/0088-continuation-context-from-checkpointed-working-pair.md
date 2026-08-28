# ADR-0088: Continuation context from a checkpointed working pair

- Status: Accepted
- Decision date: 2026-08-28
- Scope: pure construction of an existing completed-frame context from structural values
- Implementation: Complete

## Context

ADR-0087 stores one ADR-0086 checkpoint snapshot beside an independent
synchronized working pair. That structural carrier deliberately has no custom
operation. Its required first consumer must connect every stored value to an
existing semantic boundary without claiming how the values arose.

`FrameContinuationContext` is the appropriate target. It already represents
the caller-owned inputs used after one frame has produced an outcome, but its
four fields currently require manual assembly. A canonical adapter can unpack
the checkpoint and working pair and attach a caller-supplied `FrameOutcome`.
The adapter constructs a value; it does not observe or perform execution.

## Decision

Add exactly one public operation:

```lean
namespace Solcore.Semantics.FrameContinuationContext

universe u v w

/-- Build continuation inputs from checkpointed working values and an outcome. -/
def fromCheckpointedWorkingPair
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (outcome : FrameOutcome TrapReason) :
    FrameContinuationContext RollbackState TraceState TrapReason :=
  {
    stateCheckpoint := values.checkpoint.state
    effectCheckpoint := values.checkpoint.effects
    effectWorking := values.working.2
    result := ⟨values.working.1, outcome⟩
  }

end Solcore.Semantics.FrameContinuationContext
```

The mapping consumes every ADR-0087 field. Checkpoint state and effects become
the matching checkpoint fields; working effects become `effectWorking`; and
working state plus the supplied outcome become `FrameRunResult`.

The outcome remains opaque and is never matched. It need not have been
produced from the supplied working values. The operation and its generated
equation must report exactly `[propext]`.

Add no second constructor, `complete` or `finish` alias, reverse adapter,
coercion, instance, default outcome, validity predicate, branch-specific
operation, or relationship proof.

## Required proof interface

Publish exactly four simp projection laws:

```lean
namespace Solcore.Semantics.FrameContinuationContext

universe u v w

@[simp] theorem stateCheckpoint_fromCheckpointedWorkingPair
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (outcome : FrameOutcome TrapReason) :
    (fromCheckpointedWorkingPair values outcome).stateCheckpoint =
      values.checkpoint.state

@[simp] theorem effectCheckpoint_fromCheckpointedWorkingPair
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (outcome : FrameOutcome TrapReason) :
    (fromCheckpointedWorkingPair values outcome).effectCheckpoint =
      values.checkpoint.effects

@[simp] theorem effectWorking_fromCheckpointedWorkingPair
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (outcome : FrameOutcome TrapReason) :
    (fromCheckpointedWorkingPair values outcome).effectWorking =
      values.working.2

@[simp] theorem result_fromCheckpointedWorkingPair
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (outcome : FrameOutcome TrapReason) :
    (fromCheckpointedWorkingPair values outcome).result =
      ⟨values.working.1, outcome⟩

end Solcore.Semantics.FrameContinuationContext
```

Each proof is `rfl` and must report exactly `[propext]`. The laws expose the
target carrier's four direct fields. Add no whole-constructor law, duplicate
`result.working` or `result.outcome` law, branch law, extensionality theorem,
resolve/continue coherence law, or reverse simp rule.

## Required compile regressions

Add exactly three private definition-only compile examples. Import only the
new definition module; do not import or consume the four laws. Cover:

1. the complete abstract record equation for arbitrary checkpointed working
   values and arbitrary outcome, closed by `rfl`;
2. exact retention of concrete checkpoint state/effects and working effects
   with visibly distinct state, rollback, and nonempty trace values; and
3. exact `FrameRunResult` retention of the concrete working state and one
   nonempty caller-supplied outcome.

The test module must contain no public declaration, runtime assertion, test
function, or runtime call. Add exactly one import to the existing test runner
and no call site. Do not call `resolve`, `continue?`, or any parent-indexed
constructor.

Because the first example quantifies an arbitrary `FrameOutcome`, return,
revert, and trap are all covered by the definition without three branch tests.
The operation has no outcome branch to test.

## Dependency boundary

`FrameContinuationContextFromCheckpointedWorkingPair.lean` imports exactly
`Solcore.Semantics.FrameCheckpointedWorkingPair` and
`Solcore.Semantics.FrameContinuationContext`. The properties module imports
exactly the new definition module.

The semantic umbrella imports the definition and properties modules directly
after ADR-0087. The compile-regression module imports only the new definition,
and the test runner imports that regression module exactly once. Existing
context construction, resolution, continuation, trace-prefix, and
parent-indexed APIs remain unchanged.

## What this adapter does not decide

The adapter does not establish that a frame ran or completed. It does not prove
that the outcome arose from the working state, that the checkpoint was captured
at entry, or that either input is current, fresh, valid, initialized, owned, or
related to a particular frame or parent.

It does not mutate state or effects, seed rollback data, append or relate
traces, create an account, transfer value, schedule work, deliver return or
revert data, handle or propagate a trap, enforce depth or reentrancy, or decide
transaction commit, rollback, or atomicity.

It does not call resolution or continuation and makes no cost, step-count,
evaluation-order, or exactly-once claim. It adds no parser or source syntax,
Core expression, resource rule, fuel or gas policy, Wire or Oracle field, ABI,
serialization, EVM revision, opcode behavior, Profile, canonical delta, or
published observation.

## Staged implementation plan

Keep each of five commits below 300 changed lines: this decision and internal
roadmap update; the exact one operation and umbrella import; the exact four
projection laws and umbrella import; the exact three definition-only compile
regressions and one runner import; independent audit and completion evidence.

## Publication and exclusions

This internal adapter is not published. It adds no balance, code, call data,
transferred value, host call/create behavior, concrete event taxonomy, storage
layout, frozen artifact, or public format.

## Consequences

ADR-0087 is no longer an orphan structural carrier: every checkpoint and
working value can be assembled canonically with an outcome into the existing
continuation boundary.

Future proof-only slices may state resolution or continuation coherence when
needed. Runtime transitions, checkpoint creation, scheduling, and transaction
policy remain separate decisions.

## Implementation record

The completed slice adds exactly one
`FrameContinuationContext.fromCheckpointedWorkingPair` operation in a 25-line
definition module plus one umbrella import. It consumes every checkpoint,
working, and outcome value exactly once and performs no outcome match. The
operation and its generated equation report exactly `[propext]`.

A 47-line properties module plus one umbrella import publishes exactly four
definitional simp laws for the target context's direct fields. All four report
exactly `[propext]`; their disjoint one-way reductions introduce no critical
overlap or simp loop.

A 68-line definition-only test module plus one runner import contains exactly
three private compile examples and no runtime declaration, assertion, or call.
They cover an abstract whole-record equation over arbitrary outcome, exact
checkpoint and working-effect retention with distinct concrete values, and an
exact result containing working state plus nonempty return bytes
`[0x12, 0xff]`. The test imports no laws and calls neither resolution nor
continuation.

The implementation commits are `4910627` (225 changed lines), `1d18d3f` (26),
`4b0f21a` (48), and `a9c3825` (69), all below 300 changed lines; this completion
update is the fifth staged commit. Focused and full builds, tests, trust-zero,
axiom, simp-termination, semantic-kernel, metadata, diff, and independent
P0-P3 audits pass.

The adapter establishes no execution completion, outcome provenance,
checkpoint capture, initialization, lifecycle, ownership, trace relationship,
scheduling, delivery, trap handling, or transaction policy.
