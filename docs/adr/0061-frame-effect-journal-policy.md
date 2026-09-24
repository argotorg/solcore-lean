# ADR-0061: Parametric frame effect journal policy

- Status: Accepted
- Decision date: 2026-08-28
- Scope: rollback-scoped state and surviving trace snapshots
- Implementation: Complete

## Context

ADR-0057 fixes state selection for return and revert while leaving traps open.
ADR-0060 pairs speculative WorldState with a frame outcome. Neither decision
separates effects that rollback from observations that survive a revert.

This slice fixes only that separation. It does not choose concrete effects,
events, trace ordering, or append behavior.

## Decision

Add exactly one public carrier with two intentional public fields:

```lean
universe u v w

structure FrameEffectJournal
    (RollbackState : Type u) (TraceState : Type v) : Type (max u v) where
  rollback : RollbackState
  trace : TraceState
```

The generated constructor, projections, and recursor are the intended semantic
surface. Add no deriving clause, instance, extensionality law, or helper.
`RollbackState` may later contain rollback-scoped logs, created-contract state,
or subcall effects. `TraceState` is an opaque, already-accumulated observation
snapshot that survives revert. This ADR chooses no concrete member of either
type.

Add exactly one named public executable operation:

```lean
FrameEffectJournal.resolved?
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (checkpoint working : FrameEffectJournal RollbackState TraceState)
    (outcome : FrameOutcome TrapReason) :
    Option (FrameEffectJournal RollbackState TraceState)
```

Return yields `some working`. Revert yields
`some ⟨checkpoint.rollback, working.trace⟩`: rollback-scoped state comes from
the checkpoint while the accumulated trace survives. Trap yields `none`, still
meaning that trap disposition is undecided.

## Required proof interface

Publish exactly five laws. The first three are simp constructor equations:

```lean
@[simp] theorem resolved?_returned
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (checkpoint working : FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    resolved? checkpoint working
      (FrameOutcome.returned (TrapReason := TrapReason) data) = some working

@[simp] theorem resolved?_reverted
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (checkpoint working : FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    resolved? checkpoint working
      (FrameOutcome.reverted (TrapReason := TrapReason) data) =
        some ⟨checkpoint.rollback, working.trace⟩

@[simp] theorem resolved?_trapped
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (checkpoint working : FrameEffectJournal RollbackState TraceState)
    (reason : TrapReason) :
    resolved? checkpoint working (.trapped reason) = none
```

The two nested laws are deliberately non-simp:

```lean
theorem resolved?_child_return_parent_revert
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (parentCheckpoint childCheckpoint childWorking :
      FrameEffectJournal RollbackState TraceState)
    (childData parentData : Bytes) :
    (resolved? childCheckpoint childWorking
      (FrameOutcome.returned (TrapReason := TrapReason) childData)).bind
        (fun childResolved => resolved? parentCheckpoint childResolved
          (FrameOutcome.reverted (TrapReason := TrapReason) parentData)) =
      some ⟨parentCheckpoint.rollback, childWorking.trace⟩

theorem resolved?_child_revert_parent_revert
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (parentCheckpoint childCheckpoint childWorking :
      FrameEffectJournal RollbackState TraceState)
    (childData parentData : Bytes) :
    (resolved? childCheckpoint childWorking
      (FrameOutcome.reverted (TrapReason := TrapReason) childData)).bind
        (fun childResolved => resolved? parentCheckpoint childResolved
          (FrameOutcome.reverted (TrapReason := TrapReason) parentData)) =
      some ⟨parentCheckpoint.rollback, childWorking.trace⟩
```

Thus a returned child is adopted before a later parent revert re-rolls
rollback-scoped state. A reverted child discards its speculative rollback state,
and its trace still survives the later parent revert. All five laws are expected
to introduce no axioms; completion records the measured result.

## Required tests

Add exactly five runtime assertions using private Nat snapshot fixtures and only
the definition module: returned, reverted, trapped, child-return then
parent-revert, and child-revert then parent-revert. Fixtures distinguish all
rollback snapshots and trace snapshots.

## Staged implementation plan

Keep every commit below 300 changed lines: documentation; carrier and resolver;
five laws; five runtime assertions; independent audit and completion evidence.

## Publication and exclusions

This internal slice is not published. It defines no nested stack or invocation
mechanism, concrete effect or event taxonomy, event ordering, trace append
operation or algebra, transaction boundary, ABI, Core-result adapter, trap
taxonomy, EVM revision, opcode, gas schedule, or resource-limit policy.

It adds no parser or source form, Wire field or tag,
serialization, canonical delta, or frozen artifact. Integration with
`FrameRunResult` remains a separate decision.

## Consequences

Rollback-scoped and surviving observations can be modeled independently of
their eventual concrete contents. Nested composition is specified only as pure
resolver composition, not as an execution stack.

## Implementation record

The completed internal slice adds exactly one public carrier with two public
fields and one named executable resolver. The definition module contains 32
lines plus one umbrella import. It adds no deriving clause, instance,
extensionality law, or helper.

The 57-line properties module plus one umbrella import publishes exactly five
laws: three simp constructor equations and two non-simp nested equations. The
resolver and all five laws introduce no axioms. Exactly five runtime assertions
live in a 64-line definition-only test module with two runner lines.

The implementation commits are `8b5aa9f` (181 changed lines), `26f609f` (33),
`a31e18f` (58), and `3f66922` (66). Each remains below 300 changed lines.
Focused and full builds, tests, trust-zero, semantic-kernel,
forbidden-declaration, document-link, and diff checks pass. Independent stage
audits found no P0-P3 issue.
