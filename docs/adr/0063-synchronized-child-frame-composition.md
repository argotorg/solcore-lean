# ADR-0063: Synchronized child-frame composition

- Status: Accepted
- Decision date: 2026-08-28
- Scope: proof-only child resolution followed by parent revert
- Implementation: In progress

## Context

ADR-0062 resolves WorldState and parametric effects from one shared frame
outcome. The approved nested policy says that a returned child is adopted as
the parent's speculative working pair, while a reverted child first restores
its child checkpoint. A later parent revert must restore the parent checkpoint
in either case while preserving the accumulated trace.

This slice proves those two compositions. It does not add an invocation or
frame-stack operation.

## Decision

Add no carrier, executable API, instance, or helper. Publish exactly two
non-simp laws with the following typechecked signatures:

```lean
universe u v w

theorem resolvedWorldStateAndEffects?_child_return_parent_revert
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (parentStateCheckpoint childStateCheckpoint childStateWorking : WorldState)
    (parentEffectCheckpoint childEffectCheckpoint childEffectWorking :
      FrameEffectJournal RollbackState TraceState)
    (childData parentData : Bytes) :
    (resolvedWorldStateAndEffects?
      childStateCheckpoint childEffectCheckpoint childEffectWorking
      (⟨childStateWorking, FrameOutcome.returned
        (TrapReason := TrapReason) childData⟩ : FrameRunResult TrapReason)).bind
        (fun childResolved => resolvedWorldStateAndEffects?
          parentStateCheckpoint parentEffectCheckpoint childResolved.2
          (⟨childResolved.1, FrameOutcome.reverted
            (TrapReason := TrapReason) parentData⟩ : FrameRunResult TrapReason)) =
      some (parentStateCheckpoint,
        ⟨parentEffectCheckpoint.rollback, childEffectWorking.trace⟩)

theorem resolvedWorldStateAndEffects?_child_revert_parent_revert
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (parentStateCheckpoint childStateCheckpoint childStateWorking : WorldState)
    (parentEffectCheckpoint childEffectCheckpoint childEffectWorking :
      FrameEffectJournal RollbackState TraceState)
    (childData parentData : Bytes) :
    (resolvedWorldStateAndEffects?
      childStateCheckpoint childEffectCheckpoint childEffectWorking
      (⟨childStateWorking, FrameOutcome.reverted
        (TrapReason := TrapReason) childData⟩ : FrameRunResult TrapReason)).bind
        (fun childResolved => resolvedWorldStateAndEffects?
          parentStateCheckpoint parentEffectCheckpoint childResolved.2
          (⟨childResolved.1, FrameOutcome.reverted
            (TrapReason := TrapReason) parentData⟩ : FrameRunResult TrapReason)) =
      some (parentStateCheckpoint,
        ⟨parentEffectCheckpoint.rollback, childEffectWorking.trace⟩)
```

Both laws are proved by `rfl` and are expected to report exactly `[propext]`;
completion records the measured result. They remain outside the simp set
because they encode a two-stage scenario rather than local normalization.

For child return, the first resolution adopts the child working WorldState and
effect journal as the parent's speculative working pair. Parent revert then
restores parent WorldState and parent rollback state. For child revert, the
first resolution restores the child checkpoints before the same parent revert.
The final result is identical: parent checkpoint WorldState, parent checkpoint
rollback state, and the child's accumulated working trace.

## Trace convention

`childEffectWorking.trace` is an opaque snapshot that already contains the
parent trace prefix. It is not a child-local fragment. These laws neither append
nor reorder events and select no taxonomy, collection type, append operation,
or algebra.

## Required tests

Add exactly two runtime assertions using only the ADR-0062 definition module.
Distinct WorldState and Nat rollback/trace fixtures cover child return followed
by parent revert and child revert followed by parent revert. Each assertion
checks intermediate child projections as well as the final parent checkpoint
WorldState, parent rollback state, and child accumulated trace. Tests do not
invoke the proof laws.

## Staged implementation plan

Keep each of four commits below 300 changed lines: documentation; the exact two
laws; the exact two runtime assertions; independent audit and completion
evidence.

## Publication and exclusions

This proof-only slice is internal and not published. It defines no nested frame
stack, invocation operation, frame identity, call depth, checkpoint creation,
trace construction, event taxonomy or order, append behavior, transaction
boundary or atomicity, or trap disposition.

It adds no parser or source form, Wire field or tag, Profile, Oracle behavior,
ABI, Core-result adapter, EVM revision, opcode, gas schedule, serialization,
canonical delta, or frozen artifact.

## Consequences

The approved non-trapping child policy has one explicit synchronized proof
boundary. A concrete nested evaluator and trap policy still require separate
decisions.
