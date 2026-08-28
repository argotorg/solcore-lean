# ADR-0073: Parent-indexed frame continuation context

- Status: Accepted
- Decision date: 2026-08-28
- Scope: tie one completed frame's checkpoints to an exact parent working pair
- Implementation: Active

## Context

ADR-0067 and ADR-0068 provide a completed-frame context and total result.
ADR-0071 binds checkpoint-to-working trace-prefix evidence to that context,
while ADR-0072 supplies an event-only construction path for the evidence.

One relationship is still carried only by caller convention: when the context
represents a completed nested frame, its state and effect checkpoints should be
the parent's working state and journal at entry. This relationship must be
packaged without claiming that an invocation actually occurred and without
duplicating the existing resolver.

## Decision

Add exactly one parent-indexed public carrier:

```lean
universe u v w

structure ParentIndexedFrameContinuationContext
    (RollbackState : Type u) (Event : Type v) (TrapReason : Type w)
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event))
    extends
      FrameContinuationContextWithTracePrefix
        RollbackState Event TrapReason where
  checkpoint_eq_parentWorking :
    (stateCheckpoint, effectCheckpoint) = parentWorking
```

The inherited value is one completed continuation context. Its existing proof
says that the checkpoint trace prefixes the working trace. The new proof ties
both checkpoints to the exact parent working pair used as the type index.
Constructing the usual nested-frame shape from that pair closes the equality by
`rfl`.

The generated constructor, base and equality projections, and eliminators are
intentional. Add no executable operation, alias, coercion, instance, default,
smart constructor, or new result carrier. Inherited field notation already
reuses the ADR-0068 total resolver; a new resolver would duplicate its three
branches.

Both stored relationships live in `Prop`. Existing execution does not inspect,
decide, or branch on either proof.

## Required proof interface

Publish exactly three non-simp laws. First, transport the inherited prefix
proof across checkpoint equality:

```lean
universe u v w

theorem ParentIndexedFrameContinuationContext.parentWorking_tracePrefix
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    FrameTrace.IsPrefixOf
      parentWorking.2.trace context.effectWorking.trace
```

Second, a known returned outcome resolves through the existing operation and
retains the parent trace prefix:

```lean
universe u v w

theorem ParentIndexedFrameContinuationContext.resolve_returned
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.returned (TrapReason := TrapReason) data) :
    context.resolve = FrameResolutionResult.returned
      context.result.working context.effectWorking data ∧
    FrameTrace.IsPrefixOf
      parentWorking.2.trace context.effectWorking.trace
```

Third, a known reverted outcome resolves to the indexed parent state and
rollback component, retains the accumulated working trace, and carries the same
prefix evidence:

```lean
universe u v w

theorem ParentIndexedFrameContinuationContext.resolve_reverted
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.reverted (TrapReason := TrapReason) data) :
    context.resolve = FrameResolutionResult.reverted parentWorking.1
      ⟨parentWorking.2.rollback, context.effectWorking.trace⟩ data ∧
    FrameTrace.IsPrefixOf
      parentWorking.2.trace context.effectWorking.trace
```

All three laws remain outside the simp set. The carrier and laws must report
exactly `[propext]` and no additional axioms. Add no separate trap law: the
existing reason-only result has no state/effects to relate to the parent index.

## Required tests

Add exactly three runtime assertions importing definition modules only. Use a
nonempty parent trace and ADR-0072 to record one nested event. Construct the
ADR-0071 context with the generated prefix theorem, then construct the indexed
context with checkpoint equality `rfl`.

Distinct parent and nested working WorldState storage values and rollback
snapshots must show that inherited resolution selects the nested working pair
and payload on return, selects the indexed parent state/rollback with the
accumulated parent-then-nested trace and payload on revert, and preserves only
the concrete reason on trap. Do not import or invoke the three proof laws.

## What this context does not prove

The parent index, checkpoint equality, and trace prefix are caller-supplied
value relationships. They do not establish a runtime parent/child identity,
that an invocation occurred, checkpoint creation, ownership or lifetime, event
authenticity, scheduling, stack or depth, reentrancy, argument/result delivery,
or that an append occurred exactly once.

Trap disposition, trace survival after a trap, transaction boundaries,
rollback, and atomicity remain undecided. This slice also introduces no
recursion or divergence behavior.

## Staged implementation plan

Keep each of five commits below 300 changed lines: documentation; the exact one
carrier and umbrella import; the exact three non-simp laws and umbrella import;
the exact three definition-only runtime assertions and runner wiring;
independent audit and completion evidence.

## Publication and exclusions

This internal refinement is not published. It adds no concrete event taxonomy,
balance, code, call data, transferred value, host call/create behavior, ABI,
EVM revision, opcode, gas schedule, parser or source form, Core expression,
Wire field or tag, Profile, Oracle behavior, serialization, canonical delta,
or frozen artifact.

## Consequences

A consumer can resolve one completed context while proving that its checkpoints
are one exact parent working pair and that its accumulated trace extends that
pair's trace. Concrete nested invocation, scheduling, traps, and transaction
policy remain later decisions.
