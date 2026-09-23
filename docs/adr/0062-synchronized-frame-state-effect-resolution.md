# ADR-0062: Synchronized frame state and effect resolution

- Status: Accepted
- Decision date: 2026-08-28
- Scope: one-outcome resolution of WorldState and parametric effects
- Implementation: Complete

## Context

ADR-0060 resolves a frame's speculative WorldState against an external
checkpoint. ADR-0061 independently resolves rollback-scoped effects and a
surviving trace. A caller should not need to match the same outcome twice or
risk selecting state and effects from different halt branches.

## Decision

Add no carrier, instance, or helper. In module `FrameRunEffectResolution`, add
exactly one public executable operation:

```lean
universe u v w

FrameRunResult.resolvedWorldStateAndEffects?
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (stateCheckpoint : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (result : FrameRunResult TrapReason) :
    Option (WorldState × FrameEffectJournal RollbackState TraceState)
```

The implementation matches `result.outcome` exactly once. Return yields
`some (result.working, effectWorking)`. Revert yields
`some (stateCheckpoint,
  ⟨effectCheckpoint.rollback, effectWorking.trace⟩)`. Trap yields `none` and
retains the existing meaning that trap disposition is unresolved.

## Required proof interface

Publish exactly five laws. The constructor equations are simp laws proved by
`rfl`:

```lean
@[simp] theorem resolvedWorldStateAndEffects?_returned
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.returned
        (TrapReason := TrapReason) data⟩ : FrameRunResult TrapReason) =
      some (workingWorld, effectWorking)

@[simp] theorem resolvedWorldStateAndEffects?_reverted
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.reverted
        (TrapReason := TrapReason) data⟩ : FrameRunResult TrapReason) =
      some (stateCheckpoint,
        ⟨effectCheckpoint.rollback, effectWorking.trace⟩)

@[simp] theorem resolvedWorldStateAndEffects?_trapped
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (reason : TrapReason) :
    resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.trapped reason⟩ : FrameRunResult TrapReason) =
      none
```

The two projection-coherence laws are non-simp and proved by outcome cases and
`rfl`:

```lean
theorem resolvedWorldStateAndEffects?_worldState
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (stateCheckpoint : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (result : FrameRunResult TrapReason) :
    Option.map Prod.fst
      (resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint
        effectWorking result) =
      result.resolvedWorldState? stateCheckpoint

theorem resolvedWorldStateAndEffects?_effects
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (stateCheckpoint : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (result : FrameRunResult TrapReason) :
    Option.map Prod.snd
      (resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint
        effectWorking result) =
      FrameEffectJournal.resolved? effectCheckpoint effectWorking result.outcome
```

The definition and all five laws are expected to report exactly `[propext]`;
completion records the measured result.

## Required tests

Add exactly three runtime assertions using only the definition module. Distinct
WorldState storage values and Nat rollback/trace snapshots verify return,
revert, and trap, including both product projections.

## Staged implementation plan

Keep every commit below 300 changed lines: documentation; definition; five
laws; three runtime assertions; independent audit and completion evidence.

## Publication and exclusions

This internal slice is not published. It adds no result carrier, nested child
composition or invocation, trace ownership rule, concrete effect or event
taxonomy, ordering, append operation or algebra, transaction boundary, or trap
disposition.

It adds no parser or source form, Wire field or tag, Profile,
ABI, Core-result adapter, EVM revision, opcode, gas schedule, serialization,
canonical delta, or frozen artifact.

## Consequences

State and effects now share one explicit halt branch. Child adoption and nested
execution remain separate decisions rather than hidden behavior of this
resolver.

## Implementation record

The completed internal slice adds no carrier, instance, or helper and publishes
exactly one executable resolver. Its definition module contains 27 lines plus
one umbrella import.

The 78-line properties module plus one umbrella import publishes exactly five
laws: three simp constructor equations and two non-simp projection-coherence
equations. The definition and all five laws report exactly `[propext]`.
Exactly three runtime assertions live in a 66-line definition-only test module
with two runner lines and exercise both product projections.

The implementation commits are `f12a3fa` (185 changed lines), `bc0183c` (28),
`7481d5c` (79), and `c86afac` (68). Each remains below 300 changed lines.
Focused and full builds, tests, trust-zero, semantic-kernel, metadata,
forbidden-declaration, document-link, and diff checks pass. Independent stage
audits found no P0-P3 issue.
