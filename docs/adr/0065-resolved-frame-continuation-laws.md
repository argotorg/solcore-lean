# ADR-0065: Resolved frame continuation laws

- Status: Accepted
- Decision date: 2026-08-28
- Scope: proof-only continuation equations for synchronized partial resolution
- Implementation: Complete

## Context

ADR-0062 resolves a frame's WorldState and effect journal together. ADR-0064
proves that a trapped result remains `none` when followed by any Option
continuation. The two resolved constructors need the matching generic boundary:
their continuation must receive exactly the pair selected by the resolver.

This slice records those equations without adding an invocation operation or
choosing who creates checkpoints and accumulated traces.

## Decision

Add no carrier, executable API, instance, or helper. Publish exactly two
non-simp laws:

```lean
universe u v w x

theorem resolvedWorldStateAndEffects?_returned_bind
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    (resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.returned
        (TrapReason := TrapReason) data⟩ :
        FrameRunResult TrapReason)).bind next =
      next (workingWorld, effectWorking)

theorem resolvedWorldStateAndEffects?_reverted_bind
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    (resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.reverted
        (TrapReason := TrapReason) data⟩ :
        FrameRunResult TrapReason)).bind next =
      next (stateCheckpoint,
        ⟨effectCheckpoint.rollback, effectWorking.trace⟩)
```

Both proofs are `rfl`, report exactly `[propext]`, and are not simp rules. They
describe a continuation boundary rather than local constructor normalization.
Together with ADR-0064, they cover all three FrameOutcome constructors.

## Required tests

Add exactly two runtime assertions importing only the definition module. Each
uses a sentinel continuation that inspects the received WorldState, rollback
snapshot, and trace snapshot. One assertion covers return and one covers
revert. The tests do not import or invoke the proof laws.

## Staged implementation plan

Keep each of four commits below 300 changed lines: documentation; the exact two
laws and umbrella import; the exact two runtime assertions and runner entry;
independent audit and completion evidence.

## Publication and exclusions

This proof-only slice is internal and not published. It adds no child/parent
scenario theorem, frame stack, invocation operation, checkpoint creation or
ownership, trace taxonomy, append operation or order, concrete event
representation, transaction boundary, or trap policy.

It adds no parser or source form, Wire field or tag, Profile,
ABI, Core-result adapter, EVM revision, opcode, gas schedule, serialization,
canonical delta, or frozen artifact.

## Consequences

Any continuation after a resolved return or revert receives exactly the
synchronized pair already selected by the resolver. A later invocation API can
reuse these equations without this ADR deciding how its inputs are produced.

## Implementation record

The completed proof-only slice adds no carrier, executable API, instance, or
helper. A 44-line properties module plus one umbrella import publishes exactly
two non-simp `rfl` laws. Each measured axiom set is `[propext]`.

Two runtime assertions live in a 61-line definition-only test module with two
runner lines. Their sentinel continuations observe the selected WorldState
value, rollback snapshot, and trace snapshot for return and revert.

The implementation commits are `25ce7bf` (147 changed lines), `c98d2e3` (45),
and `9bc43c5` (63), all below 300 changed lines; this completion update is the
fourth staged commit. Focused and full builds, tests, trust-zero, axiom,
semantic-kernel, metadata, document-link, diff, and independent P0-P3 audits
pass.
