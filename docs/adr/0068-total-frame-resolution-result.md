# ADR-0068: Total frame resolution result

- Status: Accepted
- Decision date: 2026-08-28
- Scope: branch-complete first-order result of one frame resolution
- Implementation: Complete

## Context

ADR-0066 exposes an Option continuation boundary. It intentionally maps a trap
and a continuation that returns `none` to the same partial result. ADR-0067
bundles the caller-owned inputs for one completed frame, but a consumer that
needs to inspect the frame before choosing a continuation still lacks a total,
first-order resolution value.

The new value must preserve return/revert payloads and trap reasons while
representing only valid combinations of outcomes and selected state/effects.

## Decision

Add exactly one public inductive carrier:

```lean
universe u v w

inductive FrameResolutionResult
    (RollbackState : Type u) (TraceState : Type v)
    (TrapReason : Type w) : Type (max u v w) where
  | returned
      (state : WorldState)
      (effects : FrameEffectJournal RollbackState TraceState)
      (data : Bytes)
  | reverted
      (state : WorldState)
      (effects : FrameEffectJournal RollbackState TraceState)
      (data : Bytes)
  | trapped (reason : TrapReason)
```

The three constructors and generated recursor/eliminators are an intentional
semantic surface. Add no deriving clause, instance, default, projection helper,
or extensionality interface.

Add exactly one total public operation:

```lean
universe u v w

def FrameContinuationContext.resolve
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    FrameResolutionResult RollbackState TraceState TrapReason
```

The operation matches `context.result.outcome` exactly once. Return preserves
the return bytes and carries `context.result.working` with
`context.effectWorking`. Revert preserves the revert bytes and carries
`context.stateCheckpoint` with checkpoint rollback state and working trace.
Trap carries only its reason.

The trapped constructor does not mean that checkpoint, working state, or
effects were deleted. It means this result selects none of them while trap
disposition remains unresolved. The original immutable context remains
available to the caller. No fatal, rollback, trace-survival, or transaction
policy is inferred from the omission.

## Required proof interface

Publish exactly three simp constructor laws:

```lean
universe u v w

@[simp] theorem FrameContinuationContext.resolve_returned
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    (⟨stateCheckpoint, effectCheckpoint, effectWorking,
      ⟨workingWorld, FrameOutcome.returned
        (TrapReason := TrapReason) data⟩⟩ :
      FrameContinuationContext RollbackState TraceState TrapReason).resolve =
      FrameResolutionResult.returned workingWorld effectWorking data

@[simp] theorem FrameContinuationContext.resolve_reverted
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    (⟨stateCheckpoint, effectCheckpoint, effectWorking,
      ⟨workingWorld, FrameOutcome.reverted
        (TrapReason := TrapReason) data⟩⟩ :
      FrameContinuationContext RollbackState TraceState TrapReason).resolve =
      FrameResolutionResult.reverted stateCheckpoint
        ⟨effectCheckpoint.rollback, effectWorking.trace⟩ data

@[simp] theorem FrameContinuationContext.resolve_trapped
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (reason : TrapReason) :
    (⟨stateCheckpoint, effectCheckpoint, effectWorking,
      ⟨workingWorld, FrameOutcome.trapped reason⟩⟩ :
      FrameContinuationContext RollbackState TraceState TrapReason).resolve =
      FrameResolutionResult.trapped reason
```

All three laws are proved by `rfl` and must report exactly `[propext]`.

## Required tests

Add exactly three runtime assertions importing only the definition module.
Pattern matching on the public result constructors must show that return keeps
a nonempty payload and the working state/effects, revert keeps its payload and
the checkpoint/checkpoint/working selection, and trap keeps a concrete reason
without a state/effect pair. Use public WorldState observations rather than
whole-state equality. Tests do not import or invoke proof laws.

## Staged implementation plan

Keep each of five commits below 300 changed lines: documentation; the exact one
carrier, one operation, and umbrella import; the exact three laws and umbrella
import; the exact three runtime assertions and runner entry; independent audit
and completion evidence.

## Publication and exclusions

This internal result is not published. It defines no continuation-failure
diagnostic, trap disposition, parent/child link, frame identity, stack, depth,
scheduling, checkpoint creation or lifetime, trace prefix proof, append
operation or order, event taxonomy, transaction boundary or atomicity.

It adds no balances, code, host call/create behavior, parser or source form,
Wire field or tag, Profile, ABI, storage layout, Core-result
adapter, EVM revision, opcode, gas schedule, serialization, canonical delta, or
frozen artifact.

## Consequences

Consumers can now inspect every frame-resolution branch without losing payload
or reason information and without inventing a continuation. ADR-0080 adds a
downstream reason-type mapping without changing this carrier or resolver.
Nested invocation and transaction policy remain later, explicit decisions.

## Implementation record

The completed slice adds one three-constructor carrier and one total public
operation in a 43-line definition module plus one umbrella import. The
operation matches the outcome once and selects exactly the state, effects,
payload, or reason fixed above. The carrier and operation each report exactly
`[propext]`; no deriving clause, instance, default, or helper is added.

A 50-line properties module plus one umbrella import publishes exactly three
simp `rfl` constructor laws, each with axiom set `[propext]`. Exactly three
runtime assertions live in a 77-line definition-only test module with two
runner lines.

The implementation commits are `82a2b53` (198 changed lines), `bae3146` (44),
`31482b4` (51), and `c415427` (79), all below 300 changed lines; this completion
update is the fifth staged commit. Focused and full builds, tests, trust-zero,
axiom, semantic-kernel, metadata, document-link, diff, and independent P0-P3
audits pass.
