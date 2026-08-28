# ADR-0067: Caller-owned frame continuation context

- Status: Accepted
- Decision date: 2026-08-28
- Scope: nominal bundle for one completed frame's continuation inputs
- Implementation: Complete

## Context

ADR-0066 exposes a caller-owned continuation operation whose state checkpoint,
effect checkpoint, working journal, and `FrameRunResult` are separate
arguments. Repeated call sites could accidentally reorder or mix those inputs.
They should travel as one nominal value before a larger runtime model exists.

The bundle must reuse `FrameRunResult`: duplicating its working WorldState or
outcome would create two competing representations of a completed frame.

## Decision

Add exactly one public carrier:

```lean
universe u v w

structure FrameContinuationContext
    (RollbackState : Type u) (TraceState : Type v)
    (TrapReason : Type w) : Type (max u v w) where
  stateCheckpoint : WorldState
  effectCheckpoint : FrameEffectJournal RollbackState TraceState
  effectWorking : FrameEffectJournal RollbackState TraceState
  result : FrameRunResult TrapReason
```

The four fields, generated constructor, projections, and recursor are an
intentional semantic surface. Add no deriving clause, instance, extensionality
law, default, or helper. This is a continuation-input bundle, not a complete
execution frame: it contains no address, caller, value, code, program counter,
stack, depth, or transaction data.

Add exactly one public operation:

```lean
universe u v w x

def FrameContinuationContext.continue?
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (context : FrameContinuationContext RollbackState TraceState TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    Option Next
```

The operation delegates all behavior to ADR-0066 using the four projections.
The caller constructs and owns the context. The carrier groups values but does
not prove checkpoint lineage or trace-prefix membership.

`effectWorking.trace` remains an opaque, already-accumulated snapshot. The
operation creates no checkpoint and never appends, merges, or reorders traces.
Its `none` retains ADR-0066's non-diagnostic meaning: either the frame trapped
or the continuation returned `none`.

## Required proof interface

Publish exactly one non-simp coherence law:

```lean
universe u v w x

theorem FrameContinuationContext.continue?_eq_continueWithResolvedStateAndEffects?
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (context : FrameContinuationContext RollbackState TraceState TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    context.continue? next =
      context.result.continueWithResolvedStateAndEffects?
        context.stateCheckpoint context.effectCheckpoint context.effectWorking
        next
```

The proof is `rfl` and must report exactly `[propext]`.

Do not duplicate ADR-0066's three constructor laws. Rewriting through the
coherence law exposes those existing laws when a caller needs branch-specific
reasoning.

## Required tests

Add exactly three runtime assertions importing only the definition module.
Return and revert contexts use distinct checkpoint/working WorldState values
and Nat rollback/trace snapshots, exercising all public projections while
observing the pair received by a continuation. A concrete trapped context must
skip a sentinel continuation. Tests do not import or invoke proof laws.

## Staged implementation plan

Keep each of five commits below 300 changed lines: documentation; the exact one
carrier, one operation, and umbrella import; the exact one coherence law and
umbrella import; the exact three runtime assertions and runner entry;
independent audit and completion evidence.

## Publication and exclusions

This internal carrier is not published. It defines no parent/child link, frame
identity, address, caller, transferred value, code, stack, depth, scheduling,
checkpoint creation or lifetime, trace prefix proof, append operation or order,
event taxonomy, transaction boundary or atomicity, or trap diagnosis.

It adds no balances, host call/create behavior, parser or source form, Wire
field or tag, Profile, Oracle behavior, ABI, storage layout, Core-result
adapter, EVM revision, opcode, gas schedule, serialization, canonical delta, or
frozen artifact.

## Consequences

The caller-owned continuation inputs now have one stable nominal boundary.
Future runtime carriers can contain or replace this bundle deliberately rather
than relying on an unstructured argument list.

## Implementation record

The completed slice adds one four-field carrier and one public operation in a
35-line definition module plus one umbrella import. The generated constructor,
projections, and recursor are intentional. The carrier and operation each
report exactly `[propext]`; no deriving clause, instance, default,
extensionality law, or helper is added.

A 23-line properties module plus one umbrella import publishes exactly one
non-simp `rfl` coherence law with axiom set `[propext]`. Exactly three runtime
assertions live in an 87-line definition-only test module with two runner lines.

The implementation commits are `fead51f` (171 changed lines), `8703b24` (36),
`0b8804a` (24), and `2e3b16c` (89), all below 300 changed lines; this completion
update is the fifth staged commit. Focused and full builds, tests, trust-zero,
axiom, semantic-kernel, metadata, document-link, diff, and independent P0-P3
audits pass.
