# ADR-0066: Caller-owned frame continuation

- Status: Accepted
- Decision date: 2026-08-28
- Scope: minimal executable continuation after synchronized frame resolution
- Implementation: Complete

## Context

ADR-0060 keeps frame checkpoints outside `FrameRunResult`. ADR-0061 treats the
working trace as an opaque, already-accumulated snapshot. ADR-0062 resolves
WorldState and effects together, and ADR-0064/ADR-0065 prove how all three
outcomes behave when that partial result is bound to a continuation.

The next executable seam should make that continuation boundary explicit
without introducing a parent-frame carrier, stack, or trace algebra.

## Decision

Add exactly one public operation in `FrameRunResult`:

```lean
universe u v w x

def continueWithResolvedStateAndEffects?
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (result : FrameRunResult TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    Option Next
```

The operation synchronously resolves `result` with the caller-supplied state
checkpoint, effect checkpoint, and working journal, then binds `next` to the
selected pair. It adds no carrier, instance, or helper.

The caller owns all three inputs. In particular, `effectWorking.trace` is an
opaque snapshot that already includes any caller prefix. The operation never
creates a checkpoint or appends, merges, or reorders traces.

## Meaning of `none`

A trapped result produces `none` without invoking `next`. A resolved result may
also produce `none` when `next` itself returns `none`. Therefore this operation
uses `none` only to mean that the partial continuation produced no `Next`
value. It does not diagnose a trap, choose a fatal-error envelope, or define a
transaction result. A future diagnostic carrier may distinguish causes without
changing this operation.

## Required proof interface

Publish exactly three simp constructor laws, one each for return, revert, and
trap. Return invokes `next` with working WorldState and the working journal.
Revert invokes it with checkpoint WorldState, checkpoint rollback state, and
working trace. Trap yields `none` without invoking `next`.

All three laws are `rfl`, quantify arbitrary payloads, reasons, continuations,
and `Next` types, and must report exactly `[propext]`.

## Required tests

Add exactly three runtime assertions importing only the definition module.
Distinct WorldState storage values and Nat rollback/trace snapshots show that
the return continuation receives the working triple, the revert continuation
receives the checkpoint/checkpoint/working triple, and a concrete trap skips a
sentinel continuation. Tests do not import or invoke the proof laws.

## Staged implementation plan

Keep each of five commits below 300 changed lines: documentation; the exact one
operation and umbrella import; the exact three laws and umbrella import; the
exact three runtime assertions and runner entry; independent audit and
completion evidence.

## Publication and exclusions

This internal operation is not published. It defines no parent-frame carrier,
frame identity, stack, call depth, scheduling, checkpoint creation or lifetime,
trace construction, prefixing, append operation or order, event taxonomy,
transaction boundary or atomicity, or trap/failure diagnosis.

It adds no balances, code, call/create host behavior, parser or source form,
Wire field or tag, ABI, storage layout, Core-result
adapter, EVM revision, opcode, gas schedule, serialization, canonical delta, or
frozen artifact.

## Consequences

A caller can now resume arbitrary partial computation only after a frame's
state and effects have been selected from the same outcome. Later runtime work
can choose concrete parent frames and diagnostic results without changing this
caller-owned boundary.

## Implementation record

The completed slice adds exactly one public operation in a 25-line definition
module plus one umbrella import. It adds no carrier, instance, or helper. The
operation's measured axiom set is `[propext]`.

A 59-line properties module plus one umbrella import publishes exactly three
simp constructor laws. All three are proved by `rfl` and each reports exactly
`[propext]`. Exactly three runtime assertions live in a 71-line definition-only
test module with two runner lines.

The implementation commits are `3bd1e00` (149 changed lines), `f02e3d4` (26),
`2c9795a` (60), and `bdd7e84` (73), all below 300 changed lines; this completion
update is the fifth staged commit. Focused and full builds, tests, trust-zero,
axiom, semantic-kernel, document-link, diff, and independent P0-P3
audits pass.
