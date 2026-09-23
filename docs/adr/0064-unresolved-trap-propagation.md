# ADR-0064: Unresolved trap propagation

- Status: Accepted
- Decision date: 2026-08-28
- Scope: proof-only propagation through synchronized partial resolution
- Implementation: Complete

## Context

ADR-0062 resolves a frame's WorldState and effect journal together. A trapped
outcome deliberately produces `none`, leaving trap disposition to a future
caller. When that partial result is followed by an arbitrary continuation,
the continuation must not manufacture a resolved state-and-effect pair.

This slice records that generic Option boundary. It does not decide what a
runtime eventually does with the unresolved trap.

## Decision

Add no carrier, executable API, instance, or helper. Publish exactly one
non-simp law with this typechecked signature:

```lean
universe u v w x

theorem resolvedWorldStateAndEffects?_trapped_bind
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (stateCheckpoint workingWorld : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (reason : TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) → Option Next) :
    (resolvedWorldStateAndEffects? stateCheckpoint effectCheckpoint effectWorking
      (⟨workingWorld, FrameOutcome.trapped reason⟩ :
        FrameRunResult TrapReason)).bind next = none
```

The proof is `rfl` and reports exactly `[propext]`. The theorem is not a simp
rule: it documents a continuation boundary rather than local constructor
normalization.

The quantification over `Next` and `next` is intentional. No continuation can
turn the resolver's trapped `none` into a successful value.

## Meaning of `none`

Here `none` means only that trap disposition remains unresolved and Option
bind short-circuits. It does not select checkpoint or working WorldState,
rollback or working effects, trace survival or loss, a fatal-error envelope,
or a transaction result.

## Required test

Add exactly one runtime assertion importing only the definition module. It
constructs a trapped result with a concrete reason and binds the resolver to a
sentinel continuation that would return `some` if invoked. The observed result
must be `none`. The test does not invoke the proof law.

## Staged implementation plan

Keep each of four commits below 300 changed lines: documentation; the exact
one law and umbrella import; the exact one runtime assertion and runner entry;
independent audit and completion evidence.

## Publication and exclusions

This proof-only slice is internal and not published. It adds no scenario-level
child/parent law, frame stack, invocation operation, checkpoint creation,
trace taxonomy, append operation or order, concrete event representation,
transaction boundary, fatal-trap policy, or resolved trap carrier.

It adds no parser or source form, Wire field or tag, Profile,
ABI, Core-result adapter, EVM revision, opcode, gas schedule, serialization,
canonical delta, or frozen artifact.

## Consequences

The synchronized resolver now has a generic proof boundary for unresolved
traps. A later ADR may choose how an enclosing invocation or transaction
interprets that absence without changing this propagation fact.

## Implementation record

The completed proof-only slice adds no carrier, executable API, instance, or
helper. A 26-line properties module plus one umbrella import publishes exactly
one non-simp `rfl` law, whose measured axiom set is `[propext]`.

One runtime assertion lives in a 34-line definition-only test module with two
runner lines. It supplies a concrete trap reason, observes the initial `none`,
and confirms that binding a sentinel continuation still returns `none`.

The implementation commits are `6baba07` (122 changed lines), `12fa73d` (27),
and `a1aca0f` (36), all below 300 changed lines; this completion update is the
fourth staged commit. Focused and full builds, tests, trust-zero, axiom,
semantic-kernel, metadata, document-link, diff, and independent P0-P3 audits
pass.
