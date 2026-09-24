# ADR-0090: Frame continuation branch/byte erasure coherence

- Status: Accepted
- Decision date: 2026-08-28
- Scope: proof-only compatibility between bytes-aware and bytes-insensitive continuation
- Implementation: Complete

## Context

ADR-0089 lets a caller continue from a total `FrameResolutionResult` with
separate return and revert callbacks that receive the selected state/effects
and exact bytes. ADR-0067's older `FrameContinuationContext.continue?` uses one
callback over the selected state/effects and intentionally cannot observe the
branch or bytes.

A context can already use the new route as `context.resolve.continue?`.
Adding a named wrapper for that expression would duplicate an existing
composition without adding semantics. The useful missing interface is instead
one compatibility theorem: when both branch callbacks are the same callback
and ignore bytes, the richer route must equal the existing context operation.

## Decision

Add no carrier, executable operation, alias, coercion, instance, or helper.
Publish exactly one non-simp theorem:

```lean
namespace Solcore.Semantics.FrameContinuationContext

universe u v w x

theorem resolve_continue?_ignoreBranchAndBytes
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (context : FrameContinuationContext RollbackState TraceState TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Option Next) :
    context.resolve.continue?
        (fun selected _ => next selected)
        (fun selected _ => next selected) =
      context.continue? next

end Solcore.Semantics.FrameContinuationContext
```

The left side first performs ADR-0068 total resolution and then ADR-0089
bytes-aware continuation. Both callbacks erase the return/revert distinction
and ignore the exact bytes, but preserve the selected state/effect pair. The
right side is the established bytes-insensitive context continuation.

Orient the equality from the explicit resolve/continue composition to the
shorter existing context operation. Keep it out of the global simp set and add
no reverse theorem. Callers may use it explicitly with `rw`.

The non-simp status avoids an incomplete simplification path when an existing
reason-mapping law rewrites an inner `resolve` before this outer composition is
recognized. This decision adds no result-continuation mapping law merely to
make the two simp paths converge.

## Proof boundary

Prove the theorem by exposing the context, its frame-run result, and the
outcome constructor, then close return, revert, and trap by reflexivity. The
single theorem must report exactly `[propext]`.

Add no returned, reverted, or trapped specialization. Add no theorem for
arbitrary distinct callbacks, bytes-dependent callbacks, result mapping,
context reason mapping, trace-prefixed contexts, parent-indexed contexts, or
checkpointed working pairs. Existing constructor laws already cover those
lower-level values where applicable.

The equality concerns only returned `Option Next` values. It does not assert
that either expression is evaluated operationally, that callback applications
have equal cost, or that callbacks run exactly once.

## Required compile regressions

Add exactly two private compile examples and no runtime assertion, test
function, or runner call.

The first example is polymorphic in every state, reason, and result type. It
uses an explicit rewrite to reduce the bytes-erasing resolve/continue
composition to `context.continue? next`, fixing the public theorem's intended
use and non-simp status.

The second example starts from a context whose trap-reason type is changed by
an arbitrary heterogeneous mapper. It explicitly rewrites the outer
bytes-erasing composition first, then uses the existing context-continuation
mapping-invariance law to reach the original context result. This fixes the
intended interaction that keeps the new theorem out of the simp set.

The test module imports exactly the new properties module and
`FrameContinuationContextContinueTrapReasonMapProperties`. The test runner
imports the regression module exactly once so the examples elaborate, but adds
no call.

## Dependency boundary

`FrameContinuationContextResolutionContinuationCoherenceProperties.lean`
imports exactly `Solcore.Semantics.FrameResolutionResultContinuation`. The
semantic umbrella imports the new proof module immediately after the ADR-0089
properties and before result reason mapping.

The compile-regression module imports the new proof module and the existing
context-continuation mapping-invariance properties. Existing context
continuation, total resolution, bytes-aware continuation, mapping, trace,
parent-indexed, checkpoint, and test modules remain unchanged apart from one
semantic-umbrella import and one test-runner import.

## What this theorem does not decide

The theorem performs no external delivery, parent update, state or effect
mutation, callback scheduling, frame resumption, invocation, checkpoint
creation, initialization, ownership transfer, trace append, or transaction
transition.

It does not preserve bytes for the supplied `next`; bytes are deliberately
ignored on the richer side to match the old API. It does not distinguish
return from revert for `next`. It does not observe, classify, map, diagnose,
handle, or propagate a trapped reason, and does not distinguish a trap from a
selected callback returning `none`.

It does not equate callbacks, execution traces, costs, steps, or invocation
counts. It adds no parser or source syntax, Core expression, resource rule,
fuel or gas policy, Wire field, ABI, serialization, EVM revision,
opcode behavior, canonical delta, or published observation.

## Staged implementation plan

Keep each of four commits below 300 changed lines: this decision and internal
roadmap update; the exact one proof law and umbrella import; the exact two
compile regressions and one runner import; independent audit and completion
evidence.

## Publication and exclusions

This internal compatibility theorem is not published. It adds no balance,
code, call-data destination, transferred value, host call/create behavior,
concrete event taxonomy, storage layout, frozen artifact, or public format.

## Consequences

The result-level bytes-aware continuation now provably extends the established
context continuation after branch and byte erasure. Callers that do not need
branch identity or bytes can retain the old API without a new alias, while
richer callers keep using the explicit `context.resolve.continue?`
composition.

Actual payload consumption, parent-frame mutation, trap disposition,
scheduling, checkpoint lifecycle, and transaction atomicity remain separate
decisions.

## Implementation record

The completed proof-only slice adds one 29-line properties module plus one
semantic-umbrella import. It publishes exactly one non-simp
`FrameContinuationContext.resolve_continue?_ignoreBranchAndBytes` theorem and
no carrier, executable operation, helper, alias, reverse rule, specialization,
or runtime declaration. The theorem reports exactly `[propext]`.

The proof exposes the context, frame-run result, and outcome constructors; all
three outcome branches then close by reflexivity. Keeping the theorem out of
the simp set avoids the documented incomplete path through inner context
reason mapping.

A 45-line compile-regression module plus one runner import contains exactly two
private examples and no runtime call. The first consumes the theorem directly
at fully polymorphic types. The second explicitly rewrites a heterogeneously
reason-mapped context before applying the existing continuation-invariance law.

The implementation commits are `51d095e` (199 changed lines), `163b580` (30),
and `3b69be5` (46), all below 300 changed lines; this completion update is the
fourth staged commit. Focused and full builds, tests, trust-zero, axiom,
semantic-kernel, diff, and independent P0-P3 audits pass.

The equality establishes no operational execution, callback evaluation count,
cost, byte recovery, delivery, parent mutation, trap handling, scheduling,
checkpoint lifecycle, or transaction policy.
