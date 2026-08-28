# ADR-0091: Frame-resolution continuation trap-reason mapping invariance

- Status: Accepted
- Decision date: 2026-08-28
- Scope: proof-only equality of bytes-aware continuation results under reason mapping
- Implementation: Complete

## Context

ADR-0080 maps the trapped-reason type of a total `FrameResolutionResult` while
preserving returned and reverted state, effects, and bytes. ADR-0089 continues
from that result with separate return and revert callbacks, but produces `none`
for a trap and cannot observe its reason.

These operations have complete constructor laws but no direct theorem relating
their composition. The missing proof should state that reason mapping is
unobservable to the same bytes-aware callbacks. It should not add another
continuation operation or repeat three branch-specific equations.

## Decision

Add no carrier, executable operation, alias, coercion, instance, or helper.
Publish exactly one simp theorem:

```lean
namespace Solcore.Semantics.FrameResolutionResult

universe u v w x y

@[simp] theorem continue?_mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {Next : Type y}
    (mapReason : TrapReason → MappedTrapReason)
    (result : FrameResolutionResult RollbackState TraceState TrapReason)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Bytes → Option Next) :
    (mapTrapReason mapReason result).continue?
        onReturned onReverted =
      result.continue? onReturned onReverted

end Solcore.Semantics.FrameResolutionResult
```

The theorem is heterogeneous in the source and mapped reason types. Both sides
receive the exact same two callbacks and return the same `Option Next`. The
mapper may be lossy because the continuation cannot inspect any trapped reason.

Orient the rule from continuation over a mapped result to continuation over the
original result. This removes one mapping layer. Identity, composition, and
constructor reductions converge to the same unmapped continuation expression;
add no reverse rule.

## Proof boundary

Prove the theorem by cases on the total result and reuse the public ADR-0080
mapping and ADR-0089 continuation constructor laws. The theorem must report
exactly `[propext]`.

Add no returned, reverted, or trapped specialization. Add no identity or
composition duplicate, callback mapping, `Next` mapping, context-level law,
resolution naturality law, branch-erasure law, or parent-indexed law.

ADR-0090 remains non-simp. This result-level law removes only a reason mapper
around a result before bytes-aware continuation; it does not identify the
explicit context resolve/continue composition with the older context
continuation.

## Required compile regressions

Add exactly two private compile examples and no runtime assertion, test
function, or runner call. Both examples use arbitrary rollback, trace, source
reason, mapped reason, continuation-result, and callback types.

The first example applies one heterogeneous mapper and uses `simp` to recover
the original bytes-aware continuation result. The second applies two
successive heterogeneous mappers and uses `simp` to recover the same original
result, fixing convergence with the existing mapping composition law.

The callbacks remain distinct and arbitrary in both examples. Do not add
constructor fixtures or restate branch behavior already tested by ADR-0080 and
ADR-0089.

The test module imports only the new properties module. The test runner imports
that regression module exactly once so the examples elaborate, but adds no
call.

## Dependency boundary

`FrameResolutionResultContinueTrapReasonMapProperties.lean` imports exactly
`Solcore.Semantics.FrameResolutionResultTrapReasonMapProperties` and
`Solcore.Semantics.FrameResolutionResultContinuationProperties`.

The semantic umbrella imports it immediately after the result reason-mapping
properties and before context resolution-mapping naturality. The compile
regression imports only the new proof module. Existing result, continuation,
mapping, context, ADR-0090, and test modules remain unchanged apart from one
semantic-umbrella import and one test-runner import.

## What this theorem does not decide

The theorem does not claim that bytes or the return/revert callback choice are
generally unobservable. Both remain available to the two arbitrary callbacks.
Only the trapped reason mapping is absent from their shared `Option Next`
result.

It does not claim that `mapReason` is unevaluated or that either side has equal
cost, steps, or callback invocation counts. It performs no external delivery,
parent update, state or effect mutation, callback scheduling, frame resumption,
trap handling, diagnosis, propagation, or transaction transition.

It adds no parser or source syntax, Core expression, resource rule, fuel or gas
policy, Wire or Oracle field, ABI, serialization, EVM revision, opcode behavior,
Profile, canonical delta, or published observation.

## Staged implementation plan

Keep each of four commits below 300 changed lines: this decision and internal
roadmap update; the exact one proof law and umbrella import; the exact two
compile regressions and one runner import; independent audit and completion
evidence.

## Publication and exclusions

This internal proof law is not published. It adds no balance, code, call-data
destination, transferred value, host call/create behavior, concrete event
taxonomy, storage layout, frozen artifact, or public format.

## Consequences

Reason translation on a total resolution result is now provably unobservable
to the same bytes-aware return and revert callbacks. This closes the immediate
algebraic connection between ADR-0080 and ADR-0089 without adding execution
behavior.

Actual payload consumption, parent-frame mutation, trap disposition,
scheduling, checkpoint lifecycle, and transaction atomicity remain separate
decisions.

## Implementation record

The completed proof-only slice adds one 27-line properties module plus one
semantic-umbrella import. It publishes exactly one
`FrameResolutionResult.continue?_mapTrapReason` simp theorem and no carrier,
operation, helper, alias, branch specialization, identity duplicate, or
composition duplicate. The theorem reports exactly `[propext]`.

The proof cases on the total result and reuses the existing ADR-0080 mapping
and ADR-0089 continuation constructor laws. Constructor, identity, composition,
and context-resolution mapping paths converge without a simp loop. ADR-0090
remains non-simp.

A 42-line compile-regression module plus one runner import contains exactly two
private examples and no runtime call. The first covers one arbitrary
heterogeneous mapper; the second covers two successive heterogeneous mappers.
Both retain distinct arbitrary return and revert callbacks and close by `simp`.

The implementation commits are `1c557e3` (187 changed lines), `67419cf` (28),
and `3006788` (43), all below 300 changed lines; this completion update is the
fourth staged commit. Focused and full builds, tests, trust-zero, axiom,
simp-convergence, semantic-kernel, metadata, diff, and independent P0-P3 audits
pass.

The equality establishes no mapper evaluation behavior, callback invocation
count, cost, delivery, parent mutation, trap handling, scheduling, checkpoint
lifecycle, or transaction policy.
