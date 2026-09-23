# ADR-0082: Frame trap-reason mapping resolution naturality

- Status: Accepted
- Decision date: 2026-08-28
- Scope: proof-only commutation of context mapping and total resolution
- Implementation: Complete

## Context

ADR-0081 maps the trap-reason type of a `FrameContinuationContext` while
preserving every checkpoint and working input. ADR-0080 maps the reason type of
the total `FrameResolutionResult` while preserving selected state, effects, and
bytes. The APIs do not yet state that these two routes agree with ADR-0068's
resolver.

Without that law, a consumer must reopen all return, revert, and trap cases to
show that reason translation cannot change resolution. This is a proof gap,
not a need for another resolver or mapping operation.

## Decision

Add no carrier, executable operation, alias, coercion, instance, or helper.
Publish exactly one simp theorem:

```lean
namespace Solcore.Semantics.FrameContinuationContext

universe u v w x

@[simp] theorem resolve_mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context :
      FrameContinuationContext RollbackState TraceState TrapReason) :
    resolve (mapTrapReason mapReason context) =
      FrameResolutionResult.mapTrapReason mapReason (resolve context)

end Solcore.Semantics.FrameContinuationContext
```

The left side changes the context's reason type before resolution. The right
side resolves the original context and then changes only the resulting trapped
reason. Equality proves that return/revert state, effects, and bytes are
unchanged by the placement of the mapper.

The theorem is oriented from `resolve (map context)` to `map (resolve
context)`. This removes the resolve-over-context-map redex. There is no reverse
rule. Identity, composition, and constructor simplification on either path
converge to the same `FrameResolutionResult` normal form without a loop.

Prove the theorem by exposing the context, frame result, and outcome
constructors, then use the existing ADR-0068, ADR-0080, and ADR-0081 simp laws.
Do not unfold or restate the resolver's branch policy. The theorem must report
exactly `[propext]`.

Add no return, revert, or trap specialization. The one parametric theorem
covers every branch and every pure mapper.

## Required compile regressions

Add exactly two private compile examples and no runtime assertion or test
function. Use abstract rollback, trace, source-reason, intermediate-reason, and
target-reason types.

The first example consumes `resolve_mapTrapReason` through `simp` for one
heterogeneous mapper. The second starts with two successive context mappings
and uses `simp` to reach one resolution-result mapping by the composed function
in the correct order.

The test module imports only the new properties module. Add it to the test
runner imports exactly once so the examples elaborate, but add no runtime call.
Do not add concrete branch fixtures; ADR-0068, ADR-0080, and ADR-0081 already
test those values.

## Dependency boundary

`FrameContinuationContextResolveTrapReasonMapProperties.lean` imports exactly
the ADR-0081 context-map properties, ADR-0068 resolution properties, and
ADR-0080 resolution-result-map properties. It adds the theorem to the semantic
umbrella after those dependencies.

The compile-regression module imports only the new properties module. Existing
ADR-0068, ADR-0080, and ADR-0081 definition, properties, and test modules remain
unchanged.

## What this theorem does not decide

The theorem does not execute a frame, invoke `continue?`, create or validate a
checkpoint, roll back state, append a trace, or map a trace-prefixed,
parent-indexed, or propagation payload context.

It does not propagate or handle a trap, establish ancestry, execute or resume
a parent, classify reasons, schedule a frame, or decide transaction rollback
or atomicity. It proves equality of two pure value computations only.

It adds no parser or source syntax, Core fault adapter, resource-limit rule,
fuel or gas policy, Wire field, ABI, serialization, EVM revision,
opcode behavior, Profile, canonical delta, or published format.

## Staged implementation plan

Keep each of four commits below 300 changed lines: this decision and internal
roadmap update; the exact one proof law and umbrella import; the exact two
compile regressions and one runner import; independent audit and completion
evidence.

## Publication and exclusions

This internal proof law is not published. It adds no balance, code, call data,
transferred value, host call/create behavior, storage layout, concrete log
rule, frozen artifact, or public format.

## Consequences

Reason translation is now proved natural with respect to total frame
resolution: mapping before or after resolution selects identical state,
effects, and bytes and differs only by the same caller-supplied reason mapper.

ADR-0083 fixes the corresponding `continue?` result-value invariance without
changing any execution operation.

## Implementation record

The completed proof-only slice adds one 26-line properties module plus one
semantic-umbrella import. It publishes exactly one
`FrameContinuationContext.resolve_mapTrapReason` simp theorem and no operation,
carrier, alias, instance, helper, or branch-specific law. The proof exposes the
existing context, frame-result, and outcome constructors and then reuses the
ADR-0068, ADR-0080, and ADR-0081 simp laws without unfolding resolution policy.

The theorem is heterogeneous in the source and mapped reason universes. Its
orientation removes `resolve (mapTrapReason ...)` in favor of mapping the total
resolution result, composes with the existing identity and composition laws,
and reports exactly `[propext]`.

A 34-line test module plus one runner import contains exactly two private
compile examples and no runtime function or assertion. One consumes abstract
heterogeneous naturality; the other reduces two successive context mappings to
one result mapping by `fun reason => second (first reason)`.

The implementation commits are `727fedd` (175 changed lines), `2006e89` (27),
and `966816f` (35), all below 300 changed lines; this completion update is the
fourth staged commit. Focused and full builds, tests, trust-zero, axiom,
simp-termination, semantic-kernel, metadata, diff, and independent P0-P3 audits
pass.

The theorem remains a pure equality. It invokes no continuation, maps no
indexed context or payload, and establishes no propagation, ancestry, handling,
or transaction policy.
