# ADR-0083: Frame trap-reason mapping continuation-result invariance

- Status: Accepted
- Decision date: 2026-08-28
- Scope: proof-only equality of `continue?` results under reason mapping
- Implementation: Not started

## Context

ADR-0081 can change the trap-reason type of a `FrameContinuationContext`
without changing its checkpoints, working effects, or frame working state.
ADR-0082 proves that this translation commutes with total resolution. The
other immediate consumer of the context is ADR-0067's `continue?`, whose result
is not yet related to reason translation.

Return and revert invoke a caller-supplied continuation after selecting state
and effects; trap returns `none`. None of those choices inspect the value or
type of a trapped reason. This should be exposed as one proof over the nominal
context boundary, without adding another continuation operation.

## Decision

Add no carrier, executable operation, alias, coercion, instance, or helper.
Publish exactly one simp theorem:

```lean
namespace Solcore.Semantics.FrameContinuationContext

universe u v w x y

@[simp] theorem continue?_mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x} {Next : Type y}
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason)
    (next :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Option Next) :
    (mapTrapReason mapReason context).continue? next =
      context.continue? next

end Solcore.Semantics.FrameContinuationContext
```

This is invariance, not a mapping operation on `Next`. Both sides receive the
same continuation and return the same `Option Next`. The reason mapper may be
lossy because `continue?` cannot observe it.

Orient the theorem from continuation over a mapped context to continuation
over the original context. This removes one context-map layer. There is no
reverse rule. Identity, composition, and repeated mapping therefore converge
to the same unmapped continuation expression without a simp loop.

Prove the theorem by exposing the context, frame result, and outcome
constructors. Reuse ADR-0066's continuation branch laws, ADR-0067's context
coherence law, and ADR-0081's mapping laws. Do not unfold or restate the branch
policy. The theorem must report exactly `[propext]`.

Add no returned, reverted, or trapped specialization and no lower-level
`FrameRunResult.continueWithResolvedStateAndEffects?` mapping law. The one
parametric context theorem covers every branch and pure reason mapper.

## Required compile regressions

Add exactly two private compile examples and no runtime assertion or test
function. Use abstract rollback, trace, source-reason, intermediate-reason,
target-reason, and continuation-result types.

The first example consumes `continue?_mapTrapReason` through `simp` for one
heterogeneous mapper. The second starts with two successive heterogeneous
context mappings and uses `simp` to recover the original `context.continue?
next` result, fixing repeated-mapping convergence.

The test module imports only the new properties module. Add it to the test
runner imports exactly once so the examples elaborate, but add no runtime call.
Do not add concrete return, revert, or trap fixtures; ADR-0066 and ADR-0081
already test those values.

## Dependency boundary

`FrameContinuationContextContinueTrapReasonMapProperties.lean` imports exactly
ADR-0066's `FrameRunContinuationProperties`, ADR-0067's
`FrameContinuationContextProperties`, and ADR-0081's
`FrameContinuationContextTrapReasonMapProperties`. It follows ADR-0082 in the
semantic umbrella but does not import it: resolution naturality and
continuation invariance are sibling observations over the same context mapper.

The compile-regression module imports only the new properties module. Existing
ADR-0066, ADR-0067, ADR-0081, and ADR-0082 definition, properties, and test
modules remain unchanged.

## What this theorem does not decide

The theorem does not map the continuation result, change the supplied
continuation, create or validate a checkpoint, execute a parent, append a
trace, or map a trace-prefixed, parent-indexed, or propagation payload context.

Equality of the returned `Option Next` values does not claim that `mapReason`
is unevaluated, that both computations have the same cost or steps, or that a
continuation is invoked exactly once in an operational runtime.

It does not propagate or handle a trap, establish ancestry, classify reasons,
schedule a frame, or decide transaction rollback or atomicity. It proves
equality of two pure continuation computations only.

It adds no parser or source syntax, Core fault adapter, resource-limit rule,
fuel or gas policy, Wire or Oracle field, ABI, serialization, EVM revision,
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

Reason translation is now unobservable in the `continue?` result. The existing
branch equations reduce return and revert to the same continuation application
with the same selected state and effects, while trap remains `none`.

Together with ADR-0082, this closes the two immediate semantic observations of
the canonical continuation context without adding execution behavior.
