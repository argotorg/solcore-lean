# ADR-0104: Parent-indexed initialization continuation-context coherence

- Status: Accepted
- Decision date: 2026-08-29
- Scope: equate two pure continuation-context construction routes
- Implementation: Planned

## Context

ADR-0098 builds both an initial trace extension and checkpointed working values
from one caller-designated parent pair plus caller-supplied initial state.
ADR-0074 can construct a proof-refined parent-indexed continuation context from
that trace extension, while ADR-0088 can construct the plain continuation
context directly from the checkpointed working values.

Both routes use the same parent checkpoint, initial WorldState, working
rollback, starting trace, and caller-supplied outcome. Their complete base
contexts are definitionally equal, but no public theorem records that boundary.
Consumers therefore compare projections manually or unfold both constructors.

## Decision

Add no executable operation, carrier, instance, or helper. Publish exactly one
whole-context construction coherence law:

```lean
namespace Solcore.Semantics.ParentIndexedFrameInitialization

universe u v w

theorem toFrameContinuationContext_fromTraceExtension_eq_fromCheckpointedWorkingPair
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (outcome : FrameOutcome TrapReason) :
    (ParentIndexedFrameContinuationContext.fromTraceExtension
      parentWorking initialization.workingRollback
      initialization.initialTraceExtension
      ⟨initialization.initialWorld, outcome⟩).toFrameContinuationContext =
      FrameContinuationContext.fromCheckpointedWorkingPair
        initialization.toCheckpointedWorkingPair outcome

end Solcore.Semantics.ParentIndexedFrameInitialization
```

The left route constructs the proof-refined parent-indexed context and then
forgets its prefix and parent-index evidence. The right route constructs the
same plain context from the initialized checkpointed working values. The
outcome is the same arbitrary caller argument on both sides.

Keep the law non-simp. This is a coherence theorem between two intentional
whole-context construction routes, not a field-normalization rule. Existing
ADR-0074, ADR-0088, and ADR-0098 simp laws already normalize individual
observations. Consumers that need the whole equality use this law explicitly,
without making one route a global canonical form.

## Proof boundary

The proof is `rfl`. It unfolds no WorldState operation, performs no outcome or
trace cases, and adds no private theorem, custom axiom, classical choice, or
unchecked declaration.

The public law must report exactly `[propext]`. Add no reverse theorem,
projection specialization, prefix or checkpoint-equality duplicate, resolution
law, continuation law, or equality of the proof-refined carriers themselves.

## Required compile regressions

Add exactly two private compile examples importing only the new properties
module:

1. the complete plain-context equality through the named non-simp law; and
2. equality after applying the same arbitrary `continue?` callback to both
   contexts, obtained with `congrArg` on that named law.

There is no public test function, runtime declaration, runtime assertion,
fixture, helper, or runner call. The runner imports the compile-only module
exactly once.

## Dependency boundary

`ParentIndexedFrameInitializationContinuationContextCoherenceProperties.lean`
imports exactly `ParentIndexedFrameInitialization`,
`ParentIndexedFrameContinuationConstruction`, and
`FrameContinuationContextFromCheckpointedWorkingPair`. It imports no
properties module.

The semantic umbrella imports the new module immediately after
`FrameContinuationContextFromCheckpointedWorkingPairProperties`. The compile
regression imports only the new module. The runner adds one import immediately
after the parent-indexed continuation-construction test and no call. Existing
definitions and theorem statements remain unchanged.

## What this slice does not decide

The law does not turn initialization into a completed-frame transition. The
caller supplies the outcome independently; the theorem does not claim that a
frame ran, produced that outcome, or preserved its initial state while running.

The parent pair, initial WorldState, and working rollback remain arbitrary
caller inputs. The initial trace extension records no new event. The theorem
adds no checkpoint capture time, ownership, lifetime, active-frame identity,
ancestry provenance, scheduling, stack, depth, return delivery, trap handling,
rollback, transaction, concurrency, reentrancy, atomicity, cost, or gas policy.

It adds no storage selector, Account-presence rule, parser or source syntax,
Core expression, Wire or Oracle field, Profile, ABI, serialization, or
published observation.

## Staged implementation plan

Keep each of four commits below 300 changed lines: this decision and targeted
internal documentation; the exact non-simp law plus one umbrella import; the
exact two compile regressions plus one runner import and no call; independent
audit and completion evidence.

## Publication and consequences

This proof-only layer is internal and changes no frozen or published boundary.
Whole-context consumers can transport results between the ADR-0074 and ADR-0088
construction routes without repeating their field equations.

Actual frame entry, execution, completion, and parent resumption remain
separate decisions.
