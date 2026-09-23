# ADR-0077: Parent-indexed trap propagation payload coherence

- Status: Accepted
- Decision date: 2026-08-28
- Scope: proof-only characterization of selected trap propagation payloads
- Implementation: Complete

## Context

ADR-0076 constructs an optional prospective enclosing-boundary payload. Its
three outcome laws let a caller compute the selector after first proving which
outcome constructor is stored. A consumer that instead receives
`trapPropagationPayload? = some payload` still lacks a public law for recovering
the trap reason and the payload's complete canonical shape.

The selected journal also carries the accumulated internal working trace.
ADR-0073 proves that the designated enclosing working pair's trace prefixes
that working trace, but no existing law connects the prefix fact to an
arbitrary payload known to have been selected.

These are proof-interface gaps. They do not require another value constructor,
selector, callback, or runtime transition.

## Decision

Add no carrier, executable operation, alias, coercion, instance, or helper.
Publish exactly two non-simp laws:

```lean
namespace Solcore.Semantics.ParentIndexedFrameContinuationContext

universe u v w

theorem trapPropagationPayload?_eq_some_iff
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (payload :
      FrameRunResult TrapReason ×
        FrameEffectJournal RollbackState (FrameTrace Event)) :
    context.trapPropagationPayload? = some payload ↔
      ∃ reason,
        context.result.outcome = FrameOutcome.trapped reason ∧
        payload =
          (⟨parentWorking.1, FrameOutcome.trapped reason⟩,
            ⟨parentWorking.2.rollback, context.effectWorking.trace⟩)

theorem trapPropagationPayload?_some_tracePrefix
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (payload :
      FrameRunResult TrapReason ×
        FrameEffectJournal RollbackState (FrameTrace Event))
    (payloadEq : context.trapPropagationPayload? = some payload) :
    FrameTrace.IsPrefixOf parentWorking.2.trace payload.2.trace

end Solcore.Semantics.ParentIndexedFrameContinuationContext
```

The first law is the only successful-selection characterization. Its forward
direction considers the stored outcome and rewrites with ADR-0076's three
existing laws. Its reverse direction reuses the trapped law. It must not unfold
and reimplement either ADR-0075 or ADR-0076 selection.

The second law first recovers the canonical payload with the first law, then
reuses ADR-0073's `parentWorking_tracePrefix`. It adds no new trace relation or
factorization algorithm.

Both laws report exactly `[propext]`, have no additional axioms, and are not
registered as simp rules. This downstream proof-only ADR narrowly adds the iff
and payload-prefix interfaces excluded from ADR-0076's operation slice; it does
not change that operation or its original three-law interface.

## Meaning of successful selection

An equality to `some payload` proves only that pure evaluation of the opt-in
selector produced that value. It is not evidence that a runtime transition,
propagation step, invocation, parent execution, or state mutation occurred.

The recovered `FrameRunResult.working` is the designated prospective enclosing
state. The recovered journal combines the designated enclosing working pair's
rollback component with the completed context's accumulated internal working
`FrameTrace`; it is not the original child working journal.

The prefix conclusion is non-strict value factorization. The two traces may be
equal. It proves no event authenticity, unique suffix, exactly-once append,
invocation lineage, or runtime ancestry.

## Required compile regressions

Add exactly two private compile examples and no runtime assertion. Build one
concrete trapped context through ADR-0074 from a nonempty designated enclosing
trace extended by one nested event. Define the exact expected payload and
establish its selector equality by reduction.

The first example uses both directions of
`trapPropagationPayload?_eq_some_iff`: it recovers one reason, the stored
trapped outcome equality, and the complete payload equality, then reconstructs
the original selector equality. The second consumes
`trapPropagationPayload?_some_tracePrefix` for that exact payload and also
checks by reduction that its trace list is exactly parent-then-nested.

These are consumer-facing proof regressions, so they import the new properties
module. Add one runner import so the examples elaborate, but add no runtime
call. Do not add a third example, assertion, reason mapper, strict-prefix test,
or suffix test.

## Dependency boundary

The new properties module imports only ADR-0076's properties and ADR-0073's
properties. It leaves every existing definition and properties module
unchanged. The umbrella imports the new module immediately after ADR-0076's
properties.

The compile-regression module imports the new properties module and ADR-0074's
construction definition only. The runner imports that module once.

## What these laws do not decide

The laws do not perform propagation or repeat it through ancestors. They do
not prove that an enclosing frame exists, establish runtime parent/child
provenance, execute or resume a parent, invoke a continuation, catch or recover
from a trap, or classify a reason as fatal or recoverable.

They also do not define checkpoint creation, ownership or lifetime, stack,
depth, scheduling, reentrancy, argument/result delivery, heterogeneous reason
conversion, a trap taxonomy, transaction rollback or atomicity, a top-level
outcome, suffix extraction or uniqueness, event authenticity, resource
exhaustion, fuel, gas, parser or source syntax, Wire, ABI, or EVM
behavior.

The internal `FrameTrace` still carries no concrete contract-log survival,
authenticity, or publication claim.

## Staged implementation plan

Keep each of four commits below 300 changed lines: this decision and internal
roadmap update; the exact two non-simp laws and umbrella import; the exact two
private compile regressions and runner import; independent audit and completion
evidence.

## Publication and exclusions

This proof-only slice is not published. It adds no balance, code, call data,
transferred value, host call/create behavior, storage layout, serialization,
canonical delta, Profile, frozen artifact, or public format.

## Consequences

A proof consumer can safely invert a selected parent-indexed trap payload and
carry its existing non-strict trace-prefix evidence without unfolding the
selector. Execution, ancestry, handling, repeated propagation, and transaction
policy remain explicit later decisions.

## Implementation record

The completed proof-only slice adds no carrier, executable operation, alias,
coercion, instance, or helper. A 58-line properties module plus one umbrella
import publishes exactly the two specified non-simp laws. The successful-value
characterization reuses ADR-0076's three outcome laws; the payload-prefix law
then reuses that characterization and ADR-0073's existing prefix law. Neither
proof unfolds or reimplements the selector or rollback policy.

Both laws report exactly `[propext]` and neither is registered as a simp rule.
A 78-line compile-only test module plus one runner import contains exactly two
private examples. The first uses both iff directions to recover and reconstruct
the complete concrete payload. The second recovers its non-strict prefix proof
and checks the exact parent-then-nested trace by reduction. No runtime assertion,
test function, or runner call is added.

The implementation commits are `4193f22` (209 changed lines), `edd88b4` (59),
and `e01f208` (79), all below 300 changed lines; this completion update is the
fourth staged commit. Focused and full builds, tests, trust-zero, axiom,
non-simp, semantic-kernel, metadata, diff, and independent P0-P3 audits pass.

Successful selection is still only a pure value-level fact, and the prefix is
still non-strict. These laws prove no runtime propagation, enclosing-frame
existence, ancestry, parent execution, handling, repeated propagation,
transaction disposition, or concrete-log behavior.
