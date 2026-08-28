# ADR-0076: Parent-indexed trap propagation payload selection

- Status: Accepted
- Decision date: 2026-08-28
- Scope: opt-in construction of one trap-only payload for a caller-designated prospective enclosing boundary
- Implementation: Complete

## Context

ADR-0075 selects a frame-local rollback pair only for a trapped
parent-indexed context. The trap reason remains in the immutable outcome, and
no parent-facing result is constructed. A caller that elects one-step trap
propagation therefore still has to combine the selected state/effects with the
same trapped outcome.

This combination changes semantic level: it shapes child-local rollback data
as a prospective enclosing-boundary frame result. That choice should be
explicit, opt-in, and separate from any runtime transition or stack policy.

## Decision

Add exactly one public payload selector:

```lean
namespace Solcore.Semantics.ParentIndexedFrameContinuationContext

universe u v w

def trapPropagationPayload?
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    Option
      (FrameRunResult TrapReason ×
        FrameEffectJournal RollbackState (FrameTrace Event)) :=
  context.trapRollback?.map fun (state, effects) =>
    (⟨state, context.result.outcome⟩, effects)

end Solcore.Semantics.ParentIndexedFrameContinuationContext
```

The operation uses only `Option.map`; it does not repeat the outcome match or
rollback selection. Return and revert remain `none`. On a trap, it pairs the
ADR-0075-selected state with the original immutable trapped outcome, and keeps
the selected journal as the second product component.

This operation constructs a value for one caller-designated enclosing
boundary. It does not perform or prove runtime propagation. The parent index
designates a working pair at the value level and does not establish runtime
parent/child provenance.

In the constructed `FrameRunResult`, `working` is the designated enclosing
working state selected by ADR-0075, and the trapped constructor and reason are
preserved as the prospective enclosing outcome. The second product component
is ADR-0075's selected journal: the designated enclosing working pair's
rollback component with the accumulated internal working `FrameTrace`. It is
not the original child working journal.

ADR-0075 keeps rollback selection, reason observation, and prefix evidence
orthogonal. This ADR recombines state/effects with the existing trapped outcome
only for the narrow payload-construction purpose above. It adds no reason or
prefix helper.

Add no carrier, outcome match, generic resolver change, alias, coercion,
instance, continuation, resumption, callback, or second payload operation. The
generated definitional equation is an intentional reduction artifact.

## Required proof interface

Publish exactly three non-simp laws:

```lean
namespace Solcore.Semantics.ParentIndexedFrameContinuationContext

universe u v w

theorem trapPropagationPayload?_returned
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.returned (TrapReason := TrapReason) data) :
    context.trapPropagationPayload? = none

theorem trapPropagationPayload?_reverted
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.reverted (TrapReason := TrapReason) data) :
    context.trapPropagationPayload? = none

theorem trapPropagationPayload?_trapped
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (reason : TrapReason)
    (outcomeEq : context.result.outcome = FrameOutcome.trapped reason) :
    context.trapPropagationPayload? =
      some
        (⟨parentWorking.1, FrameOutcome.trapped reason⟩,
          ⟨parentWorking.2.rollback, context.effectWorking.trace⟩)

end Solcore.Semantics.ParentIndexedFrameContinuationContext
```

Prove these by rewriting with ADR-0075's three laws; do not unfold and duplicate
its branch policy. The operation and all laws must report exactly `[propext]`
and no additional axioms. Add no prefix, reason, map-coherence, iff, or repeated
propagation theorem.

## Required tests

Add exactly three runtime assertions importing definition modules only. Build
contexts through ADR-0074 with distinct parent and working WorldState storage
values, rollback values, a nonempty parent trace extended by one nested event,
and concrete payload/reason values.

Return and revert must each produce `none`. Trap must produce `some` whose
`FrameRunResult.working` is the designated enclosing state, whose outcome
contains the exact original trap reason, and whose selected journal contains
the designated enclosing working pair's rollback component with the exact
parent-then-nested trace. Do not import or invoke the laws, and do not repeat
prefix testing.

## Dependency boundary

The definition module imports only ADR-0075's definition. The properties module
imports the new definition and ADR-0075 properties, then reuses its laws. Tests
import the new definition and ADR-0074 construction modules only.

## What this payload does not decide

This value does not mutate state, apply rollback to a machine, invoke a
continuation, prove an invocation or enclosing frame exists, execute a parent,
resume or catch, classify a trap as fatal or recoverable, or force propagation.
It does not repeat propagation through ancestors or choose a top-level verdict.

It also does not define checkpoint creation, ownership or lifetime, runtime
parent/child provenance, stack, depth, scheduling, reentrancy, argument/result
delivery, heterogeneous trap-reason conversion, a trap taxonomy, transaction
rollback or atomicity, resource exhaustion, fuel, gas, parser or source syntax,
Wire, Oracle, ABI, or EVM behavior.

The internal `FrameTrace` is inherited from ADR-0075. Carrying it adds no
concrete contract-log survival, authenticity, or publication rule and records
no new propagation event.

## Staged implementation plan

Keep each of five commits below 300 changed lines: this decision and internal
roadmap update; the exact one operation and umbrella import; the exact three
non-simp laws and umbrella import; the exact three definition-only assertions
and runner wiring; independent audit and completion evidence.

## Publication and exclusions

This internal payload selector is not published. It adds no balance, code, call
data, transferred value, host call/create behavior, storage layout,
serialization, canonical delta, Profile, frozen artifact, or public format.

## Consequences

A caller can construct one parent-indexed, trap-only propagation payload while
keeping execution, handling, ancestry, and transaction policy explicit and
separate. The payload is a value-level option, not evidence that propagation
occurred.

## Implementation record

The completed slice adds exactly one public `trapPropagationPayload?` selector
in a 24-line definition module plus one umbrella import. It uses `Option.map`
over ADR-0075's selector and does not repeat the outcome match or rollback
policy. Return and revert produce `none`; trap pairs the ADR-0075-selected
designated enclosing working state with the existing trapped outcome and
retains the selected journal. That journal combines the designated enclosing
working pair's rollback component with the accumulated internal working
`FrameTrace`; it is not the original child working journal.

A 56-line properties module plus one umbrella import publishes exactly three
non-simp outcome laws by rewriting with ADR-0075's laws. The selector, its
generated equation, and all three laws report exactly `[propext]`. A 91-line
definition-only test module plus two runner lines contains exactly three
runtime assertions. Return and revert check absence; trap distinguishes
designated enclosing and working state and rollback values, checks the exact
parent-then-nested trace, and preserves one concrete trap reason.

The implementation commits are `8f89c3c` (224 changed lines), `9e6a3aa` (25),
`c8a6330` (57), and `3e7afee` (93), all below 300 changed lines; this completion
update is the fifth staged commit. Focused and full builds, tests, trust-zero,
axiom, semantic-kernel, metadata, diff, and independent P0-P3 audits pass.

The operation constructs a value for one caller-designated prospective
enclosing boundary. It still does not perform or prove runtime propagation,
parent execution, ancestry, handling, repeated ancestor propagation, or any
transaction disposition. Carrying ADR-0075's internal `FrameTrace` adds no
concrete-log survival, authenticity, or publication claim.
