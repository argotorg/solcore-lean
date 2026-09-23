# ADR-0075: Parent-indexed trapped-frame rollback selection

- Status: Accepted
- Decision date: 2026-08-28
- Scope: opt-in selection of one frame-local rollback pair for a trapped frame
- Implementation: Complete

## Context

ADR-0061 separates rollback-scoped data from an opaque trace, but deliberately
returns `none` for traps. ADR-0062, ADR-0064, and ADR-0068 likewise preserve the
meaning that their generic resolution paths do not select trap state/effects.
ADR-0073 and ADR-0074 now provide an exact parent checkpoint pair, an
accumulated working trace, and a restricted construction path.

The next small decision is not complete trap disposition. It is whether an
explicit parent-indexed consumer can select a frame-local rollback pair for a
trap without changing the generic resolvers.

## Decision

Add exactly one opt-in public selector:

```lean
namespace Solcore.Semantics.ParentIndexedFrameContinuationContext

universe u v w

def trapRollback?
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    Option
      (WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)) :=
  match context.result.outcome with
  | .returned _ => none
  | .reverted _ => none
  | .trapped _ =>
      some
        (context.stateCheckpoint,
          ⟨context.effectCheckpoint.rollback,
            context.effectWorking.trace⟩)

end Solcore.Semantics.ParentIndexedFrameContinuationContext
```

For this operation, `none` means only that the outcome is not trapped. On a
trap, it selects the checkpoint WorldState and rollback component together with
the accumulated working `FrameTrace`. It returns a value; it does not mutate
state or apply rollback to a running machine.

The `parentWorking` index constrains the input type and appears in
characterization proofs, but the implementation body computes only from the
context fields and never inspects either proof field.

This is a new, narrow trace-retention policy. It is not derived from ADR-0061's
trapped equation. Retaining the internal `FrameTrace` does not mean that
contract logs or every future concrete effect survives a trap; rollback-scoped
effects belong in `RollbackState` once an event taxonomy is chosen.

Keep trap reason and prefix evidence in their existing orthogonal interfaces:
`FrameOutcome.trapReason?`, `FrameContinuationContext.resolve`, and
`ParentIndexedFrameContinuationContext.parentWorking_tracePrefix`. Do not copy
either into this selector's result.

Add no carrier, generic resolver change, alias, coercion, instance, callback,
continuation, resumption operation, or second selector. The generated
definitional equation is an intentional reduction artifact.

## Required proof interface

Publish exactly three non-simp laws:

```lean
namespace Solcore.Semantics.ParentIndexedFrameContinuationContext

universe u v w

theorem trapRollback?_returned
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.returned (TrapReason := TrapReason) data) :
    context.trapRollback? = none

theorem trapRollback?_reverted
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.reverted (TrapReason := TrapReason) data) :
    context.trapRollback? = none

theorem trapRollback?_trapped
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (reason : TrapReason)
    (outcomeEq : context.result.outcome = FrameOutcome.trapped reason) :
    context.trapRollback? =
      some
        (parentWorking.1,
          ⟨parentWorking.2.rollback, context.effectWorking.trace⟩)

end Solcore.Semantics.ParentIndexedFrameContinuationContext
```

The operation and all three laws must report exactly `[propext]` and no
additional axioms. Do not add a reason, prefix, coherence, or iff law. Consumers
can combine the existing reason and prefix interfaces when needed.

## Required tests

Add exactly three runtime assertions importing definition modules only. Build
contexts with ADR-0074 from a nonempty parent trace extended by one nested event.
Use distinct parent and working WorldState storage values and rollback values.

Return and revert must each produce `none`. Trap must produce `some` containing
the parent state identified through public storage observation, the parent
rollback value, and the exact parent-then-nested working trace. It must not
select the nested working state or rollback value. Do not import or invoke the
three laws, and do not duplicate reason or prefix tests.

## Dependency boundary

The definition module imports only the ADR-0073 carrier. The properties module
imports only the new definition module. Tests import the new definition and
ADR-0074 construction modules, not either properties module.

## What this selector does not decide

Frame-local rollback selection is fixed here. Trap propagation, fatality,
recoverability, parent continuation or resumption, and transaction disposition
remain separate decisions. The same local pair is selected for every
`TrapReason`; no taxonomy or classification is introduced.

This slice also does not decide runtime parent/child provenance, invocation,
checkpoint creation, ownership or lifetime, stack or depth, scheduling,
reentrancy, argument/result delivery, transaction checkpointing or atomicity,
trace authenticity or publication, concrete log survival, resource exhaustion,
fuel, gas, parser or source syntax, Wire, ABI, or EVM behavior.

## Staged implementation plan

Keep each of five commits below 300 changed lines: this decision and internal
roadmap update; the exact one selector and umbrella import; the exact three
non-simp laws and umbrella import; the exact three definition-only assertions
and runner wiring; independent audit and completion evidence.

## Publication and exclusions

This internal selector is not published. It adds no concrete event kind,
balance, code, call data, transferred value, host call/create behavior, storage
layout, serialization, canonical delta, Profile, frozen artifact, or public
format.

## Consequences

An opt-in consumer can obtain the parent-indexed frame-local rollback pair for
a trap while the generic reason-only and unresolved-trap APIs remain unchanged.
Propagation, fatality, resumption, and transaction policy remain later
decisions.

## Implementation record

The completed slice adds exactly one public `trapRollback?` selector in a
30-line definition module plus one umbrella import. It matches the stored
outcome without inspecting either proof field. Return and revert produce
`none`; trap selects checkpoint WorldState and rollback with the accumulated
internal working trace. It adds no carrier, generic resolver change, reason or
prefix duplication, continuation, resumption operation, or second selector.

A 56-line properties module plus one umbrella import publishes exactly three
non-simp outcome laws. The selector and all three laws report exactly
`[propext]`. An 84-line definition-only test module plus two runner lines
contains exactly three runtime assertions covering returned, reverted, and
trapped inputs with distinct parent and working state, rollback, and trace
witnesses.

The implementation commits are `73c87f6` (226 changed lines), `dece6a7` (31),
`2a43bb0` (57), and `d290213` (86), all below 300 changed lines; this completion
update is the fifth staged commit. Focused and full builds, tests, trust-zero,
axiom, semantic-kernel, metadata, diff, and independent P0-P3 audits pass.

The retained `FrameTrace` is the new narrow internal policy fixed by this ADR;
it does not imply survival of concrete contract logs or every future effect.
Frame-local selection is complete, while propagation, fatality, parent
resumption, and transaction disposition remain separate decisions.
