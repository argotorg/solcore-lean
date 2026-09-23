# ADR-0127: Parent-indexed resolution view

- Status: Accepted
- Decision date: 2026-08-29
- Scope: combine completed-frame resolution with opt-in trap rollback
- Implementation: Complete

## Context

The internal frame layer already has two complementary views of a completed
parent-indexed frame.

`FrameContinuationContext.resolve` is total over return, revert, and trap. It
keeps the working state and effects on return, restores the parent checkpoint
state and rollback component on revert, and preserves the reason on trap. The
generic trapped result intentionally carries no state or effects because trap
disposition is not global policy.

`ParentIndexedFrameContinuationContext.trapRollback?` is a separate opt-in
selector. It returns the exact parent checkpoint state and rollback component,
together with the accumulated working trace, only for a trapped outcome.

A caller that needs the lossless pairing of these two existing observations
must currently call both operations and prove that their branches agree.
ADR-0125 now produces the parent-indexed context after selected handled
execution, so this repeated composition has an actual producer.

The repository still cannot honestly define transaction finalization. The
parent index proves equality with one caller-supplied working pair; it does not
prove that the pair is a transaction checkpoint or root-frame state. Root
identity, checkpoint ownership and lifetime, out-of-fuel disposition, and a
final persistence boundary remain undefined.

## Decision

Add one pure parent-indexed resolution view:

```lean
namespace ParentIndexedFrameContinuationContext

universe u v w

def resolveWithTrapRollback
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)}
    (context :
      ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking) :
    FrameResolutionResult
        RollbackState (FrameTrace Event) TrapReason ×
      Option
        (WorldState ×
          FrameEffectJournal RollbackState (FrameTrace Event)) :=
  (context.resolve, context.trapRollback?)
```

The first component is the existing total resolution. The second is the
existing opt-in rollback selection. No new branch policy or calculation is
introduced.

The three observable shapes are:

- return: resolved working state, working effects, and return bytes; no trap
  rollback selection;
- revert: parent state and rollback with accumulated working trace and revert
  bytes; no trap rollback selection; and
- trap: the exact reason plus the parent state and rollback with accumulated
  working trace.

The pair is a read-only view. Producing it does not mutate a parent, apply a
rollback, catch or propagate a trap, deliver bytes, or commit state.

## Exact proof interface

Publish exactly four non-simplification laws:

```lean
theorem resolveWithTrapRollback_returned
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.returned (TrapReason := TrapReason) data) :
    context.resolveWithTrapRollback =
        (FrameResolutionResult.returned
          context.result.working context.effectWorking data, none) ∧
      FrameTrace.IsPrefixOf
        parentWorking.2.trace context.effectWorking.trace

theorem resolveWithTrapRollback_reverted
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.reverted (TrapReason := TrapReason) data) :
    context.resolveWithTrapRollback =
        (FrameResolutionResult.reverted parentWorking.1
          ⟨parentWorking.2.rollback, context.effectWorking.trace⟩ data,
          none) ∧
      FrameTrace.IsPrefixOf
        parentWorking.2.trace context.effectWorking.trace

theorem resolveWithTrapRollback_trapped
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (reason : TrapReason)
    (outcomeEq : context.result.outcome = FrameOutcome.trapped reason) :
    context.resolveWithTrapRollback =
        (FrameResolutionResult.trapped reason,
          some
            (parentWorking.1,
              ⟨parentWorking.2.rollback, context.effectWorking.trace⟩)) ∧
      FrameTrace.IsPrefixOf
        parentWorking.2.trace context.effectWorking.trace

theorem resolveWithTrapRollback_snd_eq_some_iff
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (values :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) :
    (context.resolveWithTrapRollback).2 = some values ↔
      ∃ reason,
        context.result.outcome = FrameOutcome.trapped reason ∧
          values =
            (parentWorking.1,
              ⟨parentWorking.2.rollback, context.effectWorking.trace⟩)
```

The returned and reverted laws reuse the existing parent-indexed resolver
laws. The trapped law combines the generic reason-only resolution with the
already accepted trap rollback. Each branch also returns the existing trace
prefix proof. All four laws must report only `[propext]`.

No law claims that the selected rollback was applied. No theorem turns a trap
into return, revert, success, or failure.

## Required regressions

Add compile-only consumers that:

- apply all four public laws directly;
- pass the first component through the existing bytes-aware returned and
  reverted continuation callbacks;
- recover the exact parent rollback pair from the trapped component;
- show together that a trap rejects both returned/reverted callbacks in the
  first component while selecting the exact rollback in the second;
- transport ADR-0125 whole-context completion equality through the first
  resolution component of the new view;
  and
- transport ADR-0125 completed larger-fuel stability without changing any
  optional boundary.

No new runtime fixture is required. Existing definition-only tests already
execute all three total-resolution branches, all three trap-rollback branches,
and the trap propagation payload. ADR-0124 and ADR-0125 separately execute and
construct the completed producer. The new operation only pairs those tested
components.

## Dependency boundary

Use `ParentIndexedFrameResolutionView.lean` for the definition,
`ParentIndexedFrameResolutionViewProperties.lean` for the four laws, and
`Solcore/Test/ParentIndexedFrameResolutionView.lean` for compile consumers.
The definition imports the existing parent-indexed resolver and trap rollback;
the properties module imports their laws. The test may import ADR-0125
completion coherence. Production adds no direct selected-execution or
HostDriver import, and Core gains no reverse dependency on the frame layer.

The operation is re-exported only through the internal Semantics facade. It
does not change Core, host requests, WorldState, execution, fuel, parser,
source syntax, ABI, Wire, schemas, profiles, or the root README.

## Non-goals

This ADR does not define:

- a transaction checkpoint, root frame, commit, rollback application, or
  atomicity;
- checkpoint creation, ownership, lifetime, or provenance;
- a parent machine, parent mutation, resumption, stack, or scheduler;
- return or revert byte delivery, ABI conversion, or callback policy;
- trap catch, fatality, propagation, classification, or recovery;
- the final treatment of storage absence, code absence, out-of-fuel, or a raw
  machine fault;
- concrete log survival or public trace semantics;
- caller, current address, call value, calldata, or call kind; or
- source syntax, gas, EVM revision behavior, or publication.

## Implemented sequence

The work was completed in this order:

1. record and activate the exact frame-local view;
2. add the pure pairing operation and Semantics export;
3. add the four exact laws;
4. add compile-only consumers through existing resolution and ADR-0125
   completion interfaces; and
5. run full validation and independent audit, then synchronize acceptance
   evidence and current-facing internal documents.

## Implementation record

`ParentIndexedFrameResolutionView.lean` defines only the read-only pair
`(context.resolve, context.trapRollback?)` and exports it through the internal
Semantics facade. It adds no carrier, branch calculation, mutation, or policy.

`ParentIndexedFrameResolutionViewProperties.lean` publishes exactly the four
specified non-simp laws. Return and revert reuse the existing parent-indexed
resolver laws; trap combines the existing reason-only resolution with the
existing exact rollback selector. The inverse law proves that a value appears
in the second component exactly on the trapped branch and fixes the complete
selected pair.

The compile-only consumer applies all four laws directly. It routes return and
revert bytes through the existing callbacks, checks trap callback rejection
and rollback selection together, transports ADR-0125 whole-context coherence
through the first component, and keeps all three selected-execution optional
layers under additional fuel.

## Acceptance evidence

- the full build completed 630 jobs;
- the complete test suite completed 1,148 jobs and all runtime checks passed;
- every changed Lean module compiled with trust zero and warnings as errors;
- metadata and semantic-kernel policy checks passed;
- all four public laws report exactly `[propext]`;
- no new simplification rule, unchecked declaration, runtime branch, or public
  format was added; and
- independent production and regression audits found no P0-P3 issue.

The parser, source syntax, Core, host protocol, WorldState, execution, fuel, ABI,
Wire formats, schemas, profiles, and root README did not change.

## Consequences

A future caller can inspect one branch-complete view containing both the
ordinary resolution and the opt-in trap rollback selection. Return, revert,
and trap stay distinguishable, and the existing trace-prefix evidence remains
available.

Actual transaction finalization remains blocked until the repository defines
root checkpoint provenance and lifetime, complete terminal disposition, and a
final observation or persistence boundary.
