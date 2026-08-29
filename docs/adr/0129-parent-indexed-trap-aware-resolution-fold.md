# ADR-0129: Parent-indexed trap-aware resolution fold

- Status: Accepted
- Decision date: 2026-08-29
- Scope: caller-owned elimination of all three parent-indexed frame outcomes
- Implementation: Not started

## Context

ADR-0089 lets a caller continue an ordinary `FrameResolutionResult` through
separate return and revert callbacks. A trap deliberately produces `none`
because the ordinary result carries only a reason and has no rollback policy.

ADR-0127 later added the missing parent-indexed observation without changing
that generic contract. `resolveWithTrapRollback` pairs the ordinary total
resolution with an optional exact parent rollback pair. Its compile consumer
must currently inspect the first component with `continue?` and inspect the
second component separately to handle a trap.

The two observations now contain enough value-level information for a caller
to choose one of three pure functions. They still do not contain a parent
machine, rollback application, byte-delivery rule, scheduler, or transaction
boundary.

The next safe operation is therefore an eliminator, not a transition. It must
pass exact values to caller-owned functions and return their chosen result
without interpreting it.

## Decision

Add exactly one parent-indexed, context-first fold:

```lean
namespace Solcore.Semantics.ParentIndexedFrameContinuationContext

universe u v w x

def foldResolutionWithTrapRollback
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {Next : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        TrapReason → Next) : Next :=
  match context.result.outcome with
  | .returned data =>
      onReturned (context.result.working, context.effectWorking) data
  | .reverted data =>
      onReverted
        (context.stateCheckpoint,
          ⟨context.effectCheckpoint.rollback, context.effectWorking.trace⟩)
        data
  | .trapped reason =>
      onTrapped
        (context.stateCheckpoint,
          ⟨context.effectCheckpoint.rollback, context.effectWorking.trace⟩)
        reason

end Solcore.Semantics.ParentIndexedFrameContinuationContext
```

`Next` is an arbitrary caller-selected type. The fold adds no `Option`, error,
or diagnostic layer. A caller that needs partiality may choose
`Next := Option Result`; a caller that needs a total marker may choose an
ordinary inductive type.

The fold name refers to the exact rollback values supplied to the trap
callback. It does not mean that rollback is applied.

## Branch meanings

- Return selects `onReturned` with the terminal working WorldState, terminal
  working journal, and exact return bytes.
- Revert selects `onReverted` with the indexed parent WorldState, indexed
  parent rollback component, accumulated working trace, and exact revert
  bytes.
- Trap selects `onTrapped` with the same exact parent rollback pair and the
  exact trapped reason.

The definition matches the original outcome rather than the unrefined product
type returned by ADR-0127. This avoids inventing behavior for impossible
combinations such as a trapped resolution with no rollback selection. The
coherence law below proves that the three callback inputs reconstruct the
ADR-0127 view exactly.

## Exact proof interface

Publish exactly four non-simplification laws.

The first three laws fix callback selection and every supplied value:

```lean
universe u v w x

variable {RollbackState : Type u} {Event : Type v}
variable {TrapReason : Type w} {Next : Type x}
variable {parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}

theorem foldResolutionWithTrapRollback_returned
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.returned (TrapReason := TrapReason) data)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        TrapReason → Next) :
    context.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onReturned (context.result.working, context.effectWorking) data

theorem foldResolutionWithTrapRollback_reverted
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (data : Bytes)
    (outcomeEq : context.result.outcome =
      FrameOutcome.reverted (TrapReason := TrapReason) data)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        TrapReason → Next) :
    context.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onReverted
        (parentWorking.1,
          ⟨parentWorking.2.rollback, context.effectWorking.trace⟩) data

theorem foldResolutionWithTrapRollback_trapped
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (reason : TrapReason)
    (outcomeEq : context.result.outcome = FrameOutcome.trapped reason)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        TrapReason → Next) :
    context.foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      onTrapped
        (parentWorking.1,
          ⟨parentWorking.2.rollback, context.effectWorking.trace⟩) reason
```

Under the same shared variables, the fourth law fixes coherence with ADR-0127:

```lean
theorem foldResolutionWithTrapRollback_reconstructs_view
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    context.foldResolutionWithTrapRollback
        (fun values data =>
          (FrameResolutionResult.returned values.1 values.2 data, none))
        (fun values data =>
          (FrameResolutionResult.reverted values.1 values.2 data, none))
        (fun values reason =>
          (FrameResolutionResult.trapped reason, some values)) =
      context.resolveWithTrapRollback
```

All four laws and the operation must report exactly `[propext]`. Add no simp
attribute, reverse reconstruction law, callback extensionality law, identity
law, fusion law, or second fold.

## Required runtime regressions

Add exactly three definition-only runtime assertions. Use distinct parent and
working WorldStates, rollback values, a parent-plus-nested trace, nonempty
return and revert bytes, and a concrete trap reason.

Each callback returns a distinct branch marker only after checking every value
it receives. The assertions must prove that return, revert, and trap select the
correct callback with the exact values. The test imports only the fold
definition, not its laws or ADR-0127.

One public test function and one runner call are sufficient. No new Core
execution fixture is required because this operation consumes a completed
context and does not execute Core.

## Required compile regressions

Use a separate compile-only module to:

- apply all four public laws directly;
- instantiate `Next := Option Marker` and show that a trapped outcome returns
  the trap callback's exact `some` value rather than creating `none` itself;
- extract an ADR-0125 completed parent-indexed context and apply the fold's
  reconstruction law to it without changing the three optional boundaries;
  and
- use ADR-0125 completed larger-fuel stability to show that the exact same
  parent context yields the exact same fold result at the larger budget.

The last two examples may depend on ADR-0125 only in the test layer. Do not add
a fold wrapper over its nested `Option` result.

## Dependency boundary

Use `ParentIndexedFrameResolutionFold.lean` for the operation and
`ParentIndexedFrameResolutionFoldProperties.lean` for the four laws. The
definition imports only the parent-indexed continuation context. The properties
module additionally imports ADR-0127's view laws.

Use `Solcore/Test/ParentIndexedFrameResolutionFold.lean` for definition-only
runtime checks and
`Solcore/Test/ParentIndexedFrameResolutionFoldProperties.lean` for compile
consumers. The test runner imports both and calls only the runtime test.

The Semantics facade exports the definition and properties after the ADR-0127
view and mapping-naturality modules. Core gains no reverse dependency on the
frame layer.

## Non-goals

This ADR does not define or claim:

- parent mutation, execution, resumption, byte delivery, or callback storage;
- rollback application, commit, persistence, atomicity, or transaction exit;
- a root frame, root checkpoint, checkpoint creation, ownership, or lifetime;
- trap catch, fatality, classification, propagation, recovery, or diagnostics;
- stack, call depth, scheduling, nested invocation, or reentrancy;
- callback evaluation count, runtime cost, fuel, gas, or exactly-once policy;
- trace-prefix evidence in callback arguments or a concrete event taxonomy;
- storage absence, code absence, out-of-fuel, or raw-fault disposition;
- a lift through ADR-0125's nested options;
- caller, current address, call value, calldata, call kind, balance, or
  authority; or
- parser, Surface, ABI, Wire, Oracle, schema, profile, EVM revision, or public
  format behavior.

## Implementation sequence

Keep each green commit below roughly 300 changed lines:

1. record and activate the exact fold contract;
2. add the one operation and Semantics export;
3. add the four exact laws and Semantics export;
4. add the three definition-only runtime assertions and runner call;
5. add compile consumers through the public laws and ADR-0125 producer;
6. run full validation and independent audit; and
7. synchronize completion evidence in current-facing internal documents.

## Consequences

A caller can consume return, revert, and trap through one total, pure function
while receiving the exact values already fixed by the parent-indexed context.
The reconstruction theorem prevents this eliminator from drifting away from
ADR-0127's branch-complete observation.

Actual parent resumption and transaction finalization remain blocked on the
missing parent machine, checkpoint provenance and lifetime, terminal failure
policy, and final persistence boundary.
