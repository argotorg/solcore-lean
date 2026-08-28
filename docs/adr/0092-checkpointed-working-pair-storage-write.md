# ADR-0092: Checkpointed working-pair storage write

- Status: Accepted
- Decision date: 2026-08-28
- Scope: conditional storage update of only the working world state
- Implementation: Not started

## Context

`WorldState.writeStorage?` already defines a strict internal storage update. It
updates an explicitly present account, stores a nonzero word, deletes the
selected slot for zero, and returns `none` when the account is absent.
ADR-0087 pairs a caller-supplied checkpoint with an independent working
state/effect pair, but deliberately adds no operation.

The first concrete working-state transition on that carrier should lift the
existing storage operation to only its working world state. The checkpoint and
the complete working effect journal must remain unchanged. This connects a
real WorldState transition to checkpointed frame data without deciding
checkpoint creation, frame ownership, or transaction behavior.

## Decision

Add exactly one public operation:

```lean
namespace Solcore.Semantics.FrameCheckpointedWorkingPair

universe u v

/-- Conditionally update storage in only the working world state. -/
def writeWorkingStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (address : Address) (slot value : Core.Word) :
    Option (FrameCheckpointedWorkingPair RollbackState TraceState) :=
  (values.working.1.writeStorage? address slot value).map fun state =>
    ⟨values.checkpoint, (state, values.working.2)⟩

end Solcore.Semantics.FrameCheckpointedWorkingPair
```

The address, slot, and value are caller inputs. The address is not designated
as the current contract, callee, owner, or otherwise authorized principal.
The operation only lifts the existing WorldState rule.

Success returns a new immutable carrier. The exact checkpoint value and the
entire working journal are reused. Only `working.1` changes. Failure is decided
only by account absence in `values.working.1`; an account present at the same
address in the checkpoint does not make the write succeed or create a working
account.

A zero value inherits the existing `Account.storageWrite` meaning: delete the
selected storage slot while retaining the present account. It does not delete
the account or signal a revert.

The operation and its single generated equation must report exactly
`[propext]`. Add no non-optional alias, checkpoint-writing variant, account-
creating fallback, address default, current-account wrapper, reverse adapter,
coercion, instance, or second operation.

## Required proof interface

Publish exactly two simp laws:

```lean
namespace Solcore.Semantics.FrameCheckpointedWorkingPair

universe u v

@[simp] theorem writeWorkingStorage?_of_absent
    {RollbackState : Type u} {TraceState : Type v}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (address : Address) (slot value : Core.Word)
    (absent : values.working.1.account? address = none) :
    values.writeWorkingStorage? address slot value = none

@[simp] theorem writeWorkingStorage?_of_present
    {RollbackState : Type u} {TraceState : Type v}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (address : Address) (account : Account)
    (slot value : Core.Word)
    (present : values.working.1.account? address = some account) :
    values.writeWorkingStorage? address slot value =
      some ⟨values.checkpoint,
        (values.working.1.putAccount address
          (account.storageWrite slot value), values.working.2)⟩

end Solcore.Semantics.FrameCheckpointedWorkingPair
```

Both proofs expose only the new operation and existing WorldState definition.
Both laws must report exactly `[propext]`. Their right sides already make
checkpoint and journal preservation exact; add no projection duplicates,
success-existence theorem, bind law, overwrite/commutation lift, zero-specific
law, resolution coherence, or reverse rule in this slice.

## Required runtime regressions

Add exactly three runtime assertions importing only the new definition module.
One public test function and one private assertion helper are permitted;
additional fixture and observation helpers remain private. The test runner
imports the module and calls the test function exactly once.

Use two distinct addresses, two distinct slots, distinct checkpoint and working
slot values, a nonzero replacement, distinct checkpoint and working rollback
values, and distinct nonempty traces. The working-present fixture also retains
an unrelated slot at the selected account and an unrelated account.

The first assertion uses a checkpoint where the selected account exists and a
working world where it is absent. It checks both fixture conditions and that
the operation returns `none`, detecting any lookup against the checkpoint or
implicit account creation.

The second assertion writes the nonzero replacement. It checks the new working
slot and exact preservation of the checkpoint state sentinel, checkpoint
journal, working journal, unrelated slot, and unrelated account.

The third assertion writes zero. It checks that the working account remains
present, the selected slot is absent and reads as zero, and the same checkpoint,
journal, unrelated-slot, and unrelated-account observations remain unchanged.

The tests import or invoke no laws. They call no context adapter, resolver,
continuation, outcome, trace-extension, parent-indexed operation, scheduler, or
external effect other than reporting a failed assertion.

## Dependency boundary

`FrameCheckpointedWorkingPairStorageWrite.lean` imports exactly
`Solcore.Semantics.FrameCheckpointedWorkingPair`. Its properties module imports
exactly the new definition module.

The semantic umbrella imports the definition and properties immediately after
the carrier and before the ADR-0088 context adapter. The test module imports
only the new definition. The runner adds one import and one call. Existing
WorldState, Account, checkpoint, context, resolution, and continuation APIs
remain unchanged.

## What this operation does not decide

The operation does not identify the caller-selected address with a current
contract, establish write authorization, create an absent account, or change
balances, code, nonce, transferred value, call data, or ownership.

It does not capture or validate the checkpoint, initialize the working state,
prove provenance or freshness, update rollback data, append a trace or log,
produce an outcome, resolve or continue a frame, mutate a parent, manage a
stack, schedule work, enforce depth or reentrancy, or decide transaction commit
or atomic rollback.

Its `none` means only that the addressed account was absent from the working
WorldState. It is not a revert, trap, diagnostic, permission failure, or
inconclusive execution.

It does not connect Core local cells to contract storage or decide storage
layout, access warmth, refunds, gas, ABI, serialization, EVM revision, opcode
behavior, parser or source syntax, Wire or Oracle fields, Profile, canonical
delta, or published observation.

## Staged implementation plan

Keep each of five commits below 300 changed lines: this decision and internal
roadmap update; the exact one operation and umbrella import; the exact two laws
and umbrella import; the exact three runtime assertions with one runner import
and call; independent audit and completion evidence.

## Publication and exclusions

This internal working-state update is not published. It changes no frozen
artifact, schema, profile, capability report, or public format.

## Consequences

Once implemented, callers can apply the established strict storage-write rule
to a checkpointed carrier without manually rebuilding it or risking accidental
checkpoint or journal replacement. The operation remains a pure function that
returns a new value.

Checkpoint creation, concrete frame identity, broader account state, parent
resumption, scheduling, trap disposition, and transaction atomicity remain
separate decisions.
