# ADR-0097: Address-bound working storage read/write coherence

- Status: Accepted
- Decision date: 2026-08-29
- Scope: stage-preserving reads after address-bound working storage writes
- Implementation: Planned

## Context

ADR-0093 gives checkpointed working values one retained storage address and a
conditional write operation. ADR-0095 adds the matching working-state read,
and ADR-0096 proves the underlying WorldState read/write laws. The carrier
operations are already useful together, but callers still have to unfold both
carrier lifts before the WorldState laws apply.

This slice closes that proof boundary. It adds no operation, address role, or
checkpoint policy.

## Decision

Publish exactly two simp laws:

```lean
namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

@[simp] theorem readStorage?_writeStorage?_same
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map
        (fun next => next.readStorage? slot) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => some value)

@[simp] theorem readStorage?_writeStorage?_other_slot
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (writtenSlot value readSlot : Core.Word)
    (different : readSlot ≠ writtenSlot) :
    (context.writeStorage? writtenSlot value).map
        (fun next => next.readStorage? readSlot) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => context.readStorage? readSlot)

end Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress
```

Both laws preserve the outer conditional-write stage with `Option.map`. If the
retained address is absent from the working WorldState, the result is outer
`none`. If the write succeeds, the same-slot read is `some (some value)` and a
different-slot read preserves the original carrier-level observation inside
the successful branch.

The carrier accepts no fresh address, so there is no carrier-level
different-address law. That case remains available at the underlying
WorldState boundary in ADR-0096.

Both laws eliminate a mapped write-then-read observation and have no reverse
form. The same-slot and different-slot cases are separated by the disequality
hypothesis, so both are simplification rules. Each law must report exactly
`[propext]`.

Add no executable API, carrier, helper, other-address law, selector or
checkpoint preservation duplicate, Account-presence specialization, flattened
`Option.bind` theorem, mutation-order claim, or exactly-once claim.

## Required compile regressions

Add exactly two private compile examples importing only the new properties
module, one per public law. Each example must use the corresponding law through
the simp interface.

There is no public test function, runtime declaration, runtime assertion, or
runner call. The test runner imports the compile-only module exactly once.
Existing definition-boundary tests already exercise successful and failing
carrier reads and writes; this slice tests only their combined proof interface.

## Dependency boundary

`FrameCheckpointedWorkingPairWithStorageAddressStorageReadWriteProperties.lean`
imports exactly
`FrameCheckpointedWorkingPairWithStorageAddressStorageRead` and
`WorldStateStorageReadWriteProperties`. It unfolds the two established carrier
operations and reuses ADR-0096 rather than reproving Account storage behavior.

The semantic umbrella imports the new module after the WorldState coherence
module. The compile-only regression imports only the new module; the runner
adds one import and no call. Existing definitions and theorem statements remain
unchanged.

## What this slice does not decide

The retained address is still only a caller-supplied selector. It is not proved
to be a current contract, callee, code address, caller, owner, or authorized
principal. This slice adds no Account creation, code, balance, nonce, value
transfer, call data, call kind, frame entry, checkpoint creation, ownership,
lifetime, outcome provenance, trace append, stack, scheduling, recursion,
reentrancy, gas, ABI, transaction, host I/O, or published observation rule.

The equalities are pure nested `Option` observations. They make no concurrent
mutation, cost, evaluation-count, or external-effect claim. They add no parser
or source syntax, Core expression, Wire or Oracle field, Profile, or frozen
artifact.

## Staged implementation plan

Keep each of four commits below 300 changed lines: this decision and targeted
documentation updates; the exact two laws plus one umbrella import; the exact
two compile regressions plus one runner import and no call; independent audit
and completion evidence.

## Publication and consequences

This proof-only layer is not published. Consumers of the existing
address-bound carrier can normalize a working-storage read after a write
without unfolding the carrier or WorldState implementations.

After this slice, checkpoint initialization, child working-state construction,
address roles, invocation inputs, and outcome provenance must be audited
together before adding an entry carrier. Parser, ABI, gas, transaction, and
host policies remain outside that audit.
