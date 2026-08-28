# ADR-0093: Checkpointed working-pair storage address

- Status: Accepted
- Decision date: 2026-08-28
- Scope: bind one caller-designated storage address to checkpointed working values
- Implementation: Complete

## Context

ADR-0092 lifts `WorldState.writeStorage?` to
`FrameCheckpointedWorkingPair`, but every write still accepts an unrestricted
address argument. A later caller can therefore select a different account for
each write even when several writes belong to one intended frame scope.

The next runtime boundary should retain one storage target beside the
checkpointed working values and remove the address argument from subsequent
writes. This is narrower than defining a complete current frame. In
particular, a storage address need not later equal a code address, callee,
caller, owner, or any address introduced by contract entry.

Lifted overwrite or commutation laws would only specialize ADR-0059. Likewise,
write-then-resolution laws would specialize the existing ADR-0088 resolution
path. Those proof-only consequences remain derivable but do not close the
missing value boundary, so they are not selected for this slice.

## Decision

Add exactly one public carrier:

```lean
namespace Solcore.Semantics

universe u v

/-- A caller-designated storage address paired with checkpointed working values. -/
structure FrameCheckpointedWorkingPairWithStorageAddress
    (RollbackState : Type u) (TraceState : Type v) : Type (max u v) where
  storageAddress : Address
  values : FrameCheckpointedWorkingPair RollbackState TraceState

end Solcore.Semantics
```

`storageAddress` is only a stored selector. Construction does not prove that
the address is present, authorized, current, or associated with an invocation.
`values` remains the exact ADR-0087 carrier, including its independent
checkpoint and working pair.

Add exactly one public operation:

```lean
namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- Write the stored address's working storage while retaining its scope. -/
def writeStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    Option
      (FrameCheckpointedWorkingPairWithStorageAddress
        RollbackState TraceState) :=
  (context.values.writeWorkingStorage?
      context.storageAddress slot value).map fun values =>
    ⟨context.storageAddress, values⟩

end Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress
```

The operation has no address argument. It delegates the conditional update to
ADR-0092 and preserves the stored address on success. Failure remains exactly
the absence of `context.storageAddress` from the working WorldState.

The intentional public surface is exactly one carrier and one operation, plus
the operation's single generated equation and the two laws below. The
carrier's generated constructor, recursor, and two projections are the
ordinary unavoidable structure API; add no custom constructor, projection
alias, coercion, instance, default, validity predicate, or second operation.

The carrier, its generated declarations, the operation, and the generated
operation equation must report exactly `[propext]`.

## Required proof interface

Publish exactly two simp laws:

```lean
namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

@[simp] theorem writeStorage?_of_absent
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word)
    (absent :
      context.values.working.1.account? context.storageAddress = none) :
    context.writeStorage? slot value = none

@[simp] theorem writeStorage?_of_present
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (account : Account)
    (slot value : Core.Word)
    (present :
      context.values.working.1.account? context.storageAddress = some account) :
    context.writeStorage? slot value =
      some
        ⟨context.storageAddress,
          ⟨context.values.checkpoint,
            (context.values.working.1.putAccount context.storageAddress
                (account.storageWrite slot value),
              context.values.working.2)⟩⟩

end Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress
```

Both proofs must reuse the ADR-0092 branch laws and report exactly `[propext]`.
Their hypotheses are exclusive and both reductions remove `writeStorage?`, so
the simp rules converge without a reverse rule or loop.

Add no custom carrier projection law, storage-address identity law, success
existence theorem, bind law, overwrite or commutation lift, zero-specific law,
write-resolution coherence theorem, or relation to another address.

## Required runtime regressions

Add exactly three runtime assertions. Import only the new definition module;
do not import or invoke either law. One public test function and private fixture
or observation helpers are permitted. The runner imports the test module and
calls the test function exactly once.

Use one checkpointed working value with two distinct present working accounts,
distinct addresses and stored values, distinct checkpoint and working values,
distinct rollback sentinels, and distinct nonempty traces.

1. A context whose stored address is absent from working state returns `none`,
   even when another working account and the selected checkpoint account exist.
2. A context selecting the first present address updates only that address and
   preserves the second account, stored address, checkpoint, and whole working
   journal.
3. A context over the same base values selecting the second address updates
   only that address and preserves the first account, stored address,
   checkpoint, and whole working journal.

Use nonzero replacement values in the two successful assertions. Zero deletion
is already covered at the delegated ADR-0092 boundary and must not be repeated
as a fourth assertion.

## Dependency boundary

`FrameCheckpointedWorkingPairWithStorageAddress.lean` imports exactly
`Solcore.Semantics.FrameCheckpointedWorkingPairStorageWrite`. Its properties
module imports exactly the new definition module and
`Solcore.Semantics.FrameCheckpointedWorkingPairStorageWriteProperties` so the
two proofs reuse the public delegated laws.

The semantic umbrella imports the definition and properties directly after
the ADR-0092 properties module and before the ADR-0088 context adapter. The
runtime regression imports only the new definition module. The test runner
adds one import and one call. Existing WorldState, checkpointed-pair, context,
resolution, and continuation APIs remain unchanged.

## What this slice does not decide

The stored address is not asserted to be a current contract, callee, code
address, caller, origin, owner, or authorized principal. The carrier proves no
address provenance, account presence, invocation occurrence, lifetime, frame
identity, ancestry, or uniqueness.

The operation does not create an account, select code, transfer value, accept
call data, initialize or capture a checkpoint, change rollback data, append a
trace or log, produce an outcome, resolve or continue a frame, mutate a parent,
manage a stack, schedule work, enforce depth or reentrancy, or choose trap or
transaction behavior.

It adds no balance, nonce, call-kind or delegate-call rule, Core-local-store
bridge, storage layout, access warmth, refund, gas, ABI, serialization, EVM
revision, parser or source syntax, Wire or Oracle field, Profile, canonical
delta, or published observation. It performs no in-place mutation.

## Staged implementation plan

Keep each of five commits below 300 changed lines: this decision and the three
targeted documentation updates; the exact carrier and operation plus one
umbrella import; the exact two laws plus one umbrella import; the exact three
runtime assertions plus one runner import and call; independent audit and
completion evidence.

## Implementation record

The completed slice adds one 34-line definition module plus one umbrella
import. Its single carrier retains a caller-supplied storage selector beside
the existing checkpointed working values. Its single operation accepts only a
slot and value, delegates to ADR-0092 with that stored selector, and retains
the selector on success.

One 44-line properties module plus one umbrella import publishes exactly the
two required simp laws. Both reuse the ADR-0092 branch laws, terminate at the
explicit absent or present result, and report exactly `[propext]`. The carrier,
its generated declarations, the operation, and its generated equation also
report exactly `[propext]`.

One 94-line definition-only test module plus one runner import and one call
contains exactly three runtime assertions. They reject lookup through an
unrelated working account or the checkpoint and verify symmetric selection of
two stored addresses while preserving the checkpoint, both journal fields,
the selector, and the unselected account.

The implementation commits are `aa74372` (251 changed lines), `b9103a6` (35),
`b5e914a` (45), and `fab671e` (96), all below 300 changed lines; this completion
update is the fifth staged commit. Focused trust-zero checks, full build and
test runs, metadata and kernel checks, diff checks, declaration inventories,
simp review, and independent P0-P3 audits pass.

## Publication and exclusions

This internal carrier and operation are not published. They change no frozen
artifact, schema, profile, capability report, or public format.

## Consequences

Later working-storage transitions can obtain their target from one retained
field instead of accepting an unrestricted address at every call. Repeated
successful writes preserve that selector together with the checkpoint and
working journal.

Contract entry may later supply a storage address and separately introduce
code, caller, or callee addresses. This decision does not require those values
to coincide.
