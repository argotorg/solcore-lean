# ADR-0095: Address-bound working storage read

- Status: Accepted
- Decision date: 2026-08-29
- Scope: read working storage through a retained storage address
- Implementation: Complete

## Context

ADR-0093 retains one caller-designated storage address beside checkpointed
working values and already uses it for writes. ADR-0094 now provides the
canonical WorldState read that distinguishes an absent Account from a missing
slot in a present Account.

The next frame-facing boundary should connect those decisions. A caller should
supply only a slot, while the operation selects the carrier's stored address
and the working WorldState. Defining a second account-lookup rule here would
duplicate ADR-0094, and accepting another address would undo ADR-0093.

## Decision

Add exactly one public operation in a new module:

```lean
namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- Read one slot from the stored address in the working WorldState. -/
def readStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot : Core.Word) : Option Core.Word :=
  context.values.working.1.readStorage? context.storageAddress slot

end Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress
```

The operation has no address argument and reads only `values.working.1`. It
does not consult `values.checkpoint.state`. Its result delegates exactly to
ADR-0094: an absent working Account returns `none`; a present Account with a
missing or deleted slot returns `some Core.Word.zero`; a stored nonzero value
returns `some value`.

The operation is a pure observation and does not return a rebuilt carrier. The
operation and its single generated equation must report exactly `[propext]`.
Add no alternate-address overload, checkpoint read, defaulting wrapper,
account-returning variant, selector projection law, coercion, instance, or
second operation.

## Required proof interface

Publish exactly two simp laws:

```lean
namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

@[simp] theorem readStorage?_of_absent
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot : Core.Word)
    (absent :
      context.values.working.1.account? context.storageAddress = none) :
    context.readStorage? slot = none

@[simp] theorem readStorage?_of_present
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (account : Account)
    (slot : Core.Word)
    (present :
      context.values.working.1.account? context.storageAddress = some account) :
    context.readStorage? slot = some (account.storageRead slot)

end Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress
```

Both proofs must reuse the ADR-0094 laws and report exactly `[propext]`. Their
hypotheses are exclusive and both conclusions eliminate the carrier-level
operation, so they introduce no simp loop.

Add no checkpoint specialization, empty or stored-slot specialization,
read-after-write law, write-after-read law, unchanged-carrier theorem, generic
delegation law beyond the generated equation, reverse rule, or resolution
coherence theorem here.

## Required runtime regressions

Add exactly three runtime assertions importing only the new definition module.
Do not import or invoke either law. One public test function and private fixture
or observation helpers are permitted. The runner imports the module and calls
the function exactly once.

Use distinct addresses, slots, checkpoint values, and working values.

1. A stored address present in the checkpoint but absent from the working
   state returns `none`, even when another working Account is present.
2. The same checkpoint address paired with a present empty working Account
   returns `some zero`, not the checkpoint's nonzero value.
3. Two carriers over the same working state but with different stored addresses
   return their respective exact values; a second slot sentinel detects slot
   selection errors.

The tests invoke no laws, carrier write operation, context adapter, resolver,
continuation, scheduler, or external effect other than failed-assert reporting.

## Dependency boundary

The definition module imports exactly the ADR-0093 carrier module and
`Solcore.Semantics.WorldStateStorageRead`. Its properties module imports exactly
the new definition and `WorldStateStorageReadProperties`. The semantic umbrella
imports both after the ADR-0093 modules and before the continuation-context
adapter. The runtime test imports only the new definition; the runner adds one
import and one call.

Existing WorldState, carrier, write, checkpoint, context, resolution, and
continuation APIs remain unchanged.

## What this slice does not decide

The stored address is still not a current contract, callee, code address,
caller, owner, or authorized principal. The operation is not SLOAD and adds no
account creation, balance, nonce, code, value transfer, call kind, storage
layout, access warmth, refund, gas, ABI, serialization, EVM revision,
checkpoint lifecycle, rollback, outcome, trap, parent mutation, stack,
scheduling, transaction, delta, or published observation rule.

It performs no mutation, does not validate checkpoint/working relationships,
and does not make an absent Account read as zero. It adds no parser or source
syntax, Core expression, Wire field, Profile, or frozen artifact.

## Staged implementation plan

Keep each of five commits below 300 changed lines: this decision and targeted
roadmap updates; the exact operation and umbrella import; the exact two laws
and umbrella import; the exact three runtime assertions plus one runner import
and call; independent audit and completion evidence.

## Implementation record

The completed slice adds exactly one operation in a 20-line definition module
plus one umbrella import. It passes the carrier's working WorldState, retained
storage address, and caller-supplied slot directly to ADR-0094. The operation
and its generated equation report exactly `[propext]`.

A 37-line properties module plus one umbrella import publishes exactly the two
required simp laws. Each proof delegates directly to the matching ADR-0094 law.
Both report exactly `[propext]`; their exclusive hypotheses and one-way
reductions introduce no critical overlap or simplification loop.

An 84-line definition-only test module plus one runner import and one call
contains exactly three runtime assertions. They reject checkpoint fallback and
unrelated-account rescue, distinguish working Account absence from a present
empty Account, and verify all four combinations of two retained addresses and
two slots against distinct working values.

The implementation commits are `c905bef` (186 changed lines), `8d702dd` (24),
`4563d31` (38), and `ba00324` (86), all below 300 changed lines; this completion
update is the fifth staged commit. Focused trust-zero checks, full build and
test runs, metadata and kernel checks, diff checks, simp review, declaration
inventory, and independent P0-P3 audits pass.

## Publication and consequences

This internal operation is not published. Frame-facing consumers can now read
working storage through one retained selector without repeating WorldState
absence semantics or accepting a fresh address. Code address, caller, callee,
and contract-entry data can remain separate later fields.
