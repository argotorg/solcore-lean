# ADR-0094: Conditional WorldState storage read

- Status: Accepted
- Decision date: 2026-08-28
- Scope: read one storage slot while preserving explicit account absence
- Implementation: Complete

## Context

ADR-0056 gives `Account.storageRead` a total, zero-default meaning once an
Account is available. It also keeps an absent Account distinct from a present
empty Account. Callers that start with a WorldState must currently combine
`WorldState.account?` and `Account.storageRead` themselves.

ADR-0093 binds a storage address to checkpointed working values. Before that
carrier receives a read operation, the account-presence and slot-read
composition needs one canonical WorldState definition. Otherwise a
frame-specific implementation would duplicate the rule and become a second
authority for absence behavior.

## Decision

Add exactly one public operation in a new module:

```lean
namespace Solcore.Semantics.WorldState

/-- Read a slot only when its Account is explicitly present. -/
def readStorage?
    (state : WorldState)
    (address : Address)
    (slot : Core.Word) : Option Core.Word := do
  let account ← state.account? address
  some (account.storageRead slot)

end Solcore.Semantics.WorldState
```

The `Option` records only Account presence. An absent Account returns `none`.
A present Account always returns `some`; a missing or deleted slot uses
`Account.storageRead` and therefore returns `some Core.Word.zero`. A stored
nonzero value returns `some value`.

The operation is a pure observation. It does not update the WorldState or
normalize an absent Account into an empty Account. The operation and its one
generated equation must report exactly `[propext]`.

Add no second read operation, non-optional defaulting wrapper, account-returning
variant, presence predicate, address default, state projection, coercion,
instance, or update operation.

## Required proof interface

Publish exactly two simp laws:

```lean
namespace Solcore.Semantics

@[simp] theorem WorldState.readStorage?_of_absent
    (state : WorldState)
    (address : Address)
    (slot : Core.Word)
    (absent : state.account? address = none) :
    state.readStorage? address slot = none

@[simp] theorem WorldState.readStorage?_of_present
    (state : WorldState)
    (address : Address)
    (account : Account)
    (slot : Core.Word)
    (present : state.account? address = some account) :
    state.readStorage? address slot = some (account.storageRead slot)

end Solcore.Semantics
```

Both hypotheses are exclusive and both conclusions eliminate `readStorage?`,
so the simp rules have one direction and no loop. Both laws must report exactly
`[propext]`.

Add no empty-state specialization, missing-slot or stored-slot theorem,
read-after-write law, unchanged-state theorem, extensionality theorem, frame
lift, reverse rule, or relation to `storageValue?` in this slice. Those facts
are either direct consequences or belong to a later composition layer.

## Required runtime regressions

Add exactly three runtime assertions importing only the new definition module.
Do not import or invoke either law. One public test function and private fixture
or observation helpers are permitted. The runner imports the test module and
calls the function exactly once.

Use two distinct addresses, a selected slot, a different slot, and distinct
nonzero values.

1. Reading an absent target returns `none` even when another Account is present.
2. Reading a missing slot from a present empty Account returns `some zero`.
3. Reading a stored nonzero value returns exactly that value while distinct
   address and slot sentinels demonstrate correct selection.

The tests call no write law, frame carrier, context, resolver, continuation,
scheduler, or external effect other than reporting a failed assertion.

## Dependency boundary

`WorldStateStorageRead.lean` imports exactly `Solcore.Semantics.WorldState`.
Its properties module imports exactly the new definition module. The semantic
umbrella imports both after WorldState and before frame checkpoint modules.
The runtime test imports only the definition module; the runner adds one import
and one call.

Existing Account, WorldState, write, checkpoint, frame, resolution, and
continuation APIs remain unchanged. The later address-bound lift must delegate
to this operation rather than repeat its lookup rule.

## What this slice does not decide

This is not an SLOAD opcode rule and does not identify the address as current,
authorized, called, owned, or code-bearing. It adds no account creation,
balance, nonce, code, call kind, value transfer, storage layout, access warmth,
refund, gas, ABI, serialization, EVM revision, checkpoint, rollback, outcome,
trap, stack, scheduling, transaction, delta, or observation policy.

It does not reinterpret an absent Account as zero storage. `none` remains a
strictly different result from `some Core.Word.zero`. It adds no parser or
source syntax, Core expression, Wire field, Profile, or published format.

## Staged implementation plan

Keep each of five commits below 300 changed lines: this decision and targeted
roadmap updates; the exact operation and umbrella import; the exact two laws
and umbrella import; the exact three runtime assertions plus one runner import
and call; independent audit and completion evidence.

## Implementation record

The completed slice adds exactly one operation in a 17-line definition module
plus one umbrella import. `WorldState.readStorage?` binds only explicit Account
lookup and then returns `some (account.storageRead slot)`. The operation and its
generated equation report exactly `[propext]`.

A 28-line properties module plus one umbrella import publishes exactly the two
required simp laws. Their exclusive hypotheses reduce Account absence to
`none` and Account presence to the existing zero-default read. Both laws report
exactly `[propext]`, with no reverse rule or simplification loop.

A 56-line definition-only test module plus one runner import and one call
contains exactly three runtime assertions. They distinguish an absent target
from an unrelated present Account, distinguish `none` from a present missing
slot's `some zero`, and verify exact address-and-slot selection for nonzero
values.

The implementation commits are `bde695e` (178 changed lines), `8f2a89c` (18),
`03f2be3` (29), and `0d6872b` (58), all below 300 changed lines; this completion
update is the fifth staged commit. Focused trust-zero checks, full build and
test runs, metadata and kernel checks, diff checks, simp review, declaration
inventory, and independent P0-P3 audits pass.

## Publication and consequences

This internal operation is not published and changes no frozen artifact. It
establishes one reusable boundary between Account absence and zero-default slot
reads. The next frame-level storage-read slice can now select its stored address
and delegate without redefining either meaning.
