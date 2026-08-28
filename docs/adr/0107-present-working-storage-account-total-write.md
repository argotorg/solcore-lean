# ADR-0107: Present working storage Account total write

- Status: Accepted
- Decision date: 2026-08-29
- Scope: synchronously update a proven-present working Account and its context
- Implementation: Planned

## Context

ADR-0093 writes through an address-bound working context with an optional
result because the selected Account may be absent. ADR-0105 now retains that
Account and its working-state presence evidence, and ADR-0106 reads it without
another lookup or failure branch.

The corresponding total write must keep the evidence carrier internally
coherent after mutation. Updating only the stored Account would leave the
working WorldState stale; updating only the WorldState would leave the stored
Account and its proof indexed by the old snapshot. Re-running the optional
write and refinement would add redundant lookups and unreachable branches.

## Decision

Add exactly one total operation:

```lean
namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

def writeStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    FrameCheckpointedWorkingPairWithPresentStorageAccount
      RollbackState TraceState :=
  let storageAccount := context.storageAccount.storageWrite slot value
  let nextContext :
      FrameCheckpointedWorkingPairWithStorageAddress
        RollbackState TraceState :=
    ⟨context.context.storageAddress,
      ⟨context.context.values.checkpoint,
        (context.context.values.working.1.putAccount
          context.context.storageAddress storageAccount,
          context.context.values.working.2)⟩⟩
  ⟨nextContext, storageAccount, by
    simp [nextContext, WorldState.putAccount, WorldState.account?]⟩

end Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
```

The operation updates the stored Account and selected working-state entry with
the same `Account.storageWrite` result, then constructs evidence for that new
snapshot. It retains the selector, checkpoint, all non-selected Accounts, and
working effect journal. It executes no Account lookup and has no failure path.

Writing zero follows the existing Account semantics: the slot entry is deleted
but the selected Account remains explicitly present in the WorldState and in
the returned carrier.

## Required proof interface

Publish exactly one simp coherence law:

```lean
namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

@[simp] theorem context_writeStorage?_eq_some_writeStorage_context
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    context.context.writeStorage? slot value =
      some (context.writeStorage slot value).context

end Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
```

The proof applies the existing address-bound present-write law with
`context.storageAccount_present`. It normalizes the conditional write to the
context projection of the total write in one direction. Its critical pair with
the older present-write simp law converges on the same exact updated context.

The operation, its generated equation, and the public law must report exactly
`[propext]`. Add no optional write on the refined carrier, Account projection
law, preservation law, read-after-write law, public re-refinement theorem,
algebra law, lookup helper, coercion, instance, or alternative constructor.

## Required regressions

Add one definition-only runtime module with exactly three assertions:

1. a nonzero write to a present empty selected Account updates both the stored
   Account and selected working-state entry while retaining checkpoint,
   journal, and a non-selected Account;
2. writing zero deletes the selected slot in both views while the Account
   remains present; and
3. the returned carrier accepts another total write, with same-slot overwrite
   and a distinct slot preserved in both synchronized views.

Every assertion obtains its initial carrier through
`withPresentStorageAccount?` and invokes the new `writeStorage`. The runtime
module imports only the new definition, exposes one public test function, and
does not import proof laws or the total-read module.

Add one compile-only module with exactly three private examples. The first
names the conditional/total coherence law directly. The second transports an
arbitrary pure context observer through the optional result with `Option.map`.
The third proves that optional write followed by canonical re-refinement
returns the same total carrier, using only the new coherence law and ADR-0105's
named present-refinement law. No example relies on broad simplification to
select either public law.

The runner imports both modules exactly once, calls the runtime test exactly
once, and adds no call for the compile-only module.

## Dependency boundary

`FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWrite.lean`
imports only `FrameCheckpointedWorkingPairWithPresentStorageAccount`.
`FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteProperties.lean`
imports only the new total-write definition and
`FrameCheckpointedWorkingPairWithStorageAddressProperties`.

The semantic umbrella places both modules together immediately after ADR-0106
total-read properties. The runtime test imports only the new definition; the
compile-only test imports the new properties and ADR-0105 refinement
properties. The runner places both after ADR-0106's tests and before
address-bound read/write coherence. Existing definitions and theorem statements
remain unchanged.

## What this slice does not decide

The total operation requires an already proven-present Account and never
creates one from absence. Its returned evidence applies only to its new
immutable working snapshot. It does not claim that the retained address is the
current contract or assign ownership, authorization, provenance, or lifetime.

This slice adds no new read law. Read-after-write, other-slot read preservation,
overwrite, commutation, and individual selector/checkpoint/journal projection
laws remain separate consumer slices. It adds no balance, nonce, code, value
transfer, call data, outcome, trace event, rollback, scheduling, transaction,
concurrency, reentrancy, atomicity, cost, or gas rule.

It adds no parser or source syntax, Core expression, Wire or Oracle field,
Profile, ABI, storage layout, serialization, or published observation.

## Staged implementation plan

Keep each of five commits below 300 changed lines: this decision and targeted
internal documentation; the exact total operation plus one umbrella import;
the exact coherence law plus one umbrella import; runtime and compile-only
regressions plus runner wiring; independent audit and completion evidence.

## Publication and consequences

This internal consumer changes no frozen or published boundary. A
proven-present working Account can be updated repeatedly without another
lookup, while its Account value, working-state entry, and presence evidence
remain synchronized.
