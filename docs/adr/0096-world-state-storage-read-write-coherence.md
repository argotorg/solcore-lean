# ADR-0096: WorldState storage read/write coherence

- Status: Accepted
- Decision date: 2026-08-29
- Scope: stage-preserving observable reads after conditional storage writes
- Implementation: Planned

## Context

ADR-0056 defines conditional `WorldState.writeStorage?`, ADR-0059 proves its
sequential update algebra, and ADR-0094 defines conditional
`WorldState.readStorage?`. Their observable composition is not yet available as
a named proof interface. Callers must unfold Account lookup, partial writes,
zero deletion, and unrelated update behavior to reason about a read after a
write.

This slice closes that proof boundary without adding an operation or changing
either failure rule.

## Decision

Add no public executable definition, carrier, helper, instance, or coercion.
Publish exactly three simp laws:

```lean
namespace Solcore.Semantics

@[simp] theorem WorldState.readStorage?_writeStorage?_same
    (state : WorldState) (address : Address)
    (slot value : Core.Word) :
    (state.writeStorage? address slot value).map
        (fun next => next.readStorage? address slot) =
      (state.account? address).map (fun _ => some value)

@[simp] theorem WorldState.readStorage?_writeStorage?_other_slot
    (state : WorldState) (address : Address)
    (writtenSlot value readSlot : Core.Word)
    (different : readSlot ≠ writtenSlot) :
    (state.writeStorage? address writtenSlot value).map
        (fun next => next.readStorage? address readSlot) =
      (state.account? address).map
        (fun _ => state.readStorage? address readSlot)

@[simp] theorem WorldState.readStorage?_writeStorage?_other_address
    (state : WorldState)
    (writtenAddress readAddress : Address)
    (writtenSlot value readSlot : Core.Word)
    (different : readAddress ≠ writtenAddress) :
    (state.writeStorage? writtenAddress writtenSlot value).map
        (fun next => next.readStorage? readAddress readSlot) =
      (state.account? writtenAddress).map
        (fun _ => state.readStorage? readAddress readSlot)

end Solcore.Semantics
```

All three laws deliberately use `Option.map` rather than `Option.bind`. Their
result is `Option (Option Core.Word)`: outer `none` means that the write target
Account was absent; `some none` means that the write succeeded but the selected
read Account was absent; `some (some value)` means both stages succeeded. The
proof interface must not collapse these distinct observations.

The same-slot law preserves conditional failure. A present Account yields
`some (some value)`, including a nested zero after zero deletion; an absent
Account yields outer `none`.

The different-slot law keeps the original read inside the successful write
branch. Because both stages use the same address, its nested read is always
present when the outer write succeeds.

The different-address law needs no presence hypothesis because the outer map
retains write failure. If the write target is present and the read target is
absent, both sides are `some none`; an absent write target remains outer
`none` even when the read target would be present.

All three rules remove a mapped write-then-read observation and have no reverse
form, so they are simplification rules. Same-slot and different-slot matching
is separated by the disequality hypothesis; different-address matching is
separated by address disequality. Every law must report exactly `[propext]`.

Add no flattened `Option.bind` duplicate, write-success theorem,
read-before-write theorem, carrier lift, batch operation, mutation-order claim,
or exactly-once evaluation claim.

## Required compile regressions

Add exactly three private compile examples importing only the new properties
module, one per public law. Each example uses the corresponding theorem through
the simp interface. There is no public test function, runtime assertion, or
runner call. The test runner imports the compile-only module exactly once.

Runtime behavior for Account and WorldState reads and writes is already covered
at the ADR-0056, ADR-0059, and ADR-0094 definition boundaries. This slice tests
the new proof interface rather than duplicating those fixtures.

## Dependency boundary

`WorldStateStorageReadWriteProperties.lean` imports exactly
`Solcore.Semantics.WorldStateStorageReadProperties` and
`Solcore.Semantics.WorldStateProperties`. It reuses the existing Account
read-after-write, WorldState account-update, conditional read, and conditional
write definitions and laws.

The semantic umbrella imports the new properties module after the existing
WorldState storage-write algebra. The compile-only regression imports only the
new module; the runner adds one import and no call. Existing definitions and
theorem statements remain unchanged.

## What this slice does not decide

These are equalities of pure nested `Option` values, not claims about concurrent
mutation, cost, order of external effects, or exactly-once execution. They add
no Account creation, deletion, authorization, current-contract identity,
checkpoint, rollback, outcome, trap, stack, scheduling, transaction, balance,
code, storage layout, warmth, refund, gas, ABI, serialization, EVM revision,
delta, or published observation rule.

The slice adds no parser or source syntax, Core expression, Wire or Oracle
field, Profile, capability, or frozen artifact.

## Staged implementation plan

Keep each of four commits below 300 changed lines: this decision and targeted
roadmap updates; the exact three laws plus one umbrella import; the exact three
compile regressions plus one runner import and no call; independent audit and
completion evidence.

## Publication and consequences

This proof-only layer is not published. Consumers can normalize the observable
result of a conditional write without unfolding private Account or WorldState
representation. A later present-Account refinement can reuse these laws while
providing total frame-local storage operations.
