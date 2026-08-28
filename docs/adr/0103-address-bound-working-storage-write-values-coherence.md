# ADR-0103: Address-bound working storage-write values coherence

- Status: Accepted
- Decision date: 2026-08-29
- Scope: relate a retained-address write to its underlying values write
- Implementation: Planned

## Context

ADR-0093 wraps checkpointed working values with one retained storage selector
and maps successful writes back into that wrapper. ADR-0100 proves sequential
algebra for the underlying address-parameterized write, while ADR-0101 and
ADR-0102 expose selected algebra and structural observations at the wrapper
boundary.

Consumers still lack the direct relation between those two write APIs. To use
an existing or future generic values-level consumer, they must unfold the
wrapper operation and normalize nested `Option.map` expressions themselves.

## Decision

Add no executable operation, carrier, instance, or helper. Publish exactly one
values-projection coherence law:

```lean
namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

@[simp] theorem values_writeStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map (fun next => next.values) =
      context.values.writeWorkingStorage?
        context.storageAddress slot value

end Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress
```

The equality preserves the complete optional stage. An absent selected Account
produces `none` on both sides. A successful write produces the exact underlying
checkpointed working values on both sides; only the redundant retained-address
wrapper is forgotten by the left projection.

Register the law as a simp rule. It reduces a wrapper-specific write projection
to the existing generic operation. The absent and present branch rules reach
the same `none` or `some` normal form, and there is no reverse rule.

## Proof boundary

The proof performs only the two cases of the existing underlying optional write
result and unfolds the wrapper write. It adds no private theorem, direct
WorldState proof, Account lookup split, custom axiom, classical choice, or
unchecked declaration.

The public law must report exactly `[propext]`. Do not add a reverse wrapping
operation, success witness, inverse, equality of input carriers, or separate
failure theorem.

## Required compile regressions

Add exactly two private compile examples importing only the new properties
module:

1. the abstract values projection simplifies directly to the underlying
   optional write; and
2. applying an arbitrary pure values consumer to both optional results is
   justified through the named coherence law.

There is no public test function, runtime declaration, runtime assertion,
fixture, helper, or runner call. The runner imports the compile-only module
exactly once.

## Dependency boundary

`FrameCheckpointedWorkingPairWithStorageAddressStorageWriteCoherenceProperties.lean`
imports only `FrameCheckpointedWorkingPairWithStorageAddress`.

The semantic umbrella imports the new module after the ADR-0102 preservation
properties and before the initialization adapter. The compile regression
imports only the new module; the runner adds one import after the ADR-0102
compile regression and before the address-bound write-algebra regression, with
no call. Existing definitions and theorem statements remain unchanged.

## What this slice does not decide

The law forgets the retained selector only from an optional result observation.
It does not remove or change the selector in the input, construct a new wrapper,
or claim that two wrapper values with different selectors are equal.

Storage-address preservation remains owned by ADR-0102. Sequential overwrite
and commutation remain owned by ADR-0100 and ADR-0101; storage observations
remain owned by ADR-0097. Add no duplicate checkpoint, working-journal,
read-after-write, zero-deletion, initialization-specific, or Account-presence
law.

The retained address remains only a caller-supplied selector. This coherence
adds no current-contract identity, ownership, authorization, Account creation,
checkpoint capture or lifetime, rollback, outcome, trap, scheduling,
transaction, concurrency, reentrancy, atomicity, cost, gas, or external-effect
policy.

It adds no parser or source syntax, Core expression, Wire or Oracle field,
Profile, ABI, storage layout, serialization, or published observation.

## Staged implementation plan

Keep each of four commits below 300 changed lines: this decision and targeted
internal documentation; the exact law plus one umbrella import; the exact two
compile regressions plus one runner import and no call; independent audit and
completion evidence.

## Publication and consequences

This proof-only layer is internal and changes no frozen or published boundary.
Generic consumers of `writeWorkingStorage?` can be transported through the
retained-address writer without unfolding its wrapper construction.

Further contract-entry inputs still wait for concrete consumers and lifetime
rules.
