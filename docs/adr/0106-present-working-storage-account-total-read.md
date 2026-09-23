# ADR-0106: Present working storage Account total read

- Status: Accepted
- Decision date: 2026-08-29
- Scope: expose a total slot read from a proven-present working Account
- Implementation: Complete

## Context

ADR-0095 reads through an address-bound working context with result type
`Option Core.Word`, preserving the possibility that the selected Account is
absent. ADR-0105 now provides a refined carrier containing the exact selected
working Account and evidence that its lookup succeeded.

Consumers of that carrier no longer need another WorldState lookup or an
unreachable absence branch. The first consumer should be a total read that
uses only the stored Account while remaining coherent with the existing
conditional context read.

## Decision

Add exactly one total operation:

```lean
namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

def readStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot : Core.Word) : Core.Word :=
  context.storageAccount.storageRead slot

end Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
```

The operation is total because Account-level reads already return zero for a
missing slot. It reads the Account stored by the refinement, performs no
WorldState lookup, and does not inspect the checkpoint, address, journals, or
presence proof at runtime.

## Required proof interface

Publish exactly one simp coherence law:

```lean
namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

@[simp] theorem context_readStorage?_eq_some_readStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot : Core.Word) :
    context.context.readStorage? slot = some (context.readStorage slot)

end Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
```

The proof applies the existing address-bound present-read law with
`context.storageAccount_present`. It normalizes the conditional read to the
total read in one direction and introduces no reverse rule or simp loop.

The operation, its generated equation, and the public law must report exactly
`[propext]`. Add no optional read on the refined carrier, direct unfolding law,
second coherence law, address or default argument, lookup helper, coercion,
instance, or Account reconstruction.

## Required regressions

Add one definition-only runtime module with exactly three assertions:

1. a present empty selected Account reads `Core.Word.zero` from a missing slot;
2. selector A over a two-Account working state reads A's exact values from two
   distinct slots; and
3. selector B over the same state reads B's exact values from both slots,
   without cross-address or cross-slot confusion.

Each assertion obtains the refined carrier through
`withPresentStorageAccount?` and invokes the new `readStorage`; none reads
`storageAccount` directly. ADR-0105 remains responsible for refinement failure.

The runtime module imports only the new definition, exposes one public test
function, and does not import the coherence law.

Add one compile-only module with exactly two private examples. The first names
the coherence law directly. The second rewrites a conditional read consumed by
`Option.getD` to the total result for an arbitrary fallback. Both examples use
the named law, so unrelated simp rules cannot mask its absence.

The runner imports both modules exactly once, calls the runtime test exactly
once, and adds no call for the compile-only module.

## Dependency boundary

`FrameCheckpointedWorkingPairWithPresentStorageAccountStorageRead.lean`
imports only `FrameCheckpointedWorkingPairWithPresentStorageAccount`.
`FrameCheckpointedWorkingPairWithPresentStorageAccountStorageReadProperties.lean`
imports only the new total-read definition and
`FrameCheckpointedWorkingPairWithStorageAddressStorageReadProperties`.

The semantic umbrella places both modules together immediately after the
address-bound conditional-read properties that the coherence proof consumes.
The runner places both tests after the address-bound conditional-read runtime
test and before address-bound read/write coherence. Existing definitions and
theorem statements remain unchanged.

## What this slice does not decide

The total result is valid for the immutable working snapshot stored in the
carrier. A transformed working context needs a newly constructed carrier and
matching evidence. This operation does not claim that the retained address is
the current contract or assign ownership, authorization, provenance, or
lifetime to it.

This slice adds no storage write; a total write is the immediate next consumer.
It adds no Account creation, balance, nonce, code, value transfer, call data,
outcome, trace event, rollback, scheduling, transaction, concurrency,
reentrancy, atomicity, cost, or gas rule.

It adds no parser or source syntax, Core expression, Wire field,
Profile, ABI, storage layout, serialization, or published observation.

## Staged implementation plan

Keep each of five commits below 300 changed lines: this decision and targeted
internal documentation; the exact total operation plus one umbrella import;
the exact coherence law plus one umbrella import; runtime and compile-only
regressions plus runner wiring; independent audit and completion evidence.

## Implementation record

The completed slice adds a 20-line definition module and a 24-line properties
module, with one semantic umbrella import for each. It publishes exactly the
required total operation and one simp coherence law. The operation, generated
equation, and law report exactly `[propext]`; only the law is registered with
the intended simp orientation.

The 70-line runtime module contains exactly three assertions, all of which
reach `readStorage` through a successful refinement. The 34-line compile-only
module contains exactly two private examples and names the coherence law in
both. The runner imports both modules once, calls the sole public runtime test
once, and adds no compile-only call.

The implementation commits are `6b319ab` (187 changed lines), `f1e0dc1` (21),
`af37c2d` (25), and `8c391b8` (107), all below 300 changed lines; this completion
update is the fifth staged commit. Focused trust-zero checks, the 554-job full
build, the 1000-job full test run, metadata and kernel checks, diff checks,
declaration and simp-registration inventories, exact dependency audits, and
independent P0-P3 audits pass.

## Publication and consequences

This internal consumer changes no frozen or published boundary. Proven-present
working storage can be read without rechecking Account absence, while the
coherence law keeps existing conditional consumers aligned.
