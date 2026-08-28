# ADR-0099: Storage-address adapter for parent-indexed frame initialization

- Status: Accepted
- Decision date: 2026-08-29
- Scope: bind one storage selector to initialized checkpointed working values
- Implementation: Complete

## Context

ADR-0098 produces a canonical `FrameCheckpointedWorkingPair` from one
parent-indexed initialization value. ADR-0093 already defines the carrier that
stores one caller-supplied storage address beside such values, and ADR-0093,
ADR-0095, and ADR-0097 provide its write, read, and read-after-write consumers.

The two boundaries currently meet only through direct constructor syntax. A
small adapter can fix their canonical wiring without inventing another carrier
or assigning the address a broader runtime role.

Other possible entry inputs are not ready for this layer. Caller, callee, code,
call data, transferred value, and call kind have no corresponding consumers or
lifetime rules in the current semantic model.

## Decision

Add exactly one operation:

```lean
namespace Solcore.Semantics.ParentIndexedFrameInitialization

universe u v

def toCheckpointedWorkingPairWithStorageAddress
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address) :
    FrameCheckpointedWorkingPairWithStorageAddress
      RollbackState (FrameTrace Event) :=
  ⟨storageAddress, initialization.toCheckpointedWorkingPair⟩

end Solcore.Semantics.ParentIndexedFrameInitialization
```

The initialization comes first so the operation supports dot notation. The
result is the existing ADR-0093 carrier, not a new address-bearing entry or
initialization type. Its address is exactly the caller input, and its values are
exactly the ADR-0098 result.

The operation is canonical wiring only. The address remains a stored selector;
it is not a current contract, callee, code address, caller, owner, or authorized
principal. The operation does not check that the address is present in either
WorldState.

Add no new carrier, custom constructor, second operation, address role, address
equality, Account-presence proof, validity or authority predicate, coercion,
instance, or default.

## Required proof interface

Publish exactly two simp projection laws:

```lean
namespace Solcore.Semantics.ParentIndexedFrameInitialization

universe u v

@[simp] theorem
    storageAddress_toCheckpointedWorkingPairWithStorageAddress
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address) :
    (initialization.toCheckpointedWorkingPairWithStorageAddress
      storageAddress).storageAddress = storageAddress

@[simp] theorem values_toCheckpointedWorkingPairWithStorageAddress
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address) :
    (initialization.toCheckpointedWorkingPairWithStorageAddress
      storageAddress).values = initialization.toCheckpointedWorkingPair

end Solcore.Semantics.ParentIndexedFrameInitialization
```

Both laws expose only the two fields observed by existing consumers. They
reduce projections and have no reverse form, so they are simplification rules.
The operation, generated equation, and both laws must report exactly
`[propext]`.

Do not add a whole-record simp law. The operation's generated equation already
exposes the direct constructor form, while ADR-0098 separately owns the
canonical contents of `toCheckpointedWorkingPair`. Repeating that full nested
normal form here would couple two proof layers and broaden simplification
without adding an observation.

Add no read, write, or read-after-write duplicate. ADR-0093, ADR-0095, and
ADR-0097 apply directly to the returned carrier.

## Required compile regressions

Add exactly three private compile examples importing only the new properties
module:

1. the result projects the exact supplied storage address through simp;
2. the result projects the exact ADR-0098 checkpointed working pair through
   simp; and
3. the result is accepted by the existing address-bound `writeStorage?`
   consumer, with its defining working-write expression checked at compile
   time.

The third example may unfold the existing write operation, but it must use the
new projection simp interface for the adapter. There is no public test function,
runtime declaration, runtime assertion, or runner call. The runner imports the
compile-only module exactly once.

## Dependency boundary

`ParentIndexedFrameInitializationStorageAddress.lean` imports exactly
`ParentIndexedFrameInitialization` and
`FrameCheckpointedWorkingPairWithStorageAddress`.
`ParentIndexedFrameInitializationStorageAddressProperties.lean` imports only
the new definition module because both projection proofs are definitional.

The semantic umbrella imports both modules after the existing address-bound
carrier modules and before their storage-read lift. The compile regression
imports only the new properties module; the runner adds one import and no call.
Existing definitions and theorem statements remain unchanged.

## What this slice does not decide

The adapter does not prove that construction occurred during frame entry, that
an invocation exists, or that the supplied address belongs to any runtime
identity. It performs no Account lookup, Account creation, storage read, storage
write, mutation, authorization, value transfer, or code selection.

It adds no caller, callee, code, or origin address; call data, transferred
value, call kind, balance, nonce, code lookup, outcome provenance, return
delivery, trap handling, event, stack, depth, scheduling, recursion,
reentrancy, gas, ABI, transaction, host I/O, or published observation.

It adds no parser or source syntax, Core expression, Wire or Oracle field,
Profile, or frozen artifact. It makes no concurrency, cost, evaluation-count,
or external-effect claim.

## Staged implementation plan

Keep each of five commits below 300 changed lines: this decision and targeted
documentation updates; the exact operation plus one umbrella import; the exact
two projection laws plus one umbrella import; the exact three compile
regressions plus one runner import and no call; independent audit and completion
evidence.

## Implementation record

The completed slice adds a 24-line definition module plus one semantic
umbrella import. It contains exactly the required adapter operation and no new
carrier. The operation and its generated equation report exactly `[propext]`.

A 34-line properties module plus one umbrella import publishes exactly the two
required simp projection laws. Both report exactly `[propext]`; the one-way
field reductions introduce no simplification loop or whole-record overlap.

A 50-line compile-only test module plus one runner import contains exactly
three private examples for the address projection, values projection, and the
existing address-bound storage-write consumer. It adds no public or runtime
declaration, assertion, helper, or runner call.

The implementation commits are `6164149` (217 changed lines), `60d5b97` (25),
`f586ff2` (35), and `8d43460` (51), all below 300 changed lines; this completion
update is the fifth staged commit. Focused trust-zero checks, the 538-job full
build, the 964-job full test run, metadata and kernel checks, diff checks,
simplification review, declaration inventory, and independent P0-P3 audits
pass.

## Publication and consequences

This internal adapter is not published. It gives the only input role with
established consumers a direct path from ADR-0098 initialization to the
existing address-bound storage API.

Further contract-entry inputs remain separate. Each should be added only when
its consumer and lifetime rule are available; they must not be hidden in an
unconstrained payload or conflated with this storage selector.
