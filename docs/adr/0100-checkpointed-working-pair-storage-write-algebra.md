# ADR-0100: Checkpointed working-pair storage-write algebra

- Status: Accepted
- Decision date: 2026-08-29
- Scope: lift sequential storage-write algebra to checkpointed working values
- Implementation: Complete

## Context

ADR-0059 proves overwrite and independent-write commutation for the strict
`WorldState.writeStorage?` operation. ADR-0092 lifts that operation to the
working WorldState of a `FrameCheckpointedWorkingPair`, preserving the exact
checkpoint and working effect journal.

The lifted operation has absent- and present-Account branch laws, but no named
sequential algebra. Callers must currently unfold its `Option.map` wrapper to
reuse the underlying WorldState results. This proof-only slice closes that gap
at the layer that owns the address-parameterized working write.

ADR-0093's retained-address carrier delegates to the ADR-0092 operation, and
ADR-0099 constructs that carrier from initialized values. Consumer-facing
specializations may therefore reuse this generic layer later without proving
the underlying normalization again.

## Decision

Add no executable operation, carrier, instance, or public helper. Add exactly
one private proof helper that rewrites a bind of two lifted writes into the
corresponding bind of two WorldState writes, mapped back into the original
checkpoint and working journal.

Publish exactly three laws:

```lean
namespace Solcore.Semantics.FrameCheckpointedWorkingPair

universe u v

@[simp] theorem writeWorkingStorage?_overwrite
    {RollbackState : Type u} {TraceState : Type v}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (address : Address) (slot first second : Core.Word) :
    (values.writeWorkingStorage? address slot first).bind
        (fun next => next.writeWorkingStorage? address slot second) =
      values.writeWorkingStorage? address slot second

theorem writeWorkingStorage?_commute_slots
    {RollbackState : Type u} {TraceState : Type v}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (address : Address)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftSlot ≠ rightSlot) :
    (values.writeWorkingStorage? address leftSlot leftValue).bind
        (fun next =>
          next.writeWorkingStorage? address rightSlot rightValue) =
      (values.writeWorkingStorage? address rightSlot rightValue).bind
        (fun next =>
          next.writeWorkingStorage? address leftSlot leftValue)

theorem writeWorkingStorage?_commute_addresses
    {RollbackState : Type u} {TraceState : Type v}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (leftAddress rightAddress : Address)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftAddress ≠ rightAddress) :
    (values.writeWorkingStorage? leftAddress leftSlot leftValue).bind
        (fun next =>
          next.writeWorkingStorage? rightAddress rightSlot rightValue) =
      (values.writeWorkingStorage? rightAddress rightSlot rightValue).bind
        (fun next =>
          next.writeWorkingStorage? leftAddress leftSlot leftValue)

end Solcore.Semantics.FrameCheckpointedWorkingPair
```

Only overwrite is a simp rule: two writes to the same address and slot reduce
to the final write. Both commutation laws remain non-simp because exchanging
symmetric orders provides no canonical simplification direction and would
permit a rewrite loop.

These are equalities between pure `Option.bind` expressions. Their final
`none` means only that at least one required Account was absent; the bind does
not retain which stage failed or whether the first write produced an
intermediate value. Successful results are rebuilt with the original
checkpoint and whole working journal. The laws do not assert that both writes
succeed or that either write occurred as a runtime action.

## Proof boundary

The private helper uses only the ADR-0092 definition and the standard
`Option.bind_map` and `Option.map_bind` equalities. Each public law then reuses
the matching ADR-0059 WorldState theorem instead of repeating Account-presence
case analysis.

All three public laws must report exactly `[propext, Quot.sound]`. Add no
classical choice, custom axiom, unchecked declaration, second private helper,
or public normalization theorem.

Do not lift the zero-deletion existential in this slice. ADR-0092's present
branch already exposes the exact `Account.storageWrite` result, while
ADR-0096 and ADR-0097 expose the relevant read observation. This slice is only
the three-law sequential algebra.

## Required compile regressions

Add exactly three private compile examples importing only the new properties
module:

1. same-address, same-slot overwrite through simp;
2. same-address, distinct-slot commutation by the named non-simp law; and
3. distinct-address commutation by the named non-simp law.

There is no public test function, runtime declaration, runtime assertion,
fixture, helper, or runner call. The runner imports the compile-only module
exactly once.

## Dependency boundary

`FrameCheckpointedWorkingPairStorageWriteAlgebraProperties.lean` imports
exactly `FrameCheckpointedWorkingPairStorageWrite` and
`WorldStateStorageWriteAlgebraProperties`. It does not import the existing
checkpointed branch-properties module because the proofs do not use it.

The semantic umbrella imports the new module immediately after
`WorldStateStorageWriteAlgebraProperties` and before the WorldState
read-after-write properties. The compile regression imports only the new
module; the runner adds one import and no call. Existing definitions and
theorem statements remain unchanged.

## What this slice does not decide

The laws do not identify either address with a current contract, caller,
callee, code address, owner, or authorized principal. They add no address role,
Account creation, balance or code update, checkpoint capture or lifetime,
rollback, outcome, trap, scheduling, transaction, concurrency, reentrancy,
atomicity, or external-effect policy.

Commutation here does not claim that runtime actions may be reordered, execute
exactly once, have equal costs, or produce the same external observations. It
only equates the existing immutable storage-write expressions and their
existing failure behavior.

The slice adds no retained-address duplicate, read-after-write law,
zero-deletion witness, parser or source syntax, Core expression, Wire or Oracle
field, Profile, ABI, storage layout, gas rule, or published observation.

## Staged implementation plan

Keep each of four commits below 300 changed lines: this decision and targeted
internal documentation; the exact private helper and three laws plus one
umbrella import; the exact three compile regressions plus one runner import and
no call; independent audit and completion evidence.

## Implementation record

The completed slice adds a 77-line properties module plus one semantic
umbrella import. One private normalization helper supports exactly the three
required public laws; no executable operation, carrier, instance, or public
helper is added.

Only `writeWorkingStorage?_overwrite` is a simp rule. The two commutation laws
remain non-simp. All three public laws report exactly
`[propext, Quot.sound]`, and simplification review finds no loop or divergent
critical overlap with the existing branch laws.

A 52-line compile-only test module plus one runner import contains exactly
three private examples. Overwrite uses the public simp rule; both commutation
examples name their public non-simp law directly. The test layer adds no
runtime or public declaration, fixture, helper, assertion, or runner call.

The implementation commits are `7814798` (214 changed lines), `afbd0ec` (78),
and `a98a71e` (53), all below 300 changed lines; this completion update is the
fourth staged commit. Focused trust-zero checks, the 540-job full build, the
968-job full test run, metadata and kernel checks, diff checks, declaration
inventory, failure-stage review, and independent P0-P3 audits pass.

## Publication and consequences

This proof-only layer is internal and changes no frozen or published boundary.
It lets callers reason about repeated ADR-0092 writes while retaining the
checkpoint and working journal implicitly through the existing carrier.

An address-bound specialization remains a separate consumer-facing decision.
Further contract-entry inputs still wait for concrete consumers and lifetime
rules.
