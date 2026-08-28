# ADR-0114: Present working storage Account optional/total re-refinement coherence

- Status: Accepted
- Decision date: 2026-08-29
- Scope: equate optional write plus canonical refinement with the total writer
- Implementation: Planned

## Context

The address-bound writer from ADR-0093 returns an optional context because its
selected working Account may be absent. ADR-0105 refines exactly the present
case, and ADR-0107 gives that refinement a total writer. ADR-0107 also proves
that the optional writer returns the context projection of the total result.

That context-only equality does not by itself expose the final proof-carrying
carrier. A consumer can bind the optional result into canonical Account
refinement, but currently must repeat the proof that this reconstruction is the
same total result. ADR-0107's compile tests establish the fact privately; it
should now be a stable semantic boundary that can be composed repeatedly.

## Decision

Publish exactly one named, non-simp law:

```lean
namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

theorem
    context_writeStorage?_bind_withPresentStorageAccount?_eq_some_writeStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.context.writeStorage? slot value).bind
        FrameCheckpointedWorkingPairWithStorageAddress.withPresentStorageAccount? =
      some (context.writeStorage slot value)

end Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
```

The left side follows the failure-aware, address-bound API, then rebuilds the
present-Account evidence carrier. The right side uses the total operation
available from the same initial evidence. Equality covers the complete carrier:
selector, checkpoint, working state and journal, stored Account, and its
snapshot-specific presence proof.

The law remains outside the simp registry. It overlaps with ADR-0107's existing
inner optional-write simplification. Applying the whole composite law produces
`some` of the total result, while taking the inner rule first and reducing
`Option.bind` leaves direct re-refinement of the returned context, which the
current registry does not close. Registering only the composite law would
therefore leave two unjoined rewrite paths. Named application supplies the
useful whole-boundary rewrite without adding a redundant direct specialization
merely to repair that overlap.

Prove it by rewriting with
`context_writeStorage?_eq_some_writeStorage_context`, reducing only
`Option.bind_some`, and applying ADR-0105
`withPresentStorageAccount?_of_present` to the total result's exact stored
Account and evidence. The theorem must report exactly `[propext]`.

Do not publish a separate direct re-refinement specialization. It is merely the
intermediate fact already constructible from ADR-0105's present branch and does
not express the optional/total boundary. Add no generic round-trip law,
fixed-two-write theorem, list or batch writer, helper, operation, carrier,
coercion, or instance. Finite sequences in which each optional write is
immediately re-refined compose by applying this one law at every `Option.bind`
stage.

## Required regressions

Add one compile-only module with exactly two private examples. The first applies
the fully qualified public theorem directly. It may not use `rfl`,
simplification, unfolding, ADR-0107 context coherence, or ADR-0105 refinement,
because each alternate route could mask a missing public declaration.

The second constructs two consecutive optional-write-plus-refinement stages and
equates them with two consecutive total writes. It rewrites with the new law at
the first stage and applies the same law directly at the second stage. It uses
no simplification, reflexivity, unfolding, or lower law. This confirms reusable
composition without adding a fixed-depth public theorem.

This proof-only slice adds no runtime module, public runtime declaration,
assertion, fixture, or runner call. ADR-0093 already executes the optional
writer's absence and success branches. ADR-0107 executes total nonzero, zero,
and sequential writes while checking the synchronized carrier. The new theorem
equates those existing paths and adds no executable behavior.

## Dependency boundary

Create
`FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteRefinementCoherenceProperties.lean`,
importing exactly ADR-0107's storage-write properties and ADR-0105's refinement
properties. It does not need read, algebra, isolation, projection, presence,
sparse-preservation, or lower WorldState proof modules.

The semantic umbrella imports the new module immediately after ADR-0113's
refined sparse-preservation module. The compile regression imports only the new
module. The runner places it immediately after ADR-0113's regression and before
the older address-bound optional read/write regression, with no call.

## What this slice does not decide

The theorem begins with a proven-present Account. It does not make an absent
Account writable, create one, or convert a genuine optional failure into a
total result. It equates values, not evaluation cost, lookup count, or an
operational trace.

This slice adds no Account role, caller, callee, code address, authority,
authorization, provenance, lifetime, checkpoint capture, rollback, outcome,
trace event, scheduling, transaction, concurrency, reentrancy, atomicity, cost,
or gas rule.

It adds no parser or source syntax, Core expression, Wire or Oracle field,
Profile, ABI, storage layout, serialization, or published observation.

## Staged implementation plan

Keep each of four commits below 300 changed lines: this decision and targeted
internal documentation; the exact one law plus one semantic umbrella import;
the exact two compile regressions plus one runner import and no call;
independent audit and completion evidence.

## Publication and consequences

This proof-only layer changes no frozen or published boundary. When complete,
consumers can move from the failure-aware address-bound writer back to the
canonical proven-present total carrier by one named equality and can reuse that
equality at every subsequent optional-write/refinement stage.
