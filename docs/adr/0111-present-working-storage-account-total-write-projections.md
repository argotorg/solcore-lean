# ADR-0111: Present working storage Account total-write projections

- Status: Accepted
- Decision date: 2026-08-29
- Scope: expose the four meaningful data projections of a total write
- Implementation: Complete

## Context

ADR-0107 reconstructs a proven-present carrier after updating its selected
working Account. ADR-0108 through ADR-0110 fix read observations, sequential
write algebra, and non-selected Account isolation, but consumers still need to
unfold the operation to observe the returned carrier's individual data fields.

Three fields are invariant: the storage selector, checkpoint, and working
effect journal. The stored Account is not invariant, but its exact updated
value is the fourth meaningful data projection. The generated whole-definition
equation is a backward-definitional equation rather than a simp projection API.

## Decision

Publish exactly four simp laws:

```lean
namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

@[simp] theorem storageAddress_writeStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage slot value).context.storageAddress =
      context.context.storageAddress

@[simp] theorem checkpoint_writeStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage slot value).context.values.checkpoint =
      context.context.values.checkpoint

@[simp] theorem workingEffects_writeStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage slot value).context.values.working.2 =
      context.context.values.working.2

@[simp] theorem storageAccount_writeStorage
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage slot value).storageAccount =
      context.storageAccount.storageWrite slot value

end Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
```

The first three laws mirror the corresponding address-bound optional-write
observations without an `Option` stage. The fourth exposes the exact Account
update promised by ADR-0107 and gives future Account observers a stable bridge
without exposing the whole carrier constructor.

All four are simp rules. Each removes one refined-carrier write from the
observed projection. The Account projection retains only the lower-level
`Account.storageWrite`. Its overlap with ADR-0109 overwrite converges through
the existing Account overwrite law. The selector rule also discharges the
deferred side condition in ADR-0110, so arbitrary nested isolation observations
can now normalize automatically when both modules are in scope.

Each proof is `rfl` against the total-write definition, and each law must report
exactly `[propext]`. Add no helper, whole-result equation, working WorldState
projection, proof-field projection, selected-address lookup law, operation,
carrier, coercion, or instance.

## Required regressions

Add one compile-only module with exactly five private examples. The first four
apply the fully qualified projection laws directly, one law per example. They
must not use `rfl`, definition unfolding, or simplification, because all four
facts are definitionally recoverable and such proofs would mask a missing
public declaration.

The fifth imports ADR-0110 isolation and proves its arbitrary two-write form by
bare `simp [different]`. This is deliberately a simp-integration regression:
it fails before the selector projection is registered and passes once the new
rule can transport the inequality through the first write.

This proof-only slice adds no runtime module or assertion. ADR-0107's three
runtime assertions already check the selector, checkpoint, working journal,
updated stored Account, and synchronized working-state entry across nonzero,
zero, and sequential writes. The runner imports the compile-only module exactly
once after ADR-0110's regression and adds no call.

## Dependency boundary

`FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteProjectionProperties.lean`
imports only the ADR-0107 total-write definition. It does not import isolation,
read-after-write, algebra, optional-write, or WorldState proof modules.

The semantic umbrella imports the new module immediately after ADR-0110's
isolation module. The compile regression imports the new module and ADR-0110
isolation; the runner places it after ADR-0110's compile regression and before
the older address-bound optional read/write coherence regression. Existing
definitions and theorem statements remain unchanged.

## What this slice does not decide

The four laws expose only direct data projections. Selected working-state
synchronization remains certified by the returned `storageAccount_present`
proof. No duplicate proof projection or selected-address lookup theorem is
needed.

Storage-value presence after zero or nonzero writes remains the next separate
observational decision. This slice adds no whole-world equality, Account
creation, address role, authority, authorization, provenance, lifetime,
checkpoint capture, rollback, outcome, trace event, scheduling, transaction,
concurrency, reentrancy, atomicity, cost, or gas rule.

It adds no parser or source syntax, Core expression, Wire or Oracle field,
Profile, ABI, storage layout, serialization, or published observation.

## Staged implementation plan

Keep each of four commits below 300 changed lines: this decision and targeted
internal documentation; the exact four laws plus one umbrella import; the exact
five compile regressions plus one runner import and no call; independent audit
and completion evidence.

## Implementation record

The completed proof-only slice adds a 55-line properties module plus one
semantic umbrella import. It publishes exactly the four required simp laws and
adds no helper, operation, carrier, coercion, or instance. All four laws are
proved by reflexivity and report exactly `[propext]`; the generated
`writeStorage.eq_1` remains outside the simp registry.

The 71-line compile-only module plus one runner import contains exactly five
private examples. Four apply the fully qualified public laws directly. The
fifth proves arbitrary two-write ADR-0110 isolation with simp and fails when the
new selector rule is absent, so it audits the intended registry integration.
The test layer adds no runtime or public declaration, fixture, helper,
assertion, or runner call.

The implementation commits are `916891a` (188 changed lines), `88f4df4` (56),
and `8151a3b` (72), all below 300 changed lines; this completion update is the
fourth staged commit. Focused trust-zero checks, the 568-job full build, the
1024-job full test run, metadata and kernel checks, diff checks, declaration,
axiom, dependency, equation-attribute, and simp-registration inventories,
critical-pair and proof-masking checks, and independent P0-P3 audit pass.

## Publication and consequences

This proof-only layer changes no frozen or published boundary. Consumers can
observe every meaningful returned data field without unfolding the evidence
carrier, and nested non-selected Account isolation becomes simp-compositional.
