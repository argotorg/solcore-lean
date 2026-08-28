# ADR-0112: Present working storage Account total-write presence

- Status: Accepted
- Decision date: 2026-08-29
- Scope: expose zero deletion and nonzero slot presence after a total write
- Implementation: Complete

## Context

ADR-0108 proves that a total read observes the value just written. A zero read,
however, does not distinguish an absent sparse-storage entry from a stored
representation. The Account semantics make that distinction explicit: writing
zero deletes the selected entry, while writing a nonzero word produces
`some value`.

ADR-0111 now exposes the exact stored Account returned by the refined carrier.
Consumers should be able to name the two representation observations without
unfolding the carrier or applying Account laws through definitional reduction.

## Decision

Publish exactly two named, non-simp laws:

```lean
namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

theorem storageValue?_writeStorage_zero
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot : Core.Word) :
    (context.writeStorage slot Core.Word.zero).storageAccount.storageValue?
        slot = none

theorem storageValue?_writeStorage_nonzero
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word)
    (nonzero : value ≠ Core.Word.zero) :
    (context.writeStorage slot value).storageAccount.storageValue? slot =
      some value

end Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
```

The zero law states deletion of the sparse entry, not deletion of the selected
Account. The nonzero law requires the same explicit inequality orientation as
the underlying Account theorem. Together they expose representation presence;
ADR-0108 remains the value-level read interface.

Keep both laws out of the simp registry. In the full registry, ADR-0111's
`storageAccount_writeStorage` simplifies the inner stored-Account projection
first. The remaining Account-level zero/nonzero presence laws are deliberately
non-simp, so registering only these outer wrappers would be ineffective and
misleading. This slice does not broaden the older Account simp policy.

Each proof first rewrites by ADR-0111 `storageAccount_writeStorage`, then applies
the corresponding `Account.storageValue?_storageWrite_zero` or
`Account.storageValue?_storageWrite_nonzero` law. Both public laws must report
exactly `[propext]`. Add no combined conditional theorem, reverse theorem,
other-slot law, helper, operation, carrier, coercion, or instance.

## Required regressions

Add one compile-only module with exactly two private examples. Each applies its
fully qualified refined-carrier law directly. The examples may not use `rfl`,
simplification, operation unfolding, the ADR-0111 projection, or the underlying
Account laws, because every such route could mask a missing public lift.

This proof-only slice adds no runtime module or assertion. ADR-0107 already
executes zero and nonzero total writes, including direct zero-entry deletion;
the minimal WorldState runtime suite separately checks both Account-level
`none` and `some value` representation branches. The new universally quantified
carrier laws add no executable behavior. The runner imports the compile-only
module exactly once after ADR-0111's regression and adds no call.

## Dependency boundary

`FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWritePresenceProperties.lean`
imports exactly ADR-0111's projection properties and `WorldStateProperties`.
The explicit layered proof does not import total reads, read-after-write,
total-write algebra, isolation, or optional-write modules.

The semantic umbrella imports the new module immediately after ADR-0111's
projection module. The compile regression imports only the new module; the
runner places it after ADR-0111's compile regression and before the older
address-bound optional read/write coherence regression. Existing definitions
and theorem statements remain unchanged.

## What this slice does not decide

These laws observe the retained Account, whose equality with the selected
working-state entry remains certified by `storageAccount_present`. They add no
duplicate context-lookup or `Option.bind` observation and do not change zero's
total-read default.

Other-slot representation preservation and optional/total multi-step coherence
remain separate decisions. This slice adds no Account creation, address role,
authority, authorization, provenance, lifetime, checkpoint, rollback, outcome,
trace event, scheduling, transaction, concurrency, reentrancy, atomicity, cost,
or gas rule.

It adds no parser or source syntax, Core expression, Wire or Oracle field,
Profile, ABI, storage layout, serialization, or published observation.

## Staged implementation plan

Keep each of four commits below 300 changed lines: this decision and targeted
internal documentation; the exact two laws plus one umbrella import; the exact
two compile regressions plus one runner import and no call; independent audit
and completion evidence.

## Implementation record

The completed proof-only slice adds a 38-line properties module plus one
semantic umbrella import. It publishes exactly the two required named non-simp
laws and adds no helper, operation, carrier, coercion, or instance. Both proofs
use ADR-0111's stored-Account projection explicitly, apply the corresponding
Account law, and report exactly `[propext]`.

The 34-line compile-only module plus one runner import contains exactly two
private examples. Each applies its fully qualified refined-carrier law directly,
so definitional reduction, the projection theorem, and lower Account laws
cannot mask a missing declaration. The test layer adds no runtime or public
declaration, fixture, helper, assertion, or runner call.

The implementation commits are `58038be` (166 changed lines), `bb1e05a` (39),
and `21c7f29` (35), all below 300 changed lines; this completion update is the
fourth staged commit. Focused trust-zero checks, the 570-job full build, the
1028-job full test run, metadata and kernel checks, diff checks, declaration,
axiom, dependency, and simp-registration inventories, projection-first and
proof-masking checks, and independent P0-P3 audit pass.

## Publication and consequences

This proof-only layer changes no frozen or published boundary. Refined storage
consumers can distinguish zero deletion from nonzero sparse-entry presence by
name while retaining the existing controlled simp policy.
