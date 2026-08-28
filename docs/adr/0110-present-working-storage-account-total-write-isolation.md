# ADR-0110: Present working storage Account total-write isolation

- Status: Accepted
- Decision date: 2026-08-29
- Scope: preserve every non-selected working Account across a total write
- Implementation: Complete

## Context

ADR-0107 updates one proven-present selected working Account and reconstructs
its evidence carrier. ADR-0108 and ADR-0109 fix the storage observations and
sequential algebra at that selected Account. Consumers still lack a direct
carrier-level theorem that the reconstructed working WorldState leaves every
other address alone.

The operation already delegates its WorldState update to `putAccount`; this
slice should expose exactly the corresponding non-interference boundary without
adding another mutation path or unfolding the carrier at each use site.

## Decision

Publish exactly one law:

```lean
namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

@[simp] theorem workingAccount?_writeStorage_other
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word)
    (otherAddress : Address)
    (different : otherAddress ≠ context.context.storageAddress) :
    (context.writeStorage slot value).context.values.working.1.account?
        otherAddress =
      context.context.values.working.1.account? otherAddress

end Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccount
```

The theorem preserves the full optional Account observation, so it covers both
presence and absence at every non-selected address. Its inequality orientation
matches `WorldState.account?_putAccount_other` and requires no decidable address
ordering.

Register the law as simp: for one exposed write, its left side contains that
write and its right side contains none. Generic nested writes are composed by
applying the named law at each stage; automatic nested normalization is not
claimed before a separate selector-projection simp law exists. When ADR-0109's
overwrite law is in scope, a same-slot nested write can first collapse to one
write and then use this isolation rule.

The proof applies `WorldState.account?_putAccount_other` directly to the
carrier's working WorldState and selected address. It must report exactly
`[propext]`. Add no selected-address theorem, Account equality theorem,
membership predicate, absent/present specialization, reverse law, helper,
operation, carrier, coercion, or instance.

## Required regressions

Add one compile-only module with exactly two private examples. The first applies
the fully qualified isolation law directly for one arbitrary write. The second
uses the named law twice to show that two arbitrary total writes preserve the
same non-selected Account observation. Neither example may unfold the operation
or invoke broad simplification, so the underlying WorldState theorem cannot
mask a missing carrier law.

This proof-only slice adds no runtime module or assertion. ADR-0107's three
runtime assertions already obtain the carrier canonically, invoke total writes,
and check the retained unrelated Account in every successful branch. The runner
imports the compile-only module exactly once after ADR-0109's regression and
adds no call.

## Dependency boundary

`FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteIsolationProperties.lean`
imports exactly the ADR-0107 total-write definition and `WorldStateProperties`.
It does not import total reads, read-after-write laws, total-write algebra,
optional-write algebra, or total-write coherence.

The semantic umbrella imports the new module immediately after ADR-0109's
total-write algebra module. The compile regression imports only the new module;
the runner places it after ADR-0109's compile regression and before the older
address-bound optional read/write coherence regression. Existing definitions
and theorem statements remain unchanged.

## What this slice does not decide

The theorem observes only the working WorldState at an address explicitly
known to differ from the retained storage selector. It does not identify that
selector with a current contract, caller, callee, owner, or code address, and
adds no authority, authorization, provenance, or lifetime rule.

Selected-Account synchronization is already carried by the returned evidence.
Individual selector, checkpoint, journal, and stored-Account projection laws,
storage-value presence after zero or nonzero writes, and optional/total
multi-step coherence remain separate consumer decisions.

This slice adds no balance, nonce, code, value transfer, call data, outcome,
trace event, rollback, scheduling, transaction, concurrency, reentrancy,
atomicity, cost, gas, parser or source syntax, Core expression, Wire or Oracle
field, Profile, ABI, storage layout, serialization, or published observation.

## Staged implementation plan

Keep each of four commits below 300 changed lines: this decision and targeted
internal documentation; the exact one law plus one umbrella import; the exact
two compile regressions plus one runner import and no call; independent audit
and completion evidence.

## Implementation record

The completed proof-only slice adds a 28-line properties module plus one
semantic umbrella import. It publishes exactly the one required simp law and
adds no helper, operation, carrier, coercion, or instance. The law applies the
existing WorldState non-interference theorem directly and reports exactly
`[propext]`.

The 42-line compile-only module plus one runner import contains exactly two
private examples. The first applies the fully qualified law directly; the
second applies it by name at each of two sequential writes. The test layer adds
no runtime or public declaration, fixture, helper, assertion, or runner call.

The implementation commits are `633a4a7` (161 changed lines), `b49a68d` (29),
and `867bb51` (43), all below 300 changed lines; this completion update is the
fourth staged commit. Focused trust-zero checks, the 566-job full build, the
1020-job full test run, metadata and kernel checks, diff checks, declaration,
axiom, dependency, and simp-registration inventories, named two-write
composition and proof-masking checks, and independent P0-P3 audit pass.

## Publication and consequences

This proof-only layer changes no frozen or published boundary. Consumers can
reason locally about the selected Account while retaining an exact guarantee
that total storage writes do not affect any other working Account.
