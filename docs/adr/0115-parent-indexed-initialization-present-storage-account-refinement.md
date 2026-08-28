# ADR-0115: Parent-indexed initialization present storage Account refinement

- Status: Accepted
- Decision date: 2026-08-29
- Scope: refine an initialization-bound storage selector in caller-supplied state
- Implementation: Complete

## Context

ADR-0098 constructs canonical checkpointed working values from a parent-indexed
initialization. ADR-0099 binds a caller-supplied storage selector to those
values. ADR-0105 can then inspect the selected working Account and, when it is
present, return the existing proof-carrying carrier used by total storage reads
and writes.

Those public operations already compose directly; this slice does not repair a
missing construction or claim current downstream duplication. Its purpose is
to fix an input-facing branch boundary stated in terms of
`initialization.initialWorld` and to establish the first checked compile-time
connection from parent-indexed initialization to a total storage consumer. The
small partial adapter preserves Account absence exactly and adds no new
Account-presence rule.

ADR-0099 is precedent only for retaining the existing selector and carrier
semantics across this wiring. It is not evidence for a new presence semantics;
the input-facing `initialWorld` branch laws and the concrete ADR-0106/0107
consumers are the additional boundary fixed here.

## Decision

Add exactly one partial operation:

```lean
namespace Solcore.Semantics.ParentIndexedFrameInitialization

universe u v

def toCheckpointedWorkingPairWithPresentStorageAccount?
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address) :
    Option
      (FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState (FrameTrace Event)) :=
  (initialization.toCheckpointedWorkingPairWithStorageAddress
    storageAddress).withPresentStorageAccount?

end Solcore.Semantics.ParentIndexedFrameInitialization
```

The operation uses ADR-0099's caller-supplied selector and checks it against
`initialization.initialWorld`, which is definitionally the derived carrier's
working WorldState. An absent Account returns `none`. On success, the returned
ADR-0105 carrier retains the selector and can immediately use ADR-0106/0107
total storage operations.

This is canonical composition, not a second presence semantics. Add no
proof-taking total adapter: that would merely ask the caller to repeat the
Account and proof already discovered by the partial refinement. Add no witness
carrier retaining initialization, address, Account, and proof; no consumer
needs that duplicated bundle.

The operation and its generated equation must report exactly `[propext]`. Add
no helper, custom constructor, coercion, instance, default, Account creation,
or alternate failure representation.

## Required proof interface

Publish exactly two simp branch laws:

```lean
@[simp] theorem
    toCheckpointedWorkingPairWithPresentStorageAccount?_of_absent
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address)
    (absent :
      initialization.initialWorld.account? storageAddress = none) :
    initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress = none

@[simp] theorem
    toCheckpointedWorkingPairWithPresentStorageAccount?_of_present
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress : Address)
    (account : Account)
    (present :
      initialization.initialWorld.account? storageAddress = some account) :
    initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
        storageAddress =
      some
        ⟨initialization.toCheckpointedWorkingPairWithStorageAddress
            storageAddress,
          account,
          present⟩
```

Both laws delegate to ADR-0105's corresponding refinement branch. Their
premises observe the caller-supplied initial WorldState directly; definitional
reduction transports them to the derived working snapshot. Both laws reduce
one new operation and must report exactly `[propext]`.

The rules are simp laws because their explicit mutually exclusive premises
select a branch and their right sides contain no occurrence of the new
operation. Their overlap with unfolding followed by ADR-0105 reaches the same
result. Add no additional unconditional coherence theorem, reverse rule,
projection duplicate, or total-result law.

## Required regressions

Add one compile-only module with exactly three private examples. The first two
apply the fully qualified absent and present laws directly. They may not use
`rfl`, simplification, operation unfolding, or ADR-0105 lower laws, because each
alternate route could mask a missing public branch declaration.

The third assumes Account presence, maps the adapter result through a total
write followed by a same-slot total read, and proves `some value`. It rewrites
with the new present law and applies ADR-0108's existing
`readStorage_writeStorage_same` result. This is the first end-to-end compile
boundary from parent-indexed initialization to a total storage consumer.

Add no runtime module, public runtime declaration, assertion, fixture, or runner
call. ADR-0098/0099 already cover initialization wiring, ADR-0105 executes both
presence branches, and ADR-0106/0107 execute total storage behavior. The new
operation only composes those paths.

## Dependency boundary

`ParentIndexedFrameInitializationPresentStorageAccount.lean` imports exactly
ADR-0099's storage-address adapter and the ADR-0105 carrier definition.
`ParentIndexedFrameInitializationPresentStorageAccountProperties.lean` imports
exactly the new definition and ADR-0105 refinement properties.

The semantic umbrella places both modules immediately after ADR-0099's
storage-address properties and before storage-read consumers. The compile
regression imports exactly the new properties module and ADR-0108 read/write
properties. The runner places it immediately after ADR-0099's compile
regression and adds no call.

## What this slice does not decide

`initialization`, `initialWorld`, and `storageAddress` remain caller-supplied.
The operation does not prove that a frame entry occurred or that the selector
is a callee, current contract, code address, owner, or authorized principal. Its
successful evidence is tied only to the derived initial working snapshot;
later total writes construct fresh evidence for their own immutable snapshots.

The adapter does not create an absent Account or choose a creation, trap, or
diagnostic policy. It adds no caller, callee, code, call data, transferred value,
call kind, balance, nonce, outcome provenance, checkpoint capture, rollback,
trace event, scheduling, transaction, concurrency, reentrancy, atomicity, cost,
or gas rule.

It adds no parser or source syntax, Core expression, Wire or Oracle field,
Profile, ABI, storage layout, serialization, or published observation.

## Staged implementation plan

Keep each of five commits below 300 changed lines: this decision and targeted
internal documentation; the exact one operation plus one semantic umbrella
import; the exact two branch laws plus one semantic umbrella import; the exact
three compile regressions plus one runner import and no call; independent audit
and completion evidence.

## Implementation record

The completed slice adds a 26-line definition module plus one semantic umbrella
import. It publishes exactly the partial adapter and no helper, carrier,
constructor, coercion, instance, default, or alternate failure representation.
The operation and its generated equation report exactly `[propext]`.

The 54-line properties module plus one umbrella import publishes exactly the
two required simp branch laws. Both directly apply the matching ADR-0105 law,
report exactly `[propext]`, terminate, and converge with explicit unfolding of
the adapter.

The 83-line compile-only module plus one runner import contains exactly three
private examples. Two directly apply the fully qualified branch laws. The third
rewrites by the new present law and applies ADR-0108 to connect parent-indexed
initialization to total write/read behavior. No runtime declaration, assertion,
fixture, or runner call was added.

The implementation commits are `e4bd5fd` (231 changed lines), `ea12a69` (27),
`9c5b2fe` (55), and `4839106` (84), all below 300 changed lines; this completion
update is the fifth staged commit. Focused trust-zero checks, the 578-job full
build, the 1044-job full test run, metadata and kernel checks, diff checks,
declaration, generated-equation, axiom, dependency, simp-convergence,
proof-masking, and runtime inventories, and independent P0-P3 audits pass.

## Publication and consequences

This internal adapter changes no frozen or published boundary. One
caller-supplied storage selector can be checked against `initialWorld`, used as
the derived working WorldState, and on success passed directly to the existing
total storage semantics without introducing a broader contract-entry model.
