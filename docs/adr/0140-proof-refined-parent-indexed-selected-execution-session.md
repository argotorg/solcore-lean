# ADR-0140: Proof-refined parent-indexed selected-execution session

- Status: Accepted
- Decision date: 2026-08-30
- Scope: bind one selected run's fixed configuration to every fuel resumption
- Implementation: Complete

## Context

ADR-0138 retains every branch of parent-indexed selected execution and can
resume an exact exhausted handler context and Core state. Its low-level
`resumeWithFuel` operation must nevertheless be supplied again with the
initialization, immutable execution inputs, and completion policy. The result
carrier itself stores none of those values.

ADR-0139 therefore states its current-address lifetime law only for a theorem
that reuses one unchanged `ExecutionInputs` value. A caller can mechanically
resume a retained result with different inputs or a different completion
policy, but that operation has no continuation-of-the-same-run meaning. The
same problem applies to the initialization and the storage selector even
though the suffix does not repeat their lookups.

The raw operations remain useful proof and implementation primitives. The next
layer should provide a safe unit for ordinary resumable execution without
changing their behavior or prematurely defining nested calls, scheduling, or
transactions.

## Decision

Add one proof-refined carrier indexed by the existing parent working pair:

```lean
structure ParentIndexedSelectedExecutionSession
    (RollbackState : Type u) (Event : Type v) (TrapReason : Type w)
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) where
  initialization : ParentIndexedFrameInitialization
    RollbackState Event parentWorking
  storageAddress : Address
  inputs : HostStorageDriver.ExecutionInputs
  doneOutcome :
    HostStorageDriver.Context RollbackState (FrameTrace Event) →
      Core.Value → Core.Store → FrameOutcome TrapReason
  providedFuel : Nat
  result : ParentIndexedSelectedExecutionResult
    RollbackState Event TrapReason parentWorking
  result_eq_run :
    result = initialization.runCodeWithStorageParentIndexedResult
      storageAddress inputs providedFuel doneOutcome
```

`providedFuel` is the total budget supplied to the run represented by the
session. It is not a claim about fuel consumed, gas charged, or remaining gas.
It increases when more budget is offered even if the retained result is
already terminal.

The equality field is operational provenance only: the stored result is
exactly the result of the stored configuration at the stored total budget. It
does not claim that an external caller, child frame, transaction, scheduler,
or source construct created the session.

## Construction

Add a `start` operation taking the five ordinary run inputs before `result`:
initialization, storage Address, complete `ExecutionInputs`, completion policy,
and initial fuel. It performs exactly
`runCodeWithStorageParentIndexedResult` and stores the result with an `rfl`
proof.

Publish exact projection equations for every stored field. In particular,
`start ... fuel`.result is the existing branch-complete run at `fuel`; there is
no alternate selection, classifier, checkpoint, or completion constructor.

Do not add a constructor that accepts an arbitrary result without the equality
proof. The structure remains proof-refined even though Lean users may construct
it directly when they can establish the exact run equation.

## Resumption

Add one method:

```lean
session.resumeWithFuel additional
```

It accepts only the additional natural-number budget. It must not accept a
replacement initialization, storage Address, `ExecutionInputs`, completion
policy, parent working pair, handler context, or Core state.

The new result is obtained by applying ADR-0138's retained-result
`resumeWithFuel` to `session.result` with the configuration already stored in
the session. The updated total is
`session.providedFuel + additional`. The existing actual-run split theorem
proves the new invariant:

```text
updated.result
  = stored configuration run once at
      session.providedFuel + additional
```

Thus an exhausted suffix reuses its exact retained context and Core state,
while the session still certifies equality with a one-shot run at the total
budget. Storage refinement, code lookup, initial Core-state construction, and
the immediately preceding handled request are not replayed by the executable
resumption path.

The four terminal result constructors remain exact result identities. Their
session budget still records the newly offered amount, and the invariant is
maintained by the corresponding one-shot stability theorem.

## Exact proof interface

Expose laws for:

- every `start` projection and its exact result equation;
- every `resumeWithFuel` projection;
- preservation of the exact initialization, storage Address, complete
  execution inputs, and completion policy;
- addition of the supplied budget and exact use of the retained-result
  resumption operation;
- the invariant that every session result is the stored one-shot run at
  `providedFuel`;
- whole-session zero identity;
- whole-session sequential addition, where resuming by `first` and then
  `second` equals resuming once by `first + second`, including all proof fields;
- impossibility of the raw-fault branch for every session created by `start`
  or subsequent session resumption;
- exact compatibility erasure of `session.result` to the existing nested
  `Option` entry point; and
- reuse of the existing exact branch, completed-continuation, and
  return/revert/trap fold theorems after rewriting by `result_eq_run`.

Equality of whole sessions uses proof irrelevance for the stored certificate;
it must not weaken to equality of only selected observations.

The resumption addition proof must reuse ADR-0138's result-resumption algebra.
The invariant proof must reuse its actual-run split theorem. Neither proof may
unfold the recursive driver or rerun selection from the initial WorldState.

## Required regressions

Compile-time consumers must instantiate the carrier and apply:

- all construction and resumption projections;
- the stored one-shot invariant;
- whole-session zero and addition;
- checked no-fault and legacy-erasure coherence;
- all five existing exact branch characterizations through the invariant; and
- completed plain-continuation and return/revert/trap fold coherence through
  the invariant.

Executable tests reuse the measured ADR-0138 program:

- start at fuel 9 with the exact pre-write request retained;
- resume by 1 and match the one-shot fuel-10 post-write state;
- resume that session by 5 and match the one-shot fuel-15 request state;
- compare direct `9 + 7` and sequential `9 + 1 + 6` completion with the
  one-shot fuel-16 result;
- prove and observe that the storage write was handled exactly once;
- exercise zero additional budget and terminal completion resumption; and
- retain exact handler context, Core state, value, Store, continuation, and
  fold observations.

A second regression reuses ADR-0139's distinct current-address fixture. A
session started with one current Address must resume to that Address's exact
result. The resumption call has no parameter through which the alternate
current Address or alternate completion policy can be supplied. A different
current Address requires a distinct `start` call and therefore a distinct
certified session.

Storage-absent and code-absent starts must remain distinct terminal results.
Do not fabricate a certified raw-fault session: checked selected execution
already proves that an actual session cannot produce one.

## Dependency and publication boundary

The carrier belongs in Semantics above parent-indexed selected execution. The
base definition and `start` depend only on the existing branch-complete
producer. Resumption depends on ADR-0138's retained-result and actual-run fuel
laws. Core remains independent of WorldState and frame semantics.

The existing raw producer, raw result carrier, raw resumption operation,
legacy nested-`Option` API, and all of their theorem statements remain
unchanged. The session is an additive safe interface, not a replacement or a
new public format.

Acceptance requires focused and full builds, the executable suite, trust-zero
and warning-as-error checks for every changed Lean root, metadata and semantic
kernel checks, diff hygiene, and an independent contract audit.

No Wire tag, Oracle command, schema, profile, metadata capability, Surface
form, grammar, parser rule, or source elaboration is added. The parser proof
program remains paused. The root README does not change.

## Non-goals

This ADR does not define or prove:

- a child invocation, parent suspension, parent result delivery, call stack,
  recursion, reentrancy, callback, or scheduling transition;
- a direct, delegate, static, library, creation, fallback, or receive call
  kind, or any relationship among storage, code, current, caller, or target
  Addresses;
- origin, signer, authority, account ownership, balance transfer,
  affordability, nonce, gas charging, refund, or fork policy;
- transaction entry, checkpoint capture, commit, rollback application,
  persistence, or finalization;
- conversion of Core values or Store to Bytes, automatic outcome selection,
  ABI, return-data delivery, calldata layout, or storage layout;
- actual historical runtime lineage beyond equality with the stored pure run;
  or
- a public compatibility promise or concrete syntax.

## Implemented sequence

1. added this decision and activated the session slice in internal docs;
2. implemented the proof-refined carrier and exact `start` projections;
3. implemented closed resumption and preserved the one-shot invariant;
4. proved whole-session algebra, no-fault, compatibility, and completion
   coherence;
5. added compile-time consumers and measured ADR-0138/ADR-0139 regressions; and
6. completed full validation, independent audit, and completion-doc
   synchronization.

## Implementation record

The carrier, `start`, and closed `resumeWithFuel` are implemented. Resumption
accepts only an additional `Nat`; the initialization, storage Address, complete
execution inputs, completion policy, and parent index remain fixed. Every
session certifies that its exact result is the stored configuration run once at
`providedFuel`. Whole-session canonicalization, zero, and sequential-addition
laws preserve that invariant, and all five result branches, checked no-fault,
legacy and plain continuation views, and return/revert/trap folds are covered.

The ADR-0138 regression starts at fuel 9, resumes through exact one-shot
boundaries 10 and 15, and completes at 16 without replaying the handled write.
A completed session offered another 100 units records total budget 116 while
retaining its terminal result. The ADR-0139 regression resumes fuel 17 by 13 to
the one-shot fuel-30 result; changing only `currentAddress` requires a distinct
start, and another 7 units leave the completed result unchanged.

The 685-job build, 1,258-job test executable build, and full test run pass. All
11 changed Lean roots pass trust-zero with warnings as errors. Metadata,
semantic-kernel, and diff checks pass; 32 public theorem reports use only
`propext` and `Quot.sound`. Independent audits found no P0-P2 issue and the one
P3 documentation typo was corrected. The root README and public Core, Wire,
Oracle, and Surface boundaries remain unchanged.

## Consequences

Ordinary resumable selected execution can no longer accidentally replace its
fixed run inputs or completion policy at the resumption call. Every session
state carries a checked equation back to one canonical run at its cumulative
provided budget, while exact retained-state execution remains the mechanism
used to advance it.

This closes a concrete API-discipline gap without pretending that nested calls
or a scheduler already exist. A later runtime can retain this unit, but must
separately specify invocation construction, parent suspension and delivery,
fuel allocation, and transaction policy.
