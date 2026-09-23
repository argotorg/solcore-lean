# ADR-0138: Branch-complete resumable parent-indexed selected execution

- Status: Accepted
- Decision date: 2026-08-29
- Scope: retain and resume every internal branch of parent-indexed selected execution
- Implementation: Complete

## Context

The current parent-indexed entry point returns three nested `Option` layers.
They distinguish missing storage, missing code, exhausted execution, and
completed execution. This interface is intentionally stable, but it discards
the exact context and Core state of exhaustion. Its generic completion adapter
also represents a raw driver fault with the same innermost `none`, although a
checked selected run proves that branch unreachable.

ADR-0136 now proves that an exhausted handled run can continue from its exact
context and Core state. Splitting a fixed budget this way is exactly equal to a
single run with the summed budget. The highest parent-indexed boundary cannot
use that result directly because its nested options no longer carry the
exhausted state.

The next step is an internal, branch-complete carrier. It must retain enough
data to resume exhaustion without repeating storage refinement, code lookup,
the executed Core prefix, or an already handled request. It must not assign a
frame meaning to exhaustion or a raw machine fault.

## Decision

Add one result type indexed by the existing parent working pair:

```lean
inductive ParentIndexedSelectedExecutionResult
    (RollbackState : Type u) (Event : Type v) (TrapReason : Type w)
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) where
  | storageAbsent
  | codeAbsent
  | outOfFuel
      (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
      (state : Core.State)
  | fault
      (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
      (error : Core.MachineFault)
      (state : Core.State)
  | unsupported
      (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
      (suspension : Core.HostSuspension)
      (remainingFuel : Nat)
  | completed
      (context : HostStorageDriver.Context RollbackState (FrameTrace Event))
      (value : Core.Value)
      (store : Core.Store)
      (continuation : ParentIndexedFrameContinuationContext
        RollbackState Event TrapReason parentWorking)
```

The two absence constructors contain no invented state. The other four carry
the exact handler context and every field of the corresponding
`HostDriverOutcome`. Completion additionally carries the canonical existing
parent-indexed continuation. ADR-0149 added `unsupported` when generic host
policies began rejecting requests explicitly instead of silently handling
them.

Add a total operation on `ParentIndexedFrameInitialization`, provisionally
named `runCodeWithStorageParentIndexedResult`. It takes the same
`storageAddress`, immutable `HostStorageDriver.ExecutionInputs`, fuel, and
`doneOutcome` policy as the existing nested-option operation. It performs the
same storage refinement and code selection, then matches all four driver
outcomes. It returns one of the six constructors and never returns `Option`.

The completed continuation is built with
`ParentIndexedFrameContinuationContext.fromTraceExtension`, using the same
`parentWorking`, `workingRollback`, `initialTraceExtension`, final handler
context, exact value and Store, and caller-owned `doneOutcome` as the existing
operation. No second checkpoint, trace, or completion policy is introduced.

## Exact branch contract

Publish an exact characterization for each constructor. Each selected branch
quantifies the exact refined context and states that refinement returned it;
the run equation then uses that same context:

1. `storageAbsent` iff
   `initialization.initialWorld.account? storageAddress = none`;
2. `codeAbsent` iff storage refinement returns an exact context and that
   context's working WorldState has no code at `inputs.codeAddress`;
3. `outOfFuel finalContext state` iff storage refinement returns an exact
   selected context and `runCodeWithStorage? inputs fuel` returns exactly
   `some ⟨finalContext, .outOfFuel state⟩`;
4. `fault finalContext error state` iff the same selected run returns exactly
   `some ⟨finalContext, .fault error state⟩`;
5. `unsupported finalContext suspension remainingFuel` iff the selected run
   returns exactly
   `some ⟨finalContext, .unsupported suspension remainingFuel⟩`; and
6. `completed finalContext value store continuation` iff the selected run
   returns exactly `some ⟨finalContext, .done value store⟩` and `continuation`
   is the canonical parent-indexed reconstruction described above.

These are whole-constructor equalities, not predicates that retain only an
outcome tag. They must expose the exact context, Core state, error, value,
Store, and continuation supplied by execution.

The classifier must contain a structural `.fault` match. Separately prove that
the top-level checked selected execution cannot equal a `fault` constructor,
using the existing checked no-fault theorem. Do not remove the constructor or
make the classifier partial merely because the current checked producer makes
that branch unreachable.

## Compatibility erasure

Do not delete, rename, change, or reimplement the public behavior of
`runCodeWithStorageParentIndexedContinuationContext?` or any of its existing
branch, coherence, and larger-fuel theorems.

Add one explicit erasure from the new carrier to its result type:

```text
storageAbsent                 -> none
codeAbsent                    -> some none
outOfFuel context state       -> some (some none)
fault context error state     -> some (some none)
unsupported context suspension remainingFuel
                              -> some (some none)
completed context value store continuation
                              -> some (some (some continuation))
```

The fault mapping is deliberately lossy and reproduces the old completion
adapter's structural result; it does not identify fault and exhaustion in the
new carrier and does not convert either to a trap.

Prove that erasing an actual new run equals the existing three-`Option` run
exactly. On the completed branch, prove that both APIs expose the same
`ParentIndexedFrameContinuationContext`, not only equal projections. No
inverse erasure theorem is required because the old type cannot recover an
exhausted context, state, or fault.

## Resumption

Add one total `resumeWithFuel` operation for the new carrier. It takes an
initialization, `ExecutionInputs`, `doneOutcome`, and the additional budget. A
carrier does not index or store those immutable arguments, so sameness is
expressed by using the same variables in split and algebraic laws; arbitrary
forged carriers rely on caller discipline. It does not take `storageAddress`;
the actual-run laws fix the selector of the originating and one-shot runs.

Only `outOfFuel context state` executes. That branch runs
`HostStorageDriver.run context inputs additional state` and classifies its
exact result as `outOfFuel`, `fault`, `unsupported`, or `completed`. It uses
the original initialization and `doneOutcome` only to reconstruct a later
completed parent continuation. The suffix must not:

- repeat storage refinement or inspect `storageAddress` again;
- repeat code lookup or rebuild `Core.State.initial`;
- replay any Core transition from the exhausted prefix;
- handle the request immediately before exhaustion a second time; or
- replace any field of the retained mutable context or immutable inputs.

`storageAbsent`, `codeAbsent`, `fault`, and `completed` are exact identities
for every additional budget. An `unsupported` request remains suspended with
the same context and suspension while its retained fuel increases by the newly
offered amount; the rejecting handler is not invoked. In particular, a raw
fault stays a raw fault with the same context, error, and state, and completion
retains the same context, value, Store, and continuation.

## Resumption laws

The proof interface must include:

- constructor equations for all six branches;
- exact split/summed coherence for an actual top-level run:
  resuming the result at `fuel` by `additional` equals the result of running
  once at `fuel + additional`;
- zero-additional identity for an actual run result, but not for an arbitrary
  forged `outOfFuel` carrier;
- sequential resumption for every carrier under one fixed initialization,
  `ExecutionInputs`, and `doneOutcome`, with `first` then `second` equal to one
  resumption by `first + second`; the actual-run corollary also fixes its
  originating storage selector;
- exact preservation of every carried field on absence and terminal branches;
  and
- an iff inversion specifically for resuming `.outOfFuel context state` to a
  completion: the exact retained context and state run under the supplied
  handler inputs to the carried final context, value, and Store, and the
  continuation equals the canonical reconstruction.

The split proof must reuse the ADR-0136 storage-driver law. It may classify the
suffix result, but may not unfold and replay the recursive driver or prove the
equation by fresh lookup from the initial WorldState.

## Completed continuation and fold coherence

From an actual producer equation ending in
`completed finalContext value store continuation`, prove:

- `continuation.toFrameContinuationContext` is the exact existing completed
  plain continuation built from `finalContext`, `value`, `store`, and
  `doneOutcome`;
- compatibility erasure returns
  `some (some (some continuation))` from the old API;
- for each policy equation making `doneOutcome finalContext value store`
  returned, reverted, or trapped, the existing fold receives respectively the
  final working pair, or the parent checkpoint rollback plus final working
  trace, with the exact returned or reverted Bytes, or exact trap reason; the
  carried Core value and Store are policy inputs, not fold callback arguments; and
- resuming that completed carrier leaves both the continuation and every fold
  result definitionally or propositionally unchanged.

The plain-context claim is an inversion of the named producer, not a theorem
about an arbitrarily constructed `completed` value whose continuation field
could have been chosen independently.

Do not add a second resolution fold over the six-way carrier. Absence,
exhaustion, raw fault, and unsupported policy have no justified
frame-resolution meaning.

## Required regressions

Add compile-time consumers that apply every branch equivalence, checked
no-fault theorem, erasure-coherence theorem, six resumption equations,
split/summed law, actual-run zero law, sequential law, and completed
plain-context and fold coherence.

Executable regressions must cover:

- distinct storage-absent and code-absent results;
- a measured exhausted result retaining its exact context and Core state;
- exhaustion followed by exhaustion and exhaustion followed by completion;
- split and one-shot runs with matching context, state, value, Store, and fold
  observations after pattern matching their branches;
- a request-sensitive prefix showing that resumption does not repeat the last
  handled request;
- zero additional fuel on an actual run and two fixed-policy additions;
- compile-time exact identity of constructed absence, fault, and completed
  carriers; and
- completed return, revert, and trap folds through the existing fold.

Reuse existing checked programs and measured budgets where they expose these
observations. A synthetic fault carrier may test terminal identity, but no
checked runtime fixture may pretend that selected checked execution faults.
Exact equality of proof-bearing continuations and constructed terminal
carriers is compile-time evidence. Runtime tests pattern-match branches and
compare observable states and folds; they do not invent `BEq` for proof fields.

## Dependency and validation boundary

The carrier and classifier live in Semantics above Core. They may depend on
parent-indexed initialization, selected storage execution, ADR-0136
resumption, and existing parent continuation construction and fold modules.
Core must not import frame or WorldState semantics.

Acceptance requires focused and full builds, the complete executable test
suite, trust-zero and warning-as-error checks for every changed Lean root,
metadata and semantic-kernel checks, whitespace and diff checks, and an axiom
audit of the six branch laws, erasure coherence, split/summed resumption,
sequential resumption, and completed coherence. No placeholder, custom axiom,
trust increase, new noncomputable dependency, or accidental simp rule is
accepted.

Independently inspect that the old three-`Option` declarations and theorem
statements remain unchanged; only the out-of-fuel branch calls the driver;
resumption performs no selection or prefix replay; exact carried fields are
not weakened to projections; and no parser or public-format dependency leaks
into the implementation.

## Implementation sequence

Keep every green commit at roughly 300 changed lines or fewer. A numbered step
may span multiple green commits; in particular separate carrier/classifier,
branch laws, resumption definitions/equations, algebraic laws, and compile-time
and runtime regressions when necessary:

1. record and activate this decision without changing execution;
2. add the six-way carrier, total classifier, and exact branch laws;
3. add explicit compatibility erasure and whole-result coherence with the
   existing nested-option API;
4. add fuel continuation and split, zero, sequential, and identity laws;
5. add completed plain-context and existing-fold coherence;
6. add focused compile-time and executable regressions;
7. run validation and independent P0-P3 audits; and
8. synchronize acceptance evidence and current-facing internal documents.

## Implementation evidence

The implementation provides the exact six-way carrier, six whole-branch
equivalences, and the checked no-fault theorem. Explicit compatibility erasure
equals the unchanged nested-`Option` producer as a whole. Resumption invokes
the driver only for `outOfFuel`; unsupported requests remain suspended while
offered fuel accumulates. Exact split/summed-budget, actual-run zero,
sequential addition, and completed-result inversion laws retain the same
initialization, immutable inputs, and completion policy.

Completion coherence recovers the exact existing plain continuation and legacy
result. Return, revert, and trap use the existing parent fold with their exact
inputs, and resuming a completed carrier preserves the continuation and every
fold result. Executable regressions measure fuel 9, 10, 15, and 16 and cover
both absence branches, retained exhaustion, request non-replay, synthetic fault
identity, completion, and all three fold outcomes.

The 673-job full build, 1,234-job test executable build, and full test run pass.
All 16 changed Lean roots pass trust-zero with warnings as errors; metadata,
semantic-kernel, and diff checks pass. The 21 audited theorem reports use only
`propext` and `Quot.sound`. The independent audit found no P0-P3 issue. The
three legacy implementation/proof files and root README remain unchanged.

## Non-goals

This ADR does not decide or add:

- a conversion from `Core.Value` or `Core.Store` to bytes;
- a mapping from machine faults or exhaustion to `FrameOutcome` or trap
  reasons;
- trap catch, propagation, retry, fatality, or diagnostics policy;
- parent mutation, callback delivery, parent-machine resumption, or a frame
  stack;
- nested invocation, recursion, reentrancy, scheduling, or call depth;
- current, caller, or callee identity, call kind, call value, calldata
  ownership, balance transfer, or authority;
- gas, refunds, wall-clock cost, sufficient fuel, fairness, or termination;
- checkpoint lifetime, ownership, persistence, commit, or transaction
  atomicity; or
- source syntax, parser, elaboration, ABI, Wire, schema, profile, or any public
  protocol.

The root README does not change.

## Consequences

Internal callers can inspect every selected-execution branch without losing
the exact state required for bounded resumption. A split execution remains the
same execution: it retains handler updates, resumes the exhausted Core state,
and produces the exact one-shot result under fixed inputs and policy.

This remains an internal execution-result boundary. It makes no decision
about how a completed Core value becomes external bytes or how any branch is
delivered to a parent machine.
