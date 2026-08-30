# ADR-0144: Parent-indexed selected checked Word execution

- Status: Accepted
- Decision date: 2026-08-30
- Scope: add storage-presence provenance and canonical parent return to ADR-0143
- Implementation: Complete

## Context

ADR-0143 retains exact absent, non-Word, and Word code selection inside a
storage-backed context. It runs only the selected checked Word program, keeps
its raw result, and projects canonical 32-byte return data without confusing
non-execution with fuel exhaustion.

That context already requires a present storage Account. A caller beginning at
`ParentIndexedFrameInitialization` must first refine a chosen storage Address
to such a context. A successful Word completion must also be lifted back to a
`ParentIndexedFrameContinuationContext` whose checkpoint is the exact indexed
parent working pair.

The repository has an older generic parent-selected path. It executes every
selected `CheckedHostCoreProgram`, accepts an arbitrary completion policy, and
uses nested options or a five-branch result. It cannot be used as a total
erasure of ADR-0143: a non-Word selection executes there but deliberately does
not execute here, and arbitrary completion policy may return, revert, or trap
where this path fixes a canonical returned Word.

## Decision

Add one present-storage provenance carrier:

```lean
structure ParentIndexedSelectedCheckedWordExecution
    {parentWorking :
      WorldState ×
        FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs) where
  initialContext :
    HostStorageDriver.Context RollbackState (FrameTrace Event)
  context_refined :
    initialization
        |>.toCheckpointedWorkingPairWithPresentStorageAccount?
          storageAddress =
      some initialContext
  execution : SelectedCheckedWordExecution initialContext inputs
```

The carrier introduces no code or raw-result branch. Its `execution` is the
complete ADR-0143 value. `initialContext` is not an arbitrary duplicate: the
refinement equality proves that it is exactly the context derived from this
initialization and storage Address.

The initialization, storage Address, and execution inputs are type indices.
They cannot be replaced during fuel resumption. The indexed `parentWorking` is
therefore the exact checkpoint origin for later parent continuation.

## Total storage refinement

Define:

```lean
def ParentIndexedSelectedCheckedWordExecution.start?
    (initialization : ParentIndexedFrameInitialization
      RollbackState Event parentWorking)
    (storageAddress : Address)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    Option
      (ParentIndexedSelectedCheckedWordExecution
        initialization storageAddress inputs)
```

`start?` matches only the existing present-storage refinement. Missing storage
produces outer `none`. A present storage context produces the provenance
carrier whose inner value is exactly
`SelectedCheckedWordExecution.start context inputs fuel`.

This single outer option means only storage-Account absence. Once a value is
present, ADR-0143 continues to distinguish code absence, selected non-Word
code, selected Word exhaustion, and selected Word completion. No nested option
is the primary branch interface.

Prove both directions exactly:

```text
start? initialization storageAddress inputs fuel = none iff
  initialization.initialWorld.account? storageAddress = none

start? initialization storageAddress inputs fuel = some execution iff
  execution has the exact refined context and canonical inner start
```

Every manually constructed carrier must canonicalize to `start?` at its inner
cumulative provided fuel. The initial-context refinement proof must also expose
that its checkpointed values equal
`initialization.toCheckpointedWorkingPair`.

Provide a simple dependent-pair erasure and prove the whole producer equation:

```text
(start? initialization storageAddress inputs fuel).map toExecutionSigma =
  (initialization
    |>.toCheckpointedWorkingPairWithPresentStorageAccount? storageAddress).map
      (fun context =>
        ⟨context, SelectedCheckedWordExecution.start context inputs fuel⟩)
```

This equation makes explicit that the carrier refines the existing storage
selection rather than implementing a second selector.

## Closed fuel resumption

Define `resumeWithFuel` on a present provenance carrier. It preserves
`initialContext` and `context_refined` and calls only ADR-0143
`execution.resumeWithFuel`.

Prove:

```text
some (execution.resumeWithFuel additional) =
  start? initialization storageAddress inputs
    (execution.execution.providedFuel + additional)

execution.resumeWithFuel 0 = execution

(execution.resumeWithFuel first).resumeWithFuel second =
  execution.resumeWithFuel (first + second)

(start? ... fuel).map (fun execution =>
  execution.resumeWithFuel additional) =
  start? ... (fuel + additional)
```

The last law covers storage absence without inventing an absent execution
session. Present branches reuse ADR-0143's retained raw continuation rather
than rerunning from the program entry.

## Canonical returned parent continuation

For any `TrapReason`, define a proof-guarded parent constructor:

```lean
def ParentIndexedSelectedCheckedWordExecution.toReturnedContinuation
    (execution : ParentIndexedSelectedCheckedWordExecution
      initialization storageAddress inputs)
    (completion :
      WordReturnedFrameCompletion RollbackState (FrameTrace Event))
    (completed : execution.execution.completion? = some completion) :
    ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking
```

Requiring the exact inner completion proof prevents unrelated completion data
from being assigned the carrier's parent provenance. Then define the primary
optional projection by matching the inner completion, supplying that match
equation, and retaining both existing values:

```lean
def ParentIndexedSelectedCheckedWordExecution.returnedCompletion? :
    Option
      (WordReturnedFrameCompletion RollbackState (FrameTrace Event) ×
        ParentIndexedFrameContinuationContext
          RollbackState Event TrapReason parentWorking)
```

The continuation-only convenience view is exactly
`returnedCompletion?.map Prod.snd`; it is not a second producer.

The primary view matches only `execution.execution.completion?`. For a
successful completion it pairs that exact completion with:

```text
ParentIndexedFrameContinuationContext.fromTraceExtension
  parentWorking
  initialization.workingRollback
  initialization.initialTraceExtension
  completion.toFrameContinuationContext.result
```

The inner result is exactly `.returned completion.returnData`. No caller-
supplied `doneOutcome` can reinterpret canonical Word completion as revert or
trap. Exhaustion and all non-execution branches produce no parent continuation
and remain observable through the retained ADR-0143 execution.

Prove that every successful parent projection retains the exact completion and
that forgetting its parent index yields exactly
`completion.toFrameContinuationContext`. This coherence proof must use:

- `context_refined`, fixing the initial checkpointed values;
- checked Word completion reconstruction, fixing the final raw result; and
- existing storage-driver checkpoint and working-effect preservation.

Consequently, parent resolution returns the exact final working WorldState,
working effects, and canonical 32-byte data while retaining the indexed parent
checkpoint and trace prefix.

## Limited legacy coherence

Do not define a total erasure into the older nested-option or generic
parent-selected session interfaces. Such an erasure would necessarily lose the
non-Word branch or reinterpret it as an execution, and could lose exhaustion or
canonical return policy.

Expose only branch-local coherence that preserves meaning:

- storage absence agrees with the existing parent storage refinement;
- code absence agrees after an exact present-context refinement;
- under `selection = word code`, the retained raw run is the same checked-code
  raw run used by the generic context execution; and
- when an older `doneOutcome` is assumed to return the exact canonical bytes
  for the exact completed Word, its completed parent continuation agrees with
  this ADR's returned parent continuation.

The last theorem is conditional. No equality is claimed for arbitrary
`doneOutcome` or selected non-Word code.

## Exact proof interface

Expose laws for:

- `start?` storage-absent and exact present-context branches;
- provenance-carrier extensionality and canonical start;
- dependent-pair erasure and whole-producer storage-refinement coherence;
- exact initial values, parent checkpoint, working rollback, and parent trace;
- inner selection, raw execution, completion, and missing-completion delegation;
- present-carrier resumption projections, one-shot equality, zero, addition,
  and optional-start resumption;
- exact returned-completion and returned-parent-continuation construction;
- parent-to-plain continuation coherence;
- returned resolution data, final working values, and trace prefix;
- successful parent-continuation stability after further fuel; and
- the limited legacy branch coherence listed above.

Downstream proofs must not need to unfold the producer, inner execution, or
parent continuation constructor.

## Required regressions

Compile-time consumers must apply every new public theorem from an external
namespace.

Executable regressions must reuse the established parent fixture and cover:

- missing storage Account at small and large fuel as outer `none`;
- present storage with code absent and checked non-Word code as present outer
  values retaining their exact non-execution branches;
- Word exhaustion at fuel 9, 10, and 15 as present values without a returned
  parent continuation;
- Word completion at fuel 16 with the exact parent checkpoint, final working
  storage, working rollback and trace, Word, Store, canonical bytes, and
  returned resolution;
- exact 9+7, 10+6, and 15+1 present resumption, zero and addition laws, and
  terminal stability;
- optional-start resumption preserving storage absence; and
- successful plain-continuation and conditional generic-parent coherence.

## Dependency and publication boundary

The carrier depends only on existing parent initialization/storage refinement,
ADR-0143 execution, and existing parent continuation construction. It adds no
new code-selection, raw-result, frame-outcome, or resolution hierarchy.

This ADR adds no Wire tag, Oracle command, schema, profile, metadata capability,
Surface form, grammar, parser rule, or source elaboration. Parser work remains
paused. The root README does not change.

Acceptance requires focused and full builds, the executable suite, trust-zero
and warning-as-error checks for every changed Lean root, metadata and semantic
kernel checks, diff hygiene, axiom reports, and independent contract and
coverage audits.

## Non-goals

This ADR does not define or prove:

- a replacement or total erasure for ADR-0125, ADR-0138, or ADR-0140;
- execution, rejection, or trapping policy for selected non-Word code;
- a caller-selected returned, reverted, or trapped completion policy;
- parent resumption for missing storage as an invented execution value;
- parent-to-child input derivation, child-result delivery, call kind,
  scheduling, recursion, reentrancy, or a call stack;
- gas prices, consumed-gas reporting, refunds, balance transfer, transaction
  commit, rollback application, or persistence;
- Solidity ABI encoding, arbitrary Core-value serialization, a public byte
  contract, external compatibility promise, or concrete syntax.

## Implemented sequence

1. recorded the storage-provenance and parent-return contract;
2. added the present parent-indexed carrier and exact `start?` branches;
3. added closed present resumption and optional-start algebra;
4. added canonical returned-parent projection and plain coherence;
5. proved limited legacy coherence and added compile/runtime regressions; and
6. completed full validation, independent audits, and documentation sync.

The implementation exposes 6 definitions and 49 public theorems. All 55
public names are exercised from external test namespaces. Runtime regressions
cover storage absence and non-executing selections at fuel 0 and 64, Word
exhaustion at 9, 10, and 15, completion at 16, exact 9+7, 10+6, and 15+1
resumption, zero/addition/terminal stability, canonical bytes, retained Store,
parent checkpoint, final working storage, resolution, trace prefix, and the
conditional legacy-success correspondence.

The 723-job full build, 1,334-job test build, executable suite, and all 16
changed Lean roots pass. The direct Lean checks use trust level zero and treat
warnings as errors. Metadata, semantic-kernel, and diff checks pass. Every
public theorem depends only on the accepted `propext` and `Quot.sound` axioms.

## Consequences

The canonical selected Word path can begin at parent-indexed initialization,
retain storage and code non-execution reasons without branch duplication, and
produce a returned parent continuation with exact canonical bytes.

This is still not a top-level transaction or nested invocation. The next
vertical slice starts from an explicit initial `WorldState` and checked Core
contract, executes one top-level invocation, commits return, rolls back revert
and trap, and returns terminal data together with an exact state observation.
Nested calls and child-result delivery remain later work.
