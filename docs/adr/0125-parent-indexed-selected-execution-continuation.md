# ADR-0125: Parent-indexed selected execution continuation

- Status: Accepted
- Decision date: 2026-08-29
- Scope: connect parent-indexed initialization to completed selected execution
- Implementation: Not started

## Context

ADR-0098 constructs checkpointed working values relative to one caller-chosen
parent working pair. ADR-0115 refines those values when the selected storage
Account exists. ADR-0124 selects checked code, runs the storage handler, and
constructs a plain continuation context only after normal completion.

These operations compose, but there is no named executable boundary carrying
their distinctions through to the existing parent-indexed continuation type.
A caller must currently perform storage refinement, code selection, execution,
completion adaptation, and proof-bearing reconstruction separately.

The parent-indexed context already has the required consumers. It resolves a
return to terminal working values, resolves a revert to the exact parent state
and rollback with the retained working trace, and supports opt-in trap rollback
and propagation payloads. Reimplementing those consumers would create a second
frame lifecycle.

The safe next connection is a pure composition that returns that existing
proof-bearing context and preserves every partial boundary.

## Decision

Add one operation in `ParentIndexedFrameInitialization`:

```lean
def runCodeWithStorageParentIndexedContinuationContext?
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking)
    (storageAddress codeAddress : Address)
    (fuel : Nat)
    (doneOutcome :
      HostStorageDriver.Context RollbackState (FrameTrace Event) →
        Core.Value → Core.Store → FrameOutcome TrapReason) :
    Option
      (Option
        (Option
          (ParentIndexedFrameContinuationContext
            RollbackState Event TrapReason parentWorking)))
```

The implementation uses three nested `Option.map` operations:

```lean
(initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
    storageAddress).map fun context =>
  (context.runCodeWithStorageContinuationContext?
    codeAddress fuel doneOutcome).map fun completed =>
      completed.map fun continuation =>
        ParentIndexedFrameContinuationContext.fromTraceExtension
          parentWorking
          initialization.workingRollback
          initialization.initialTraceExtension
          continuation.result
```

No layer uses `bind`. No failure state is flattened or assigned a new meaning.

## Four observable results

The result has four exact shapes:

- `none`: the initialization's working WorldState lacks the selected storage
  Account;
- `some none`: storage is present, but the working WorldState has no checked
  code at `codeAddress`;
- `some (some none)`: storage and code were selected, but checked execution ran
  out of fuel; and
- `some (some (some continuation))`: checked execution completed and produced
  the parent-indexed continuation.

The first two failures occur before Core execution. The third is an attempted
execution and remains distinct. Checked no-fault safety means that a selected
inner failure is exactly out-of-fuel. A raw fault is not converted to a trap.

## Parent-indexed reconstruction

ADR-0124's plain continuation already contains the exact terminal working
WorldState and caller-selected outcome in `continuation.result`. The new
operation retains that result and supplies the parent relationships through
`ParentIndexedFrameContinuationContext.fromTraceExtension`:

- checkpoint WorldState and checkpoint effects come from `parentWorking`;
- working rollback comes from the parent-indexed initialization;
- the initial trace extension starts at the exact parent trace; and
- the carrier includes both checkpoint equality and trace-prefix evidence.

The combined storage driver preserves the complete checkpoint and working
effect journal. Therefore forgetting the proof fields of the reconstructed
parent-indexed context yields the exact ADR-0124 plain continuation, not merely
a context with matching selected projections.

This connection is specific to the current storage handler's preservation of
working effects. A future handler that records events or mutates rollback state
must supply its own extension-preservation argument rather than reuse this
fixed initial extension blindly.

## Exact proof interface

Expose exactly six public laws.

The first four characterize each result shape:

1. outer `none` iff `initialWorld.account? storageAddress = none`;
2. `some none` iff present-storage refinement succeeds and selected code is
   absent;
3. `some (some none)` iff refinement succeeds and the selected run returns an
   exact out-of-fuel driver result; and
4. `some (some (some parentContinuation))` iff refinement succeeds, the
   existing ADR-0124 wrapper returns a completed plain continuation, and the
   parent continuation is its canonical parent-indexed reconstruction.

The fifth law inverts a completed result and states whole-context coherence:

```lean
∃ context continuation,
  initialization.toCheckpointedWorkingPairWithPresentStorageAccount?
      storageAddress = some context ∧
  context.runCodeWithStorageContinuationContext?
      codeAddress fuel doneOutcome = some (some continuation) ∧
  parentContinuation.toFrameContinuationContext = continuation
```

The sixth law states that an exact completed parent-indexed result is unchanged
under additional fuel. There is no stability law for any failure shape.

Only the outer `none` equivalence is a simplification rule. The remaining laws
are explicit inversions, coherence, or cross-fuel results and stay outside the
global simplifier.

## Existing lifecycle consumers

Whole-context coherence lets callers use existing operations without another
wrapper:

- `FrameContinuationContext.resolve`;
- `FrameResolutionResult.continue?`;
- parent-indexed returned and reverted resolution laws;
- `trapRollback?`; and
- `trapPropagationPayload?`.

Do not lift `resolve` or `continue?` through the three optional layers. Doing so
would add callback rejection and trapped resolution as more indistinguishable
`none` results. Branch selection remains explicit at the caller.

## Required regressions

Add compile-time consumers for:

- all four result-shape equivalences;
- completed parent-to-plain whole-context coherence;
- transport of that equality through existing resolution and continuation;
- returned and reverted parent-indexed resolution;
- trap rollback or propagation payload selection; and
- exact completed stability under larger fuel.

The new operation only composes already executed lower boundaries. Existing
runtime regressions cover storage absence, code absence, fuel-22 exhaustion,
fuel-28 completion, fuel-64 stability, terminal storage and local Store, and
all three frame outcomes. The existing fixture uses an opaque `List Nat` trace,
whereas the parent-indexed carrier requires `FrameTrace Event`; duplicating the
program and WorldState solely to retest pure `Option.map` composition adds no
new runtime observation. This slice therefore adds no second runtime fixture.

## Dependency boundary

The definition depends on parent-indexed initialization refinement, ADR-0124's
selected continuation wrapper, and the existing parent-indexed constructor.
Its properties reuse the corresponding branch and preservation laws. Core does
not import the parent or frame layer.

No parser, Surface, ABI, Oracle, Wire, schema, profile, gas, or public runtime
module changes. The root README does not change.

## Non-goals

This ADR does not define:

- an actual parent machine, parent resumption, or byte delivery rule;
- a frame stack, depth, scheduler, nested invocation, or reentrancy;
- parent mutation after return or revert;
- trap catch versus fatal policy;
- transaction commit, final observation, or atomicity;
- a new event kind or trace-recording handler;
- sufficient fuel, normalization, or retry policy;
- a mapping from Core values and local cells to ABI bytes;
- caller, current, callee, call value, calldata, or call kind; or
- source syntax, parsing, elaboration, or publication.

## Implementation sequence

Keep every green commit below roughly 300 changed lines:

1. record this four-way parent-indexed execution boundary;
2. add the nested-option operation and exact pre-completion branch laws;
3. add completed reconstruction, whole-context coherence, and fuel stability;
4. add direct compile-time consumers of every new law and existing lifecycle
   operations; and
5. run full validation and independent audit, then synchronize acceptance
   evidence and current-facing internal documents.

## Consequences

One executable internal entry point can now begin with a parent-indexed
initialization and end, only after normal checked completion, with a context
whose checkpoint and trace relationships to that exact parent are carried by
the type. Every earlier failure remains distinguishable.

This is still a value-level lifecycle boundary, not nested-call execution.
Actual delivery requires a parent machine and argument/result policy that are
not yet justified by the current internal semantics.
