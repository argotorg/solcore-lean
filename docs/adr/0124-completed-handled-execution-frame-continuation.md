# ADR-0124: Completed handled execution to frame continuation

- Status: Accepted
- Decision date: 2026-08-29
- Scope: connect completed handled Core results to existing frame lifecycle inputs
- Implementation: Not started

## Context

The internal storage driver now has a complete executable and relational proof
boundary. It selects checked code, handles typed requests, preserves exact
context updates, and distinguishes code-selection failure from an attempted
out-of-fuel execution. Existing frame semantics separately defines:

- `FrameOutcome` for returned bytes, reverted bytes, or a trap reason;
- `FrameCheckpointedWorkingPair` for checkpoint and speculative working values;
- `FrameContinuationContext` for resolving one completed frame; and
- exact return, revert, and trap resolution rules.

There is no operation connecting a completed `HostDriverResult` to those frame
inputs. A direct fixed conversion is not yet justified. Core values include
closures, cell references, and named data; interpreting a value may require the
Core-local store. ABI byte encoding is undecided. A Core `done` result also does
not by itself say whether the frame should return, revert, or trap.

Out-of-fuel is an implementation-relative incomplete observation, not a frame
trap. A raw machine fault is unreachable for checked execution, but generic raw
driver results still expose it and no trap taxonomy maps it to `FrameOutcome`.

The narrow safe connection is therefore a structural adapter for the `done`
branch, parameterized by caller-owned projection and completion policy.

## Decision

Add one generic partial adapter:

```lean
def HostDriverResult.toFrameContinuationContext?
    (result : HostDriverResult Context)
    (values :
      Context → FrameCheckpointedWorkingPair RollbackState TraceState)
    (doneOutcome :
      Context → Core.Value → Core.Store → FrameOutcome TrapReason) :
    Option (FrameContinuationContext RollbackState TraceState TrapReason) :=
  match result.outcome with
  | .done value store =>
      some <| FrameContinuationContext.fromCheckpointedWorkingPair
        (values result.context)
        (doneOutcome result.context value store)
  | .outOfFuel _ => none
  | .fault _ _ => none
```

`values` tells the adapter where one caller-specific handler context stores its
checkpointed and working frame values. `doneOutcome` is a total caller-owned
completion policy. It receives the exact terminal handler context, returned
Core value, and Core-local store before producing a frame outcome.

The adapter does not call `doneOutcome` for out-of-fuel or raw fault. It does
not turn either branch into `FrameOutcome.trapped`.

## Terminal context and local store

Both callbacks use `result.context`, never the starting handler context. A
storage write handled before completion is therefore present in the working
WorldState passed to frame resolution. Checkpoint state and effects remain the
ones retained in that same terminal context.

The local Core store is passed to `doneOutcome` because a returned `Core.Value`
may contain cell references. The policy must consume whatever semantic
information it needs before the adapter drops the local store. The adapter does
not merge local cells into WorldState, frame effects, or return bytes.

The policy may choose returned, reverted, or trapped for a completed Core value.
This parameterization is not an ABI, exception, or language-level return rule.
A policy-selected trap after Core completion is distinct from converting a raw
machine fault into a trap.

## Exact structural laws

Expose named laws for:

- exact reduction of done to `some`;
- exact reduction of out-of-fuel and raw fault to `none`;
- checkpoint state, checkpoint effects, working effects, and frame result
  projections of the constructed context; and
- total resolution when the caller policy selects returned, reverted, or
  trapped.

The resolved branches are exact:

- returned uses the terminal working WorldState, terminal working effects, and
  caller-supplied bytes;
- reverted uses the terminal checkpoint WorldState, checkpoint rollback state,
  terminal working trace, and caller-supplied bytes; and
- trapped retains exactly the caller-supplied reason.

These laws reuse the existing continuation-context construction and resolution
rules. They add no second lifecycle semantics.

## Checked storage specialization

For checked combined-storage execution, fix the projection to:

```lean
fun finalContext => finalContext.context.values
```

Expose two results:

```lean
theorem CheckedHostCoreProgram
    .runWithStorage_toFrameContinuationContext?_eq_none_iff ...
```

states that the adapter returns `none` exactly when the checked run returns an
out-of-fuel result. The existing no-fault theorem eliminates the raw-fault
branch.

```lean
theorem CheckedHostCoreProgram
    .runWithStorage_toFrameContinuationContext?_some_stable ...
```

states that a `some continuation` result remains that exact continuation under
additional fuel. It reuses done stability, including the exact terminal
context, value, and local store. There is no stability result for `none`.

## Address-selected wrapper

Connect the current highest-level internal entry point with:

```lean
def runCodeWithStorageContinuationContext? ... :
  Option (Option (FrameContinuationContext RollbackState TraceState TrapReason))
```

The implementation uses `Option.map`, not `bind`:

```lean
(context.runCodeWithStorage? codeAddress fuel).map fun result =>
  result.toFrameContinuationContext?
    (fun finalContext => finalContext.context.values) doneOutcome
```

The two optional layers are intentional:

- outer `none`: working-WorldState code lookup failed;
- `some none`: code was selected but checked execution ran out of fuel; and
- `some (some continuation)`: selected checked execution completed and the
  caller policy produced frame inputs.

Expose exact laws for all three boundaries. Outer failure is equivalent to the
existing `code? = none` observation. `some none` is equivalent to an exact
selected out-of-fuel driver result. `some (some continuation)` remains exact
under additional fuel.

Flattening the two layers would erase ADR-0122's distinction between selection
failure and incomplete execution, so no flattened helper is added.

## Required regressions

Compile-time consumers cover:

- all three generic result branches;
- exact terminal value/context/store delivery to the caller policy;
- the four continuation-context projections;
- exact returned, reverted, and trapped resolution;
- checked `none` iff out-of-fuel and completed adapter stability;
- selected outer `none`, selected `some none`, and completed
  `some (some continuation)` stability.

The existing address-selected read/write/read fixture supplies runtime coverage:

- fuel 22 has already handled the write but remains out of fuel, producing
  `some none` rather than selection failure;
- fuel 28 completes with `.word newValue` and local store `[.bool true]`;
- a policy returns bytes only when it observes that exact local store;
- returned resolution retains the terminal working storage update and working
  effects;
- reverted resolution selects checkpoint state and rollback but retains the
  terminal working trace;
- trapped resolution retains the policy-selected reason;
- fuel 64 produces the same completed nested result as fuel 28; and
- an address without code still produces outer `none`.

No fixture converts out-of-fuel or raw fault to a trap.

## Dependency boundary

The generic adapter depends on `HostDriverResult`, checkpointed working values,
and frame continuation construction. Its properties additionally reuse total
frame resolution. It is independent of storage, Address, Account, WorldState
operations, or a concrete handler.

The checked and selected lifts live in Semantics and reuse existing storage
driver safety, done stability, and code-selection completeness. Core imports no
frame or WorldState meaning.

No parser, Surface, ABI, Oracle, Wire, schema, profile, gas, or public runtime
module changes. The root README does not change.

## Non-goals

This ADR does not define:

- a canonical conversion from `Core.Value` and `Core.Store` to bytes;
- whether ordinary Core completion means return, revert, or trap;
- a mapping from raw machine faults or out-of-fuel to trap reasons;
- sufficient fuel, normalization, or retry policy;
- delivery to a parent frame, scheduling, nested invocation, or call depth;
- transaction commit, rollback ownership, or final observation;
- calldata, caller, call value, call kind, balance, or ABI; or
- publication in any frozen interface.

## Implementation sequence

Keep every green commit below roughly 300 changed lines:

1. record this done-only lifecycle boundary and its non-goals;
2. add the generic adapter and exact structural/resolution laws;
3. add checked and address-selected nested-option lifts;
4. add direct proof-interface consumers;
5. add returned/reverted/trapped and fuel-boundary runtime regressions; and
6. run full validation and independent audit, then synchronize acceptance
   evidence and current-facing internal documents.

## Consequences

Completed handled Core execution can enter the existing frame continuation and
resolution model without fixing ABI or language-level completion policy. The
adapter retains terminal speculative writes and all checkpoint/effect inputs,
while the caller consumes Core-local values and cells explicitly.

Selection failure, resource exhaustion, and completion remain distinct at the
highest-level internal entry point. Raw faults and out-of-fuel stay outside
frame outcomes until separate policies justify any interpretation.
