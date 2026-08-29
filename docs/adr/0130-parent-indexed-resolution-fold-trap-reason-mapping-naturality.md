# ADR-0130: Parent-indexed resolution-fold trap-reason mapping naturality

- Status: Accepted
- Decision date: 2026-08-29
- Scope: commute heterogeneous trap-reason mapping through the frame fold
- Implementation: Complete

## Context

ADR-0085 changes the trap-reason type of a completed parent-indexed context
without changing its parent index, checkpoints, state, journals, or trace
evidence. ADR-0129 adds a total fold that passes exact return, revert, or trap
values to caller-owned functions.

Unlike the older partial continuations, the new fold can observe a trapped
reason through `onTrapped`. Its result is therefore not simply invariant under
reason mapping. The correct relationship must map the reason before supplying
it to the trap function while leaving both non-trapping functions unchanged.

Without a public law, every caller must expose the dependent context mapper and
repeat the three outcome cases. This is a proof-interface gap only. Both the
mapper and fold are already complete runtime operations.

## Decision

Add no new operation. Publish exactly one simplification theorem:

```lean
namespace Solcore.Semantics.ParentIndexedFrameContinuationContext

universe u v w x y

@[simp] theorem foldResolutionWithTrapRollback_mapTrapReason
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x} {Next : Type y}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        Bytes → Next)
    (onTrapped :
      (WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) →
        MappedTrapReason → Next) :
    (context.mapTrapReason mapReason).foldResolutionWithTrapRollback
        onReturned onReverted onTrapped =
      context.foldResolutionWithTrapRollback
        onReturned onReverted
        (fun values reason => onTrapped values (mapReason reason))

end Solcore.Semantics.ParentIndexedFrameContinuationContext
```

The return and revert functions are identical on both sides. They receive the
same state, effects, trace, and bytes. Only the original trap function is
precomposed with `mapReason`, and it still receives the same exact parent
rollback pair.

`Next` is unchanged. The theorem maps neither the caller's result nor any
frame value other than the trapped reason supplied to `onTrapped`.

## Proof boundary

Expose the existing parent-indexed context, underlying frame result, and its
three outcome constructors. Each branch closes by definitional equality.

The proof may import the existing context-mapping definition and fold
definition. It must add no private or public helper, branch specialization,
mapper alias, fold variant, or result mapper.

The theorem must report exactly `[propext]`. It introduces no classical choice,
custom axiom, unchecked declaration, or runtime behavior.

## Simplification behavior

Orient the rule from folding a mapped context to folding the original context
with a composed trap function. This removes the outer context mapper and does
not recreate it.

Identity mapping has two possible reductions: simplify the mapped context
first, or move the identity function into `onTrapped` first. Both must reach the
original fold.

Two successive heterogeneous mappings also have two paths: compose the context
mappers first, or move them through the fold one at a time. Both must normalize
to a single trap function applying the two reason functions in order. Add no
reverse rule or branch-specific simp theorem.

## Required compile regressions

Add one compile-only test module and no runtime assertion. It must contain:

- one direct application of the exact heterogeneous theorem;
- one identity-mapping simplification to the original fold;
- one two-stage heterogeneous mapping example that converges to the composed
  trap function; and
- one commuting-square example combining ADR-0129 view reconstruction with
  ADR-0128 view-mapping naturality.

The commuting square starts with the mapped context's reconstruction callbacks
and ends with the original view's first component reason-mapped and its second
rollback component unchanged.

The runtime return, revert, and trap branches were executed by ADR-0129.
Parent-indexed reason mapping was covered by ADR-0085. Repeating either fixture
would not test a new operation.

## Dependency boundary

Use
`ParentIndexedFrameResolutionFoldTrapReasonMapProperties.lean` for the theorem
and `Solcore/Test/ParentIndexedFrameResolutionFoldTrapReasonMap.lean` for its
compile consumers.

The production theorem imports only the parent-indexed context reason mapper
and the fold definition. It does not require the fold branch laws, resolution
view, ADR-0125, selected execution, HostDriver, HostStorageDriver, or Core.

The compile consumer may additionally import ADR-0129 reconstruction and
ADR-0128 view naturality. The test runner adds one import and no runtime call.
The Semantics facade exports the theorem next to the fold properties.

## Non-goals

This ADR adds no:

- new mapper, fold, carrier, alias, coercion, instance, or `Functor`;
- mapping of `Next`, WorldState, rollback, trace, event, bytes, or parent index;
- reverse law, inverse, injectivity, surjectivity, fusion, or extensionality law;
- branch-specific mapped fold laws or duplicate identity/composition theorem;
- callback evaluation-count, cost, step, or exactly-once claim;
- `Option` wrapper or lift through ADR-0125's three optional layers;
- rollback application, trap catch, propagation, parent mutation, or resumption;
- stack, scheduler, nested invocation, root checkpoint, or transaction policy;
- caller, current address, call value, calldata, call kind, or authority role;
  or
- parser, Surface, ABI, gas, Wire, Oracle, schema, profile, or public format
  change.

## Implemented sequence

The work was completed in this order, with every green commit below roughly
300 changed lines:

1. record the exact proof-only contract;
2. activate it in current-facing internal documents;
3. add the single theorem and Semantics export;
4. add the four compile regressions and one runner import;
5. run trust, simp, axiom, dependency, build, test, metadata, kernel, and
   independent audits; and
6. synchronize completion evidence in current-facing internal documents.

## Implementation record

`ParentIndexedFrameResolutionFoldTrapReasonMapProperties.lean` publishes the
single heterogeneous naturality theorem and one Semantics-facade import. Its
proof exposes the existing parent-indexed context and frame outcome, then
closes return, revert, and trap by definitional equality. It adds no operation,
helper, branch specialization, alias, mapper, or result transformation.

`Solcore/Test/ParentIndexedFrameResolutionFoldTrapReasonMap.lean` contains the
four compile-only consumers required above. The test runner imports the module
without adding a runtime call. Production depends only on the existing
parent-indexed context reason mapper and fold definition; reconstruction and
resolution-view naturality remain test-only dependencies.

## Acceptance evidence

- the full build completed 638 jobs;
- the complete test suite completed 1,164 jobs;
- all changed Lean roots compiled with trust zero and warnings as errors;
- metadata and semantic-kernel policy checks passed;
- the single public simp theorem reports exactly `[propext]`;
- declaration and simplification inventories found exactly one theorem and no
  operation, helper, unchecked declaration, or reverse simp rule;
- production dependency inspection found only the context reason mapper and
  fold definition; and
- independent specification and implementation audits found no P0-P3 issue.

No Core execution, runtime fixture, parser, Surface, ABI, Oracle, Wire format,
schema, profile, or root README changed.

## Consequences

Callers can change a completed context's trap-reason type before or after
folding it, provided the original reason mapper is composed into the trap
function. All state, effects, trace, bytes, and rollback observations remain
unchanged.

This closes the mapping algebra introduced by ADR-0129 without adding runtime
policy. Parent execution and transaction finalization remain blocked on their
missing machine, checkpoint-lifetime, and persistence definitions.
