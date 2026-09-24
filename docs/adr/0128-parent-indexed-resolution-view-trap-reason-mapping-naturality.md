# ADR-0128: Parent-indexed resolution-view trap-reason mapping naturality

- Status: Accepted
- Decision date: 2026-08-29
- Scope: prove that reason mapping commutes with the parent-indexed resolution view
- Implementation: Complete

## Context

The internal frame layer already supports heterogeneous trap-reason mapping at
each relevant value boundary.

`ParentIndexedFrameContinuationContext.mapTrapReason` changes only the reason
type inside a completed parent-indexed context. It retains the exact parent
index, checkpoint equality, WorldState, effect journals, and trace-prefix
evidence.

`FrameResolutionResult.mapTrapReason` changes only a trapped reason in the
ordinary total resolution result. Return and revert state, effects, and bytes
remain unchanged.

ADR-0127 now adds `resolveWithTrapRollback`, whose first component is that
ordinary resolution and whose second component is the optional exact rollback
pair selected only on a trap. The repository has not yet proved how this new
view behaves when its input context's reason type is mapped.

Without a public naturality law, a downstream consumer must unfold both the
view and the dependent parent-indexed mapper, then repeat the fact that reason
mapping cannot alter rollback selection. This is a proof-interface gap, not a
runtime-semantics gap.

## Decision

Add no new value operation. Publish exactly one proof-only simplification law:

```lean
namespace Solcore.Semantics.ParentIndexedFrameContinuationContext

universe u v w x

@[simp] theorem resolveWithTrapRollback_mapTrapReason
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    (context.mapTrapReason mapReason).resolveWithTrapRollback =
      (FrameResolutionResult.mapTrapReason mapReason
          (context.resolveWithTrapRollback).1,
        (context.resolveWithTrapRollback).2)

end Solcore.Semantics.ParentIndexedFrameContinuationContext
```

The equality has two deliberately different components.

- The first component maps the ordinary resolution result. Consequently,
  return and revert values are identical while a trapped reason is mapped.
- The second component is exactly the original optional rollback selection.
  Parent state, parent rollback, accumulated working trace, and the distinction
  between selection and non-selection are unchanged.

The mapper may be non-injective or discard all reason information. No inverse,
injectivity, or recoverability premise is required because rollback selection
depends only on whether the outcome is trapped, not on the reason's identity.

## Proof boundary

The proof separates the product components.

For the first component, reuse the existing
`FrameContinuationContext.resolve_mapTrapReason` naturality theorem. For the
second component, reduce the parent-indexed context and inspect the existing
return, revert, and trap outcomes. Do not introduce a public rollback-mapping
helper, projection law, pair mapper, or second theorem.

The theorem and its generated declaration metadata must report exactly
`[propext]`. It must contain no `sorry`, custom axiom, classical choice,
unchecked declaration, or new runtime definition.

The rewrite direction is fixed from resolving a mapped context to a mapped
first component plus unchanged second component. Add no reverse simplification
rule.

## Simplification behavior

The theorem is a simplification rule because it removes a mapper from the
larger parent-indexed view and exposes existing smaller mapping operations.
The right-hand side cannot recreate its left-hand side.

Two existing simplification paths overlap intentionally:

1. map two context reason functions and apply this theorem twice; or
2. compose the context mappers first and apply this theorem once.

Both paths must normalize to one `FrameResolutionResult.mapTrapReason` using
the composed function and the unchanged rollback component. Identity mapping
must normalize to the original view. Compile regressions must check both
critical pairs rather than relying only on informal termination reasoning.

## Required regressions

Add a compile-only consumer module and no runtime assertion. It must:

- apply the new whole-product equality directly for one heterogeneous mapper;
- use two heterogeneous mappers to show that nested mapping and composed
  mapping simplify to the same exact view;
- show that identity mapping simplifies to the original view; and
- combine the new theorem with the existing bytes-aware continuation mapping
  law, proving that the first component's partial callback result and the
  second rollback component are both unchanged.

The examples may use abstract contexts and mapper functions. Runtime fixtures
would duplicate already executed branch behavior: ADR-0127 covers all three
view shapes, ADR-0080 covers result reason mapping, ADR-0085 covers
parent-indexed context mapping, and ADR-0091 covers bytes-aware continuation
invariance.

## Dependency boundary

Use
`ParentIndexedFrameResolutionViewTrapReasonMapProperties.lean` for the single
law and `Solcore/Test/ParentIndexedFrameResolutionViewTrapReasonMap.lean` for
compile consumers.

The production properties module may import the ADR-0127 view, the existing
parent-indexed context mapping properties, and the existing ordinary resolver
mapping naturality. It must not import selected execution, ADR-0125 coherence,
HostDriver, HostStorageDriver, or Core execution.

The compile consumer may additionally import the existing bytes-aware
continuation mapping law. The test runner adds one import and no runtime call.

The Semantics facade re-exports the new properties module next to the ADR-0127
view properties. Core receives no dependency on the frame layer.

## Non-goals

This ADR adds no:

- mapper operation, pair carrier, alias, coercion, type class, or `Functor`;
- map of WorldState, rollback, trace, event, bytes, or the parent type index;
- mapper evaluation-count, cost, injectivity, surjectivity, or inverse claim;
- trap classification, catch, recovery, propagation, or rollback application;
- callback dispatcher, parent resumption, byte delivery, stack, or scheduler;
- checkpoint creation, ownership, lifetime, provenance, or root identity;
- transaction commit, atomicity, persistence, or final observation boundary;
- conversion of storage absence, code absence, out-of-fuel, or raw faults into
  frame outcomes;
- lift across ADR-0125's three optional result layers;
- caller, current address, call value, calldata, call kind, or authority role;
  or
- parser, source syntax, ABI, gas, Wire, schema, profile, or public
  format change.

## Implemented sequence

The work was completed in this order:

1. record and activate the exact proof-only contract;
2. add the single naturality theorem and Semantics export;
3. add the direct, composition, identity, and continuation compile regressions;
   and
4. run full validation and independent audit, then synchronize completion
   evidence in current-facing internal documents.

## Implementation record

`ParentIndexedFrameResolutionViewTrapReasonMapProperties.lean` publishes the
single specified simp theorem and one Semantics-facade import. Its first
component proof directly reuses ordinary frame-resolution naturality. Its
second component inspects the three existing outcome constructors and proves
that optional rollback selection is exactly unchanged.

The compile-only consumer applies the whole-product theorem directly, checks
identity and two-stage heterogeneous composition, and combines it with the
existing bytes-aware continuation mapping law. The last example observes the
callback result and rollback component together, preventing either projection
from silently drifting.

## Acceptance evidence

- the full build completed 632 jobs;
- the complete test suite completed 1,152 jobs and all runtime checks passed;
- every changed Lean module compiled with trust zero and warnings as errors;
- the semantic-kernel policy check passed;
- the only new public theorem reports exactly `[propext]`;
- declaration and simplification inventories found exactly one new simp law
  and no runtime definition or unchecked declaration; and
- independent specification and implementation audits found no P0-P3 issue.

No Core execution, parser, source syntax, ABI, Wire format, schema, profile,
or root README changed.

## Consequences

Consumers can map the trap-reason type before or after observing a completed
parent-indexed frame. Only the reason inside the first component changes; the
exact optional rollback pair does not.

This closes the mapping algebra opened by ADR-0127 without adding runtime
behavior. A separate future decision may add a caller-owned three-branch fold
over the view, but it must still avoid parent mutation, rollback application,
or transaction-finalization claims.
