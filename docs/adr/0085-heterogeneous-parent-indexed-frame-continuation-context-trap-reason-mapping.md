# ADR-0085: Heterogeneous parent-indexed continuation-context reason mapping

- Status: Accepted
- Decision date: 2026-08-28
- Scope: parent-index-preserving lift of refined context reason mapping
- Implementation: Not started

## Context

ADR-0073 adds a fixed `parentWorking` type index and proof that a completed
context's checkpoints equal that pair. ADR-0084 maps the reason type of its
immediate trace-prefix context while preserving every field and prefix proof.
The parent-indexed carrier still lacks the corresponding canonical lift.

Manual reconstruction would repeat both the refined mapping and dependent
checkpoint-equality transport. The lift should keep the exact parent index and
reuse its existing proof term without mapping parent state, effects, or trace.

This adapter closes the mapping surface on the current final context carrier.
It is not itself a nested-runtime transition or a prerequisite claim about how
such a runtime must be designed.

## Decision

Add exactly one function-first public operation:

```lean
namespace Solcore.Semantics.ParentIndexedFrameContinuationContext

universe u v w x

def mapTrapReason
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    ParentIndexedFrameContinuationContext
      RollbackState Event MappedTrapReason parentWorking :=
  {
    toFrameContinuationContextWithTracePrefix :=
      context.toFrameContinuationContextWithTracePrefix.mapTrapReason mapReason
    checkpoint_eq_parentWorking := context.checkpoint_eq_parentWorking
  }

end Solcore.Semantics.ParentIndexedFrameContinuationContext
```

The refined context delegates to ADR-0084. Because that mapper preserves the
state and effect checkpoints definitionally, the original
`checkpoint_eq_parentWorking` term already has the required target type. Add no
cast, index rewrite, equality transport, proof helper, or replacement proof.

The mapper may be lossy. `parentWorking`, rollback, and event types remain
unchanged. The operation and its generated equation must report exactly
`[propext]`. Add no generic `map` alias, coercion, `Functor` instance, default
mapper, second operation, or validity condition.

## Required proof interface

Publish exactly four simp laws:

```lean
namespace Solcore.Semantics.ParentIndexedFrameContinuationContext

universe u v w x y

@[simp] theorem mapTrapReason_mk
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context :
      FrameContinuationContextWithTracePrefix
        RollbackState Event TrapReason)
    (checkpointEq :
      (context.stateCheckpoint, context.effectCheckpoint) = parentWorking) :
    mapTrapReason mapReason
        (⟨context, checkpointEq⟩ :
          ParentIndexedFrameContinuationContext
            RollbackState Event TrapReason parentWorking) =
      (⟨context.mapTrapReason mapReason, checkpointEq⟩ :
        ParentIndexedFrameContinuationContext
          RollbackState Event MappedTrapReason parentWorking)

@[simp] theorem toFrameContinuationContextWithTracePrefix_mapTrapReason
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (mapReason : TrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    (mapTrapReason mapReason context).toFrameContinuationContextWithTracePrefix =
      context.toFrameContinuationContextWithTracePrefix.mapTrapReason mapReason

@[simp] theorem mapTrapReason_id
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    mapTrapReason (fun reason => reason) context = context

@[simp] theorem mapTrapReason_comp
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {IntermediateTrapReason : Type y}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (context : ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking) :
    mapTrapReason second (mapTrapReason first context) =
      mapTrapReason (fun reason => second (first reason)) context

end Solcore.Semantics.ParentIndexedFrameContinuationContext
```

The constructor law maps the trace-prefix context and reuses the same
`checkpointEq`. The projection law is `rfl`. Identity and composition expose
the parent-indexed constructor and reuse ADR-0084's laws. All critical paths
converge on the same dependent-record normal form; no reverse rule is added.

The operation, its generated equation, and all four laws must report exactly
`[propext]`. Add no checkpoint-proof equality law, inherited projection
duplicates, `parentWorking_tracePrefix` duplicate, branch law, extensionality
theorem, resolve/continue law, or construction-commutation law.

## Required compile regressions

Add exactly three private compile examples and no runtime assertion or test
function. Import the new definition module only; do not consume the four laws.

Use distinct two-constructor source and target reason types, a nonconstant
mapper, nonempty parent and nested traces, and distinct parent and nested state
and journal values. Cover:

1. an abstract whole-constructor equation mapping the trace-prefix context
   while reusing the exact supplied checkpoint equality, closed by `rfl`;
2. recovery from a mapped value of evidence for the original context's exact
   `(stateCheckpoint, effectCheckpoint) = parentWorking` proposition; and
3. a concrete trapped fixture whose complete trace-prefix context projection
   is definitionally equal to the expected preserved fields, working state,
   prefix evidence, and mapped reason, with `parentWorking` fixed by its type.

Add the test module to the runner imports exactly once and add no runtime call.
Return/revert/trap resolution and ADR-0084's wrapper mapping are already tested
and must not be duplicated here.

## Dependency boundary

`ParentIndexedFrameContinuationContextTrapReasonMap.lean` imports exactly the
ADR-0073 carrier and ADR-0084 definition modules. Its properties module imports
exactly the new definition and ADR-0084 properties modules. In the semantic
umbrella, both follow the existing parent-indexed carrier properties and
precede parent-indexed construction.

The compile-regression module imports only the new definition module. Existing
ADR-0073, ADR-0074, and ADR-0084 definition, properties, and tests remain
unchanged.

## What this mapping does not decide

The operation does not map or replace `parentWorking`, its type index, state,
effects, traces, rollback values, prefix evidence, or checkpoint equality. It
does not create or validate checkpoints or strengthen either proof into runtime
provenance.

It does not resolve or continue a frame, select rollback, construct or map a
propagation payload, propagate or handle a trap, schedule execution, or decide
transaction rollback or atomicity.

It adds no parser or source syntax, Core fault adapter, resource-limit rule,
fuel or gas policy, Wire or Oracle field, ABI, serialization, EVM revision,
opcode behavior, Profile, canonical delta, or published format.

## Staged implementation plan

Keep each of five commits below 300 changed lines: this decision and internal
roadmap update; the exact one operation and umbrella import; the exact four
simp laws and umbrella import; the exact three definition-only compile
regressions and one runner import; independent audit and completion evidence.

## Publication and exclusions

This internal mapping is not published. It adds no balance, code, call data,
transferred value, host call/create behavior, storage layout, concrete log
rule, frozen artifact, or public format.

## Consequences

Consumers can change the reason type of a parent-indexed context without
rebuilding its trace-prefix refinement, parent index, or checkpoint equality.

Proof-only rollback invariance or propagation-payload naturality can now be
considered separately. Neither law nor nested execution behavior is selected
by this decision.
