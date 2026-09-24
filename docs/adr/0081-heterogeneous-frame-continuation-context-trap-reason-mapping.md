# ADR-0081: Heterogeneous frame-continuation-context trap-reason mapping

- Status: Accepted
- Decision date: 2026-08-28
- Scope: checkpoint-preserving lift of frame-run trap-reason mapping
- Implementation: Complete

## Context

ADR-0067 groups the caller-owned inputs for one completed frame in a
`FrameContinuationContext`. ADR-0079 can change the trap-reason type inside its
`FrameRunResult`, but callers still have to rebuild the surrounding context and
copy both effect snapshots and the state checkpoint by hand.

That reconstruction should have one canonical pure operation. It must preserve
all caller-owned checkpoint and working inputs exactly and delegate only the
result field to ADR-0079. It must not invoke a continuation or resolver.

## Decision

Add exactly one public operation in a downstream module, leaving ADR-0067 and
ADR-0079 unchanged:

```lean
namespace Solcore.Semantics.FrameContinuationContext

universe u v w x

def mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context :
      FrameContinuationContext RollbackState TraceState TrapReason) :
    FrameContinuationContext RollbackState TraceState MappedTrapReason :=
  {
    stateCheckpoint := context.stateCheckpoint
    effectCheckpoint := context.effectCheckpoint
    effectWorking := context.effectWorking
    result := context.result.mapTrapReason mapReason
  }

end Solcore.Semantics.FrameContinuationContext
```

The mapper comes first, matching ADR-0078 through ADR-0080. Generalized field
notation permits `context.mapTrapReason mapReason`.

The state checkpoint, effect checkpoint, and working effects are copied
unchanged. Only `context.result` is delegated to
`FrameRunResult.mapTrapReason`, which preserves its working state and
return/revert bytes. The rollback and trace-state types do not change.

The caller's mapper may be lossy. Add no validity requirement, default mapper,
coercion, `Functor` instance, generic `map` alias, context subtype, or second
operation. The generated definitional equation is intentional.

## Required proof interface

Publish exactly seven simp laws:

```lean
namespace Solcore.Semantics.FrameContinuationContext

universe u v w x y

variable {RollbackState : Type u} {TraceState : Type v}
variable {TrapReason : Type w} {MappedTrapReason : Type x}

@[simp] theorem mapTrapReason_mk
    (mapReason : TrapReason → MappedTrapReason)
    (stateCheckpoint : WorldState)
    (effectCheckpoint effectWorking :
      FrameEffectJournal RollbackState TraceState)
    (result : FrameRunResult TrapReason) :
    mapTrapReason mapReason
        (⟨stateCheckpoint, effectCheckpoint, effectWorking, result⟩ :
          FrameContinuationContext RollbackState TraceState TrapReason) =
      (⟨stateCheckpoint, effectCheckpoint, effectWorking,
        result.mapTrapReason mapReason⟩ :
          FrameContinuationContext RollbackState TraceState MappedTrapReason)

@[simp] theorem stateCheckpoint_mapTrapReason
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    (mapTrapReason mapReason context).stateCheckpoint =
      context.stateCheckpoint

@[simp] theorem effectCheckpoint_mapTrapReason
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    (mapTrapReason mapReason context).effectCheckpoint =
      context.effectCheckpoint

@[simp] theorem effectWorking_mapTrapReason
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    (mapTrapReason mapReason context).effectWorking = context.effectWorking

@[simp] theorem result_mapTrapReason
    (mapReason : TrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    (mapTrapReason mapReason context).result =
      context.result.mapTrapReason mapReason

@[simp] theorem mapTrapReason_id
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    mapTrapReason (fun reason => reason) context = context

@[simp] theorem mapTrapReason_comp
    {IntermediateTrapReason : Type y}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (context : FrameContinuationContext RollbackState TraceState TrapReason) :
    mapTrapReason second (mapTrapReason first context) =
      mapTrapReason (fun reason => second (first reason)) context

end Solcore.Semantics.FrameContinuationContext
```

The constructor and four projection laws are `rfl`. The constructor law gives
concrete contexts a stable simp interface, while the projections serve
abstract contexts. Identity and composition expose the single context
constructor and reuse ADR-0079's corresponding laws.

Composition is oriented only from two context mappings to one composed
mapping. Constructor, projection, identity, and composition rewriting converge
to the same record normal forms without a loop.

The operation, its generated equation, and all seven laws must report exactly
`[propext]`. Add no branch-specific context law, extensionality theorem,
observer, injectivity theorem, or continuation/resolution coherence law.

## Required tests

Add exactly three runtime assertions importing the definition module only.
Use distinct two-constructor source and target reason types and a nonconstant
mapper. Build returned, reverted, and trapped contexts with different concrete
values for all four context fields.

Each assertion must observe the exact state checkpoint, effect checkpoint,
working effects, and result working state. Return and revert additionally check
different exact nonempty byte payloads; trap checks the exact mapped target
reason. These witnesses detect dropped or exchanged fields as well as incorrect
reason mapping.

Do not import or invoke the proof laws. Add no identity, composition,
`continue?`, `resolve`, parent-indexed context, or payload assertion. Wire the
test module and function into the runner exactly once.

## Dependency boundary

`FrameContinuationContextTrapReasonMap.lean` imports the existing context and
ADR-0079 definition modules. Its properties module imports the new definition
and ADR-0079 properties. The imports sit after the existing
`FrameContinuationContext` imports in the semantic umbrella.

The test module imports only the new definition module. Existing ADR-0067,
ADR-0079, and ADR-0080 definition, properties, and test modules remain
unchanged.

## What this mapping does not decide

The operation does not call `continue?` or `resolve`, select resolved state or
effects, create or validate checkpoints, roll back state, append a trace, or
map a trace-prefixed, parent-indexed, or propagation payload context.

It establishes no naturality or behavior-preservation theorem for continuation
or resolution; those are separate proof boundaries. It does not propagate or
handle a trap, establish ancestry, execute or resume a parent, classify
reasons, schedule a frame, or decide transaction rollback or atomicity.

It adds no parser or source syntax, Core fault adapter, resource-limit rule,
fuel or gas policy, Wire field, ABI, serialization, EVM revision,
opcode behavior, canonical delta, or published format.

## Staged implementation plan

Keep each of five commits below 300 changed lines: this decision and internal
roadmap update; the exact operation and umbrella import; the exact seven simp
laws and umbrella import; the exact three definition-only runtime assertions
and runner wiring; independent audit and completion evidence.

## Publication and exclusions

This internal mapping operation is not published. It adds no balance, code,
call data, transferred value, host call/create behavior, storage layout,
concrete log rule, frozen artifact, or public format.

## Consequences

Consumers can translate a continuation context's trap-reason type without
manually rebuilding its four fields. Checkpoint and working inputs remain
exactly caller-owned values.

ADR-0082 fixes resolve naturality using the canonical context and
resolution-result mappings, without adding another executable operation.
ADR-0084 lifts this mapping to the ADR-0071 trace-prefix refinement while
reusing its existing proof evidence.

## Implementation record

The completed slice adds exactly one public
`FrameContinuationContext.mapTrapReason` operation in a 27-line downstream
definition module plus one umbrella import. The ADR-0067 and ADR-0079
definition, properties, and test modules remain unchanged. The mapper is
function-first, supports different reason universes, preserves the three
caller-owned context inputs, and delegates only the result field to ADR-0079.

An 87-line properties module plus one umbrella import publishes exactly seven
simp laws: one constructor equation, four projections, identity, and
composition. Concrete and abstract contexts both simplify without unfolding
the definition. Composition reduces two nested mappings to one composed
mapping. The operation, its generated equation, and all seven laws report
exactly `[propext]`, and the combined simp surface terminates at record normal
forms.

A 118-line definition-only test module plus two runner lines contains exactly
three runtime assertions. Returned, reverted, and trapped contexts use
different state checkpoints, effect checkpoints, working effects, and result
working states. The tests also verify distinct exact nonempty return/revert
bytes and one exact mapped trap reason without importing the laws.

The implementation commits are `8c26b3a` (250 changed lines), `43ef3c8` (32),
`4b598ee` (88), and `96577a1` (120), all below 300 changed lines; this completion
update is the fifth staged commit. The definition-stage commit also aligns the
documented composition binder with the shared `MappedTrapReason` API name.
Focused and full builds, tests, trust-zero, axiom, simp-termination,
semantic-kernel, diff, and independent P0-P3 audits pass.

The lift remains a pure record transformation. It invokes no continuation or
resolver, maps no indexed context or payload, and establishes no rollback,
propagation, ancestry, handling, or transaction policy.
