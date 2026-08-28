# ADR-0080: Heterogeneous frame-resolution-result trap-reason mapping

- Status: Accepted
- Decision date: 2026-08-28
- Scope: caller-supplied pure mapping of total frame-resolution trap reasons
- Implementation: Complete

## Context

ADR-0068 defines `FrameResolutionResult`, the total first-order output of
resolving one completed frame. Its return and revert branches carry selected
state, effects, and bytes, while its trap branch carries a parametric reason.
A consumer cannot currently change that reason type without matching all three
constructors and manually copying every unrelated field.

ADR-0078 and ADR-0079 provide the corresponding pure conversion for
`FrameOutcome` and `FrameRunResult`. Resolution output needs the same narrow
capability, but it is a separate carrier with already-selected state and
effects. Its mapping must not rerun resolution or infer any rollback policy.

## Decision

Add exactly one public operation in a downstream module, leaving ADR-0068's
carrier and resolver unchanged:

```lean
namespace Solcore.Semantics.FrameResolutionResult

universe u v w x

def mapTrapReason
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (result :
      FrameResolutionResult RollbackState TraceState TrapReason) :
    FrameResolutionResult RollbackState TraceState MappedTrapReason :=
  match result with
  | .returned state effects data => .returned state effects data
  | .reverted state effects data => .reverted state effects data
  | .trapped reason => .trapped (mapReason reason)

end Solcore.Semantics.FrameResolutionResult
```

The mapper comes first, matching ADR-0078 and ADR-0079. Generalized field
notation permits `result.mapTrapReason mapReason`.

Returned and reverted results preserve the exact selected `WorldState`, effect
journal, and byte payload. A trapped result applies the caller's function
exactly once to its reason. The rollback and trace-state types do not change.

The mapper may be lossy. Add no admissibility requirement, canonical
conversion, default mapper, coercion, `Functor` instance, generic `map` alias,
effect mapper, or second operation. The generated definitional equations are
intentional reduction artifacts.

## Required proof interface

Publish exactly five simp laws:

```lean
namespace Solcore.Semantics.FrameResolutionResult

universe u v w x y

@[simp] theorem mapTrapReason_returned
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (state : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    mapTrapReason mapReason
        (FrameResolutionResult.returned
          (TrapReason := TrapReason) state effects data) =
      FrameResolutionResult.returned
        (TrapReason := MappedTrapReason) state effects data

@[simp] theorem mapTrapReason_reverted
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (state : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (data : Bytes) :
    mapTrapReason mapReason
        (FrameResolutionResult.reverted
          (TrapReason := TrapReason) state effects data) =
      FrameResolutionResult.reverted
        (TrapReason := MappedTrapReason) state effects data

@[simp] theorem mapTrapReason_trapped
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (reason : TrapReason) :
    mapTrapReason mapReason
        (FrameResolutionResult.trapped
          (RollbackState := RollbackState) (TraceState := TraceState) reason) =
      FrameResolutionResult.trapped (mapReason reason)

@[simp] theorem mapTrapReason_id
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w}
    (result : FrameResolutionResult RollbackState TraceState TrapReason) :
    mapTrapReason (fun reason => reason) result = result

@[simp] theorem mapTrapReason_comp
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {IntermediateTrapReason : Type x}
    {MappedTrapReason : Type y}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (result : FrameResolutionResult RollbackState TraceState TrapReason) :
    mapTrapReason second (mapTrapReason first result) =
      mapTrapReason (fun reason => second (first reason)) result

end Solcore.Semantics.FrameResolutionResult
```

The constructor laws are `rfl`; identity and composition use one constructor
case split. Composition is oriented only from two mappings to one composed
mapping, so simplification decreases the number of map operations and cannot
loop with these laws.

The operation, its three generated equations, and all five laws must report
exactly `[propext]`, inherited through the state and journal-bearing carrier.
Do not describe this slice as axiom-free. Add no projection, injectivity,
surjectivity, equivalence, observer, or resolve-coherence theorem.

## Required tests

Add exactly three runtime assertions importing the definition module only.
Use different two-constructor source and target reason types and a nonconstant
mapper.

The return assertion must observe one exact state storage value, exact rollback
and trace values, and one exact nonempty byte payload. The revert assertion
must use different state, effect, and exact nonempty byte values. The trap
assertion must map one concrete source reason to the exact target constructor.

Do not import or invoke the proof laws. Add no identity, composition,
continuation, resolver, context, or payload assertion. Wire the test module and
its test function into the runner exactly once.

## Dependency boundary

`FrameResolutionResultTrapReasonMap.lean` imports only the existing
`FrameResolutionResult` module. Its properties module imports only the new
definition module. The two imports sit directly after the existing
`FrameResolutionResult` imports in the semantic umbrella.

The test module imports only the new definition module. Existing ADR-0068,
ADR-0078, and ADR-0079 definition, properties, and test modules remain
unchanged.

## What this mapping does not decide

The operation transforms an already-constructed value. It does not run
`FrameContinuationContext.resolve`, select state or effects, create or compare
checkpoints, roll back state, append a trace, invoke a continuation, or map a
continuation context, parent-indexed context, or propagation payload.

It does not propagate or handle a trap, establish ancestry, execute or resume
a parent, classify reasons as fatal or recoverable, schedule a frame, or decide
transaction rollback or atomicity. It proves no naturality law between mapping
and resolution; that is a separate possible slice.

It adds no parser or source syntax, Core fault adapter, resource-limit rule,
fuel or gas policy, Wire or Oracle field, ABI, serialization, EVM revision,
opcode behavior, Profile, canonical delta, or published format.

## Staged implementation plan

Keep each of five commits below 300 changed lines: this decision and internal
roadmap update; the exact operation and umbrella import; the exact five simp
laws and umbrella import; the exact three definition-only runtime assertions
and runner wiring; independent audit and completion evidence.

## Publication and exclusions

This internal mapping operation is not published. It adds no balance, code,
call data, transferred value, host call/create behavior, storage layout,
concrete log rule, frozen artifact, or public format.

## Consequences

Consumers can translate a total resolution result's trap-reason type without
reimplementing its three branches or changing selected state, effects, or
bytes. Reason policy remains explicit and caller-owned.

Future context mapping or resolve-coherence work can build on this operation,
but must specify its own boundary in a separate decision.

## Implementation record

The completed slice adds exactly one public
`FrameResolutionResult.mapTrapReason` operation in a 24-line downstream
definition module plus one umbrella import. The ADR-0068, ADR-0078, and
ADR-0079 definition, properties, and test modules remain unchanged. The mapper
is function-first, supports different source and target universes, preserves
exact return/revert state, effects, and bytes, and changes only trapped reasons.

A 68-line properties module plus one umbrella import publishes exactly five
simp laws: three constructor equations, identity, and composition. Composition
reduces two nested mappings to one composed mapping; no reverse equation is
present. The operation, its three generated equations, and all five laws report
exactly `[propext]`, and the combined simp surface terminates at constructor
normal forms.

A 92-line definition-only test module plus two runner lines contains exactly
three runtime assertions. Separate two-constructor source and target reason
types and a nonconstant mapper verify distinct return/revert state storage,
rollback and trace values, exact nonempty byte payloads, and one exact mapped
trap reason without importing the laws.

The implementation commits are `857d567` (249 changed lines), `8fa78a2` (25),
`b9d11fa` (69), and `0759da1` (94), all below 300 changed lines; this completion
update is the fifth staged commit. Focused and full builds, tests, trust-zero,
axiom, simp-termination, semantic-kernel, metadata, diff, and independent P0-P3
audits pass.

The mapper remains a pure transformation of an already-resolved value. It
reruns no resolver, maps no continuation context or payload, and establishes
no rollback, propagation, ancestry, handling, or transaction policy.
