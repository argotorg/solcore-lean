# ADR-0079: Heterogeneous frame-run-result trap-reason mapping

- Status: Accepted
- Decision date: 2026-08-28
- Scope: working-state-preserving mapping of frame-run trap reasons
- Implementation: Complete

## Context

ADR-0078 lets callers change the trap-reason type of a `FrameOutcome` without
changing return or revert bytes. A `FrameRunResult` also contains the
speculative `WorldState` paired with that outcome. Callers currently have to
rebuild the result by hand whenever they translate its trap reason.

That reconstruction is small but semantically important: the working state
must be kept exactly, while only the outcome is delegated to ADR-0078. Naming
this lift removes repeated record construction without claiming that the state
is valid, resolved, committed, or produced by an actual nested invocation.

## Decision

Add exactly one public operation in a downstream module. Leave the original
ADR-0060 result API and the ADR-0078 outcome API unchanged:

```lean
namespace Solcore.Semantics.FrameRunResult

universe u v

def mapTrapReason
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (result : FrameRunResult TrapReason) :
    FrameRunResult MappedTrapReason :=
  ⟨result.working, result.outcome.mapTrapReason mapReason⟩

end Solcore.Semantics.FrameRunResult
```

The function argument comes first, matching ADR-0078. Generalized field
notation permits `result.mapTrapReason mapReason`.

The operation copies `result.working` unchanged and delegates the outcome to
`FrameOutcome.mapTrapReason`. The caller still owns the arbitrary pure mapper;
it may merge reasons or otherwise lose information. No validity condition or
canonical reason conversion is implied.

Do not add a `Functor` instance, generic `map` alias, coercion, default mapper,
payload mapper, or second executable operation. The generated definitional
equation is an intentional reduction artifact.

## Required proof interface

Publish exactly five simp laws:

```lean
namespace Solcore.Semantics.FrameRunResult

universe u v w

@[simp] theorem mapTrapReason_mk
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (working : WorldState) (outcome : FrameOutcome TrapReason) :
    mapTrapReason mapReason ⟨working, outcome⟩ =
      (⟨working, outcome.mapTrapReason mapReason⟩ :
        FrameRunResult MappedTrapReason)

@[simp] theorem working_mapTrapReason
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (result : FrameRunResult TrapReason) :
    (mapTrapReason mapReason result).working = result.working

@[simp] theorem outcome_mapTrapReason
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (result : FrameRunResult TrapReason) :
    (mapTrapReason mapReason result).outcome =
      result.outcome.mapTrapReason mapReason

@[simp] theorem mapTrapReason_id
    {TrapReason : Type u} (result : FrameRunResult TrapReason) :
    mapTrapReason (fun reason => reason) result = result

@[simp] theorem mapTrapReason_comp
    {TrapReason : Type u}
    {IntermediateTrapReason : Type v}
    {MappedTrapReason : Type w}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (result : FrameRunResult TrapReason) :
    mapTrapReason second (mapTrapReason first result) =
      mapTrapReason (fun reason => second (first reason)) result

end Solcore.Semantics.FrameRunResult
```

The constructor and two projection laws are `rfl`. The constructor law gives
concrete results a stable simp interface, while the projections serve abstract
results. Identity and composition reuse the corresponding ADR-0078 laws after
exposing the single result constructor. Composition is oriented only from two
mappings to one, so the simp surface has no reverse loop.

The operation, its generated equation, and all five laws must report exactly
`[propext]`. This existing dependency comes from the `WorldState` contained in
`FrameRunResult`; do not describe this slice as axiom-free. Add no branch-
specific result law, injectivity theorem, or observer theorem beyond the two
record projections.

## Required tests

Add exactly three runtime assertions importing the definition module only.
Use distinct source and target reason inductives with at least two constructors
each and a nonconstant mapper.

The return assertion observes one exact working-state storage value and one
exact nonempty return payload. The revert assertion uses a different working
state and a different exact nonempty revert payload. The trap assertion uses a
third working state and checks the exact mapped target constructor. These
witnesses detect an implementation that drops the state, changes bytes, or
maps the wrong reason.

Do not import or invoke the proof laws. Add no identity, composition,
projection, resolver, or payload assertion. Wire the test module and its test
function into the runner exactly once.

## Dependency boundary

`FrameRunResultTrapReasonMap.lean` imports `FrameRunResult` and the ADR-0078
definition module. `FrameRunResultTrapReasonMapProperties.lean` imports the new
definition module and the ADR-0078 properties needed by identity and
composition.

The test module imports only the new definition module. The definition and
properties imports sit after the existing `FrameRunResult` imports in the
semantic umbrella. Existing ADR-0060 and ADR-0078 definitions, properties, and
tests remain unchanged.

## What this mapping does not decide

Keeping a `WorldState` value does not prove that it is valid, reachable,
committed, checkpoint-related, or the result of one execution. This operation
does not call `resolvedWorldState?`, create a checkpoint, roll back state, or
map an effect journal, trace, continuation context, resolution result, or
ADR-0076 payload.

It does not propagate a trap, establish ancestry, execute or resume a parent,
classify reasons as fatal or recoverable, choose catch behavior, schedule a
frame, or decide transaction rollback or atomicity. The mapper need not be
injective, reversible, lossless, or semantically admissible.

It adds no parser or source syntax, Core fault adapter, resource-limit rule,
fuel or gas policy, Wire field, ABI, serialization, EVM revision,
opcode behavior, canonical delta, or published format.

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

Semantic layers can translate a complete frame result's trap-reason type
without manually rebuilding the record or changing its working state. The lift
inherits ADR-0078's branch behavior while keeping reason policy explicit.

Future payload or continuation integration can reuse this operation, but must
specify its own state, effect, trace, and runtime-propagation meaning in a
separate decision.

## Implementation record

The completed slice adds exactly one public `FrameRunResult.mapTrapReason`
operation in a 20-line downstream definition module plus one umbrella import.
The ADR-0060 and ADR-0078 definition, properties, and test modules remain
unchanged. The function is caller-supplied and function-first, supports
different source and target universes, keeps the exact working state, and
delegates only the outcome to ADR-0078.

A 57-line properties module plus one umbrella import publishes exactly five
simp laws: one constructor equation, two projections, identity, and
composition. Constructor consumers and abstract-result consumers both reduce
without unfolding the definition. Composition reduces two nested mappings to
one composed mapping, and the combined simp surface converges without a loop.
The operation, its one generated equation, and all five laws report exactly
`[propext]`.

An 83-line definition-only test module plus two runner lines contains exactly
three runtime assertions. Separate two-constructor source and target reason
types and a nonconstant mapper check exact return bytes, distinct exact revert
bytes, one exact mapped trap reason, and three different observed working-state
storage values without importing the proof laws.

The implementation commits are `d21219c` (235 changed lines), `24bae38` (21),
`92634b5` (58), and `4a06204` (85), all below 300 changed lines; this completion
update is the fifth staged commit. Focused and full builds, tests, trust-zero,
axiom, simp-termination, semantic-kernel, diff, and independent P0-P3
audits pass.

The lift remains a pure value transformation. It resolves no state, maps no
journal, trace, continuation, resolution result, or payload, and establishes
no runtime propagation, ancestry, handling, or transaction policy.
