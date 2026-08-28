# ADR-0078: Heterogeneous frame-outcome trap-reason mapping

- Status: Accepted
- Decision date: 2026-08-28
- Scope: caller-supplied pure mapping of frame trap reasons
- Implementation: Complete

## Context

`FrameOutcome TrapReason` deliberately keeps the trap-reason type parametric.
That lets different semantic layers use different reason vocabularies, but the
current API cannot change the reason type while preserving returned and
reverted byte payloads.

ADR-0076 and ADR-0077 use one reason type on both sides of their prospective
payload boundary and explicitly leave heterogeneous reason conversion open.
The reusable solution belongs below those payload APIs, directly on
`FrameOutcome`. It must not invent a canonical reason taxonomy or imply that a
runtime propagation step occurred.

## Decision

Add exactly one public operation in a downstream module, leaving the original
ADR-0052 files unchanged:

```lean
namespace Solcore.Semantics.FrameOutcome

universe u v

def mapTrapReason
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (outcome : FrameOutcome TrapReason) :
    FrameOutcome MappedTrapReason :=
  match outcome with
  | .returned data => .returned data
  | .reverted data => .reverted data
  | .trapped reason => .trapped (mapReason reason)

end Solcore.Semantics.FrameOutcome
```

The function argument comes first, following the repository's and Lean's
ordinary `map` convention. Generalized field notation still permits
`outcome.mapTrapReason mapReason`.

The caller supplies an arbitrary pure function. Returned and reverted outcomes
keep their exact byte payload and only change the phantom reason parameter. A
trapped outcome applies the function exactly once to its reason.

Do not add a `Functor` instance, generic `map` alias, coercion, default mapper,
canonical mapper, relation between reason types, or second executable operation.
The generated definitional equations are intentional reduction artifacts.

This downstream operation narrowly fills the heterogeneous reason-mapping gap
left open by ADR-0076 and ADR-0077. It imports neither payload layer and changes
none of their APIs or claims.

## Required proof interface

Publish exactly five simp laws:

```lean
namespace Solcore.Semantics.FrameOutcome

universe u v w

@[simp] theorem mapTrapReason_returned
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason) (data : Bytes) :
    mapTrapReason mapReason
        (FrameOutcome.returned (TrapReason := TrapReason) data) =
      FrameOutcome.returned (TrapReason := MappedTrapReason) data

@[simp] theorem mapTrapReason_reverted
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason) (data : Bytes) :
    mapTrapReason mapReason
        (FrameOutcome.reverted (TrapReason := TrapReason) data) =
      FrameOutcome.reverted (TrapReason := MappedTrapReason) data

@[simp] theorem mapTrapReason_trapped
    {TrapReason : Type u} {MappedTrapReason : Type v}
    (mapReason : TrapReason → MappedTrapReason)
    (reason : TrapReason) :
    mapTrapReason mapReason (FrameOutcome.trapped reason) =
      FrameOutcome.trapped (mapReason reason)

@[simp] theorem mapTrapReason_id
    {TrapReason : Type u} (outcome : FrameOutcome TrapReason) :
    mapTrapReason (fun reason => reason) outcome = outcome

@[simp] theorem mapTrapReason_comp
    {TrapReason : Type u}
    {IntermediateTrapReason : Type v}
    {MappedTrapReason : Type w}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (outcome : FrameOutcome TrapReason) :
    mapTrapReason second (mapTrapReason first outcome) =
      mapTrapReason (fun reason => second (first reason)) outcome

end Solcore.Semantics.FrameOutcome
```

The three constructor laws are `rfl`. Identity and composition use
`cases outcome <;> rfl`. Composition is oriented only from two nested mappings
to one composed mapping, strictly reducing the number of map calls. Add no
reverse equation. Constructor, identity, and composition simplification all
converge to the same constructor normal forms without a loop.

The operation, its generated equations, and all five laws must be axiom-free.
Add no kind, return-data, revert-data, trap-reason observer, injectivity,
surjectivity, equivalence, admissibility, or losslessness theorem. The five laws
fully cover this slice; further consumer-specific coherence remains separate.

## Required tests

Add exactly three runtime assertions importing the definition module only.
Use distinct source and mapped reason inductives, each with at least two
constructors, and a nonconstant caller-supplied mapper.

The return assertion must observe the mapped outcome type with one exact
nonempty byte payload. The revert assertion must observe a different exact
nonempty byte payload. The trap assertion must map one concrete source reason
to the exact expected constructor of the different target type.

Do not import or invoke the five proof laws. Add no identity, composition,
observer, constant-mapper, or payload-level assertion. Wire the test module into
the runner exactly once and call its test function exactly once.

## Dependency boundary

`FrameOutcomeTrapReasonMap.lean` imports only the existing `FrameOutcome`
definition. `FrameOutcomeTrapReasonMapProperties.lean` imports only the new
definition module. The definition and properties imports sit together beside
the existing FrameOutcome imports in the semantic umbrella.

The test module imports only the new definition module. Existing
`FrameOutcome.lean`, `FrameOutcomeProperties.lean`, and their tests remain
unchanged, preserving ADR-0052's recorded surface exactly.

## What this mapping does not decide

The mapper need not be injective, surjective, reversible, lossless, or
semantically admissible. The operation does not choose the function, classify
reasons as fatal or recoverable, define catch or resume behavior, or introduce
a reason taxonomy.

It does not map `FrameRunResult`, a continuation context, state, effects,
rollback, traces, or an ADR-0076 payload. It does not prove cross-frame ancestry
or runtime propagation, execute a parent, create a checkpoint, schedule a
frame, repeat through ancestors, or decide transaction rollback or atomicity.

It also adds no parser or source syntax, Core fault adapter, resource-limit
rule, fuel or gas policy, Wire or Oracle field, ABI, serialization, EVM
revision, opcode behavior, Profile, canonical delta, or published format.

## Staged implementation plan

Keep each of five commits below 300 changed lines: this decision and internal
roadmap update; the exact one operation and umbrella import; the exact five simp
laws and umbrella import; the exact three definition-only runtime assertions
and runner wiring; independent audit and completion evidence.

## Publication and exclusions

This internal mapping operation is not published. It adds no balance, code,
call data, transferred value, host call/create behavior, storage layout,
concrete log rule, frozen artifact, or public format.

## Consequences

Semantic layers can translate only the trap reason of a frame outcome while
preserving return/revert bytes and keeping the mapping policy explicit. Future
lifting to frame results or prospective propagation payloads can reuse this
operation without changing its lower-layer meaning.

## Implementation record

The completed slice adds exactly one public `mapTrapReason` operation in a
22-line downstream definition module plus one umbrella import. The original
ADR-0052 definition, properties, and tests remain unchanged. The mapper is
function-first, supports different source and target universes, preserves exact
return/revert bytes, and applies the caller's pure function only to trapped
reasons. No instance, alias, helper, or second operation is added.

A 51-line properties module plus one umbrella import publishes exactly five
simp laws: three constructor equations, identity, and composition. Composition
reduces two nested mappings to one composed mapping; no reverse equation is
present. The operation, its three generated equations, and all five laws are
axiom-free, and the combined simp surface terminates at the expected constructor
normal forms.

A 64-line definition-only test module plus two runner lines contains exactly
three runtime assertions. Separate two-constructor source and target reason
types and a nonconstant mapper verify exact return bytes, different exact revert
bytes, and one concrete mapped trap reason without importing the laws.

The implementation commits are `4b28f83` (227 changed lines), `0273aca` (27),
`045a326` (52), and `d37a1a8` (66), all below 300 changed lines; this completion
update is the fifth staged commit. The definition-stage commit also corrects
the ADR to describe Lean's three generated equations in the plural. Focused and
full builds, tests, trust-zero, axiom, simp-termination, semantic-kernel,
metadata, diff, and independent P0-P3 audits pass.

Mapping remains caller-owned and may be lossy. This slice proves no runtime
propagation, ancestry, fatality, recoverability, parent execution, handling,
transaction disposition, or reason taxonomy, and it maps no frame result,
payload, state, effect, or trace.
