# ADR-0084: Heterogeneous trace-prefixed continuation-context reason mapping

- Status: Accepted
- Decision date: 2026-08-28
- Scope: prefix-evidence-preserving lift of continuation-context reason mapping
- Implementation: Complete

## Context

ADR-0071 refines `FrameContinuationContext` with proof that its checkpoint
trace prefixes its working trace. ADR-0081 maps the reason type of the base
context while preserving both journals, so the prefix proposition remains
definitionally identical. The refined carrier still lacks a canonical lift.

Rebuilding it manually would force consumers to repeat both the base mapping
and dependent proof transport. The lift should reuse the exact existing proof,
without mapping events, traces, rollback state, or evidence.

## Decision

Add exactly one function-first public operation:

```lean
namespace Solcore.Semantics.FrameContinuationContextWithTracePrefix

universe u v w x

def mapTrapReason
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context :
      FrameContinuationContextWithTracePrefix RollbackState Event TrapReason) :
    FrameContinuationContextWithTracePrefix
      RollbackState Event MappedTrapReason :=
  {
    toFrameContinuationContext :=
      context.toFrameContinuationContext.mapTrapReason mapReason
    tracePrefix := context.tracePrefix
  }

end Solcore.Semantics.FrameContinuationContextWithTracePrefix
```

The base context delegates to ADR-0081. Because that mapper copies both effect
journals definitionally, `context.tracePrefix` already has the required target
type; add no cast, equality transport, proof helper, or replacement evidence.
The mapper may be lossy. Rollback and event types remain unchanged.

The operation and its generated equation must report exactly `[propext]`. Add
no generic `map` alias, coercion, `Functor` instance, default mapper, subtype,
second operation, or validity condition.

## Required proof interface

Publish exactly four simp laws: `mapTrapReason_mk` for the public constructor,
`toFrameContinuationContext_mapTrapReason` for abstract consumers, identity,
and composition.

```lean
namespace Solcore.Semantics.FrameContinuationContextWithTracePrefix

universe u v w x y

@[simp] theorem mapTrapReason_mk
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context :
      FrameContinuationContext RollbackState (FrameTrace Event) TrapReason)
    (tracePrefix :
      FrameTrace.IsPrefixOf
        context.effectCheckpoint.trace context.effectWorking.trace) :
    mapTrapReason mapReason
        (⟨context, tracePrefix⟩ :
          FrameContinuationContextWithTracePrefix
            RollbackState Event TrapReason) =
      (⟨context.mapTrapReason mapReason, tracePrefix⟩ :
        FrameContinuationContextWithTracePrefix
          RollbackState Event MappedTrapReason)

@[simp] theorem toFrameContinuationContext_mapTrapReason
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    (mapReason : TrapReason → MappedTrapReason)
    (context :
      FrameContinuationContextWithTracePrefix RollbackState Event TrapReason) :
    (mapTrapReason mapReason context).toFrameContinuationContext =
      context.toFrameContinuationContext.mapTrapReason mapReason

@[simp] theorem mapTrapReason_id
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    (context :
      FrameContinuationContextWithTracePrefix RollbackState Event TrapReason) :
    mapTrapReason (fun reason => reason) context = context

@[simp] theorem mapTrapReason_comp
    {RollbackState : Type u} {Event : Type v}
    {TrapReason : Type w} {MappedTrapReason : Type x}
    {IntermediateTrapReason : Type y}
    (first : TrapReason → IntermediateTrapReason)
    (second : IntermediateTrapReason → MappedTrapReason)
    (context :
      FrameContinuationContextWithTracePrefix RollbackState Event TrapReason) :
    mapTrapReason second (mapTrapReason first context) =
      mapTrapReason (fun reason => second (first reason)) context

end Solcore.Semantics.FrameContinuationContextWithTracePrefix
```

The constructor law maps the base context and reuses the same `tracePrefix`
argument. The projection law is `rfl`. Identity and composition expose the one
refined constructor and reuse ADR-0081's laws. Composition is oriented only
from two mappings to one mapping by `fun reason => second (first reason)`.

Constructor and projection rewriting converge on the same mapped base context.
Identity and composition strictly remove mapping layers, with no reverse rule
or simp loop. The operation, its generated equation, and all four laws must
report exactly `[propext]`.

Add no proof-object equality law for `tracePrefix`, inherited-field duplicates,
branch-specific law, extensionality theorem, `resolve` law, or `continue?` law.
Inherited fields simplify through the base projection and ADR-0081. ADR-0082
and ADR-0083 already provide the two base observation laws.

## Required compile regressions

Add exactly three private compile examples and no runtime assertion or test
function. Import the new definition module only; do not consume the four laws.

Use distinct two-constructor source and target reason types, a nonconstant
mapper, a nonempty checkpoint trace, a nonempty suffix, and distinct concrete
state and journal values. Cover:

1. an abstract whole-constructor equation mapping the base context while
   reusing the exact supplied prefix evidence, closed by `rfl`;
2. recovery from a mapped value of evidence for the original context's exact
   checkpoint and working trace proposition; and
3. a concrete trapped fixture whose complete base-context projection is
   definitionally equal to the expected preserved fields, working state, and
   mapped reason.

Add the test module to the runner imports exactly once and add no runtime call.
Return and revert branch behavior, bytes, and all base fields are already
tested by ADR-0081 and must not be duplicated here.

## Dependency boundary

`FrameContinuationContextWithTracePrefixTrapReasonMap.lean` imports exactly the
ADR-0071 carrier and ADR-0081 definition modules. Its properties module imports
exactly the new definition and ADR-0081 properties modules. Both semantic
imports follow the existing trace-prefix carrier and precede the parent-indexed
carrier in the umbrella.

The compile-regression module imports only the new definition module. Existing
ADR-0071, ADR-0081, ADR-0082, and ADR-0083 definition, properties, and tests
remain unchanged.

## What this mapping does not decide

The operation does not map events, traces, rollback state, prefix evidence, a
parent index, checkpoint equality, rollback selection, or propagation payload.
It does not strengthen prefix evidence into provenance or strict extension.

It does not resolve or continue a frame, propagate or handle a trap, establish
ancestry, schedule execution, create checkpoints, or decide transaction
rollback or atomicity.

It adds no parser or source syntax, Core fault adapter, resource-limit rule,
fuel or gas policy, Wire field, ABI, serialization, EVM revision,
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

Consumers can change a trace-prefixed context's reason type without rebuilding
its base value or proof. Both traces and their existing non-strict prefix
evidence remain exact.

ADR-0085 fixes the parent-indexed lift while preserving the additional
checkpoint-to-parent equality proof.

## Implementation record

The completed slice adds exactly one public
`FrameContinuationContextWithTracePrefix.mapTrapReason` operation in a 27-line
definition module plus one umbrella import. The operation delegates the full
base context to ADR-0081 and directly reuses the existing `tracePrefix` term;
it adds no cast, transport helper, replacement proof, or second operation. The
operation and its generated equation report exactly `[propext]`.

A 61-line properties module plus one umbrella import publishes exactly four
simp laws: the refined constructor, base projection, identity, and composition.
Concrete and abstract refined contexts normalize without unfolding the
definition. All four laws report exactly `[propext]`, and their critical pairs
converge to the same record and base-context normal forms.

A 95-line definition-only test module plus one runner import contains exactly
three private compile examples and no runtime function, assertion, or call.
They cover whole-constructor reduction with the same evidence, recovery of the
original exact prefix proposition, and a concrete trapped complete-base-record
equality with distinct states, journals, nonempty traces, and mapped reason.

The implementation commits are `eb333b6` (246 changed lines), `264dac4` (28),
`1700720` (62), and `366f8e9` (96), all below 300 changed lines; this completion
update is the fifth staged commit. Focused and full builds, tests, trust-zero,
axiom, simp-termination, semantic-kernel, metadata, diff, and independent P0-P3
audits pass.

The lift maps no parent index, checkpoint equality, rollback selection,
payload, trace, event, or proof object and establishes no provenance,
propagation, scheduling, or transaction policy.
