# ADR-0071: Frame continuation context with trace prefix

- Status: Accepted
- Decision date: 2026-08-28
- Scope: bind ordered trace-prefix evidence to one frame continuation context
- Implementation: Complete

## Context

ADR-0067 groups the caller-owned inputs used after one completed frame, and
ADR-0068 resolves that context to a total first-order result. Its effect
checkpoint and working journal still accept any two values of the same trace
type. ADR-0069 and ADR-0070 now provide an opt-in ordered trace and an explicit
prefix proposition, but neither attaches that proposition to the context whose
traces it describes.

A later consumer should not carry a context and an unrelated prefix proof as
separate arguments. The invariant must refer to the exact checkpoint and
working projections stored in the same value. It must remain optional for the
generic `FrameContinuationContext`, because not every trace state uses
`FrameTrace`.

## Decision

Add exactly one public refined carrier:

```lean
universe u v w

structure FrameContinuationContextWithTracePrefix
    (RollbackState : Type u) (Event : Type v)
    (TrapReason : Type w)
    extends FrameContinuationContext
      RollbackState (FrameTrace Event) TrapReason where
  tracePrefix :
    FrameTrace.IsPrefixOf effectCheckpoint.trace effectWorking.trace
```

The inherited context is the existing semantic value, not a duplicate set of
four fields. The proof field depends on that exact inherited context. Replacing
either journal therefore requires new evidence before a refined value can be
constructed. The generated constructor, base projection, proof projection,
and eliminators are intentional.

The evidence remains a proposition. Executable paths never check, branch on,
or decide it. This makes trace consistency a construction-time obligation
without adding a runtime boolean or suffix computation.

Add no public operation, named theorem, properties module, coercion, instance,
default, alias, smart constructor, executable checker, decidability, suffix
extractor, or mutation helper. Existing parent fields and operations remain
available through field notation or the generated base projection. In
particular, ADR-0068 already resolves this value; a second resolver would be a
pure alias.

A smart constructor that blindly appends two same-typed traces would recreate
the double-prefix risk that motivated ADR-0070.

## Required proof interface

The generated `tracePrefix` projection is the complete proof interface. It
returns evidence about the exact two inherited journals and needs no theorem
that merely repeats the field type. Existing ADR-0068 laws continue to
characterize resolution through the inherited context.

The carrier definition must introduce no new axiom. Its prefix evidence is not
inspected by any executable operation.

## Required compile regressions

Add exactly three private compile-time examples importing only the definition
module. Use a private event type, a nonempty checkpoint trace, a nonempty
fragment, and a working trace formed by appending them. Cover:

- construction with the direct witness `⟨fragment, rfl⟩`;
- projection of evidence about the exact inherited checkpoint and working
  traces; and
- reuse of the existing total resolver, definitionally equal to resolving the
  generated base projection.

The main test module adds exactly one import and no runtime call. Do not add a
fake executable test for an invalid proof or replay the public prefix laws.

## What this invariant does not prove

`IsPrefixOf` is non-strict value factorization. The refined context does not
show which runtime invocation produced either trace, that its events are
authentic, that an append occurred exactly once, that the suffix is unique, or
that the two traces belong to parent and child frames. Unrelated traces that
happen to satisfy the same factorization can still be packaged with a proof.

The carrier also does not relate WorldState or rollback checkpoints to their
producers. It defines no frame identity, checkpoint ownership or lifetime,
stack, depth, scheduling, reentrancy, trap disposition, trace survival after a
trap, transaction rollback, or atomicity.

## Staged implementation plan

Keep each of four commits below 300 changed lines: documentation; the exact one
carrier and umbrella import; the exact three definition-only compile regressions
and one test import; independent audit and completion evidence.

## Publication and exclusions

This internal refinement is not published. It adds no concrete event taxonomy,
timestamp, serialization, hashing, compression, size limit, balance, code,
host call/create behavior, ABI, EVM revision, opcode, gas schedule, parser or
source form, Core expression, Wire field or tag, Profile, Oracle behavior, or
frozen artifact.

## Consequences

Consumers can require an ordered trace-consistency proof and the frame inputs
it describes as one value while reusing existing continuation and total
resolution operations. Generic frame semantics remain reusable for other trace
representations. Runtime provenance and the actual nested invocation transition
remain later, separate decisions.

## Implementation record

The completed slice adds exactly one 21-line carrier module plus one umbrella
import. The carrier extends the existing context, adds only the dependent
`tracePrefix` field, and reports exactly `[propext]`. It adds no public
operation, theorem, properties module, instance, coercion, alias, or helper.

A 52-line definition-only regression module plus one main test import contains
exactly three private examples and no runtime call. They cover direct
construction, proof projection from the exact inherited journals, and `rfl`
reuse of the existing total resolver.

The implementation commits are `091434c` (174 changed lines), `d3e0649` (22),
and `52bab8f` (53), all below 300 changed lines; this completion update is the
fourth staged commit. Focused and full builds, tests, trust-zero, axiom,
semantic-kernel, metadata, document-link, diff, and independent P0-P3 audits
pass.
