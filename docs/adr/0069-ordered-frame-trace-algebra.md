# ADR-0069: Ordered frame trace algebra

- Status: Accepted
- Decision date: 2026-08-28
- Scope: opt-in finite chronological trace accumulation for frame effects
- Implementation: Complete

## Context

ADR-0061 deliberately leaves `FrameEffectJournal` generic in its surviving
`TraceState`. Later frame-resolution work treats that value as an opaque,
already-accumulated snapshot. Nested execution now needs a way to build such a
snapshot without fixing concrete event kinds or changing the generic journal.

A named child-completion factory was considered and rejected. It would only
repackage the existing `FrameContinuationContext` constructor while implying
checkpoint lineage and parent/child validity that its type could not prove.
Trace construction is the smaller missing semantic decision that provides real
new behavior.

## Decision

Add exactly one public carrier whose constructor and field are private:

```lean
universe u

structure FrameTrace (Event : Type u) : Type u where private mk ::
  private events : List Event
```

Add exactly four public operations:

```lean
universe u

def FrameTrace.empty {Event : Type u} : FrameTrace Event

def FrameTrace.toList
    {Event : Type u} (trace : FrameTrace Event) : List Event

def FrameTrace.append
    {Event : Type u}
    (earlier later : FrameTrace Event) : FrameTrace Event

def FrameTrace.record
    {Event : Type u}
    (trace : FrameTrace Event) (event : Event) : FrameTrace Event
```

`toList` observes events in chronological order. `record trace event` places
the new event at the end. `append earlier later` places every event observed in
`earlier` before every event observed in `later`. Events are finite, duplicate
events are retained, and append is order-sensitive.

The private constructor and field keep arbitrary List operations out of the
trace-construction API. The `toList` result defines semantic observation order;
it does not define a wire or storage encoding. Add no deriving clause,
instance, coercion, default, alias, or other helper.

This is an opt-in specialization, not a replacement for the generic journal.
Existing code may use
`FrameEffectJournal RollbackState (FrameTrace Event)` without modifying
`FrameEffectJournal` or its resolver. Other `TraceState` choices remain valid.

The phrase extension algebra describes the four operations. It does not prove
that one caller-supplied trace descended from another, nor that every trace in
a program was created only through these operations.

## Required proof interface

Publish exactly seven laws:

```lean
universe u

@[simp] theorem FrameTrace.toList_empty
    {Event : Type u} :
    (FrameTrace.empty : FrameTrace Event).toList = []

@[simp] theorem FrameTrace.toList_append
    {Event : Type u} (earlier later : FrameTrace Event) :
    (FrameTrace.append earlier later).toList =
      earlier.toList ++ later.toList

@[simp] theorem FrameTrace.toList_record
    {Event : Type u} (trace : FrameTrace Event) (event : Event) :
    (FrameTrace.record trace event).toList = trace.toList ++ [event]

theorem FrameTrace.toList_injective
    {Event : Type u} :
    Function.Injective
      (FrameTrace.toList : FrameTrace Event → List Event)

@[simp] theorem FrameTrace.append_empty_left
    {Event : Type u} (trace : FrameTrace Event) :
    FrameTrace.append FrameTrace.empty trace = trace

@[simp] theorem FrameTrace.append_empty_right
    {Event : Type u} (trace : FrameTrace Event) :
    FrameTrace.append trace FrameTrace.empty = trace

theorem FrameTrace.append_assoc
    {Event : Type u} (first second third : FrameTrace Event) :
    FrameTrace.append (FrameTrace.append first second) third =
      FrameTrace.append first (FrameTrace.append second third)
```

Associativity is deliberately non-simp. The carrier, four operations, and all
seven laws must introduce no axioms. Prove the List identity and associativity
steps by structural induction rather than inheriting stronger dependencies
from library simplification lemmas.

Do not publish commutativity: it is false for chronological traces. Do not add
an equality or representation instance merely to simplify tests.

## Required tests

Add exactly six runtime assertions importing only the definition module. A
private event type and `toList` pattern matching must cover empty observation,
one record, repeated tail recording with duplicates, left-before-right append,
both empty identities, and both parenthesizations of a three-part append.

At least one fixture must instantiate
`FrameEffectJournal Nat (FrameTrace Event)` to confirm opt-in integration.
Tests do not derive equality for events, import proofs, replay laws, or inspect
the private representation.

## Staged implementation plan

Keep each of five commits below 300 changed lines: documentation; the exact one
carrier, four operations, and umbrella import; the exact seven laws and
umbrella import; the exact six definition-only assertions and two runner
lines; independent audit and completion evidence.

## Publication and exclusions

This internal trace algebra is not published and does not replace every
`TraceState`. It defines no concrete event constructors, taxonomy, timestamps,
filtering, indexing, deduplication, truncation, size limit, compression,
serialization, hashing, or canonical transaction observation.

It proves no trace-prefix lineage, checkpoint ownership, parent/child identity,
call tree, stack, depth, scheduling, reentrancy, rollback filtering, trap
disposition, transaction boundary, or atomicity. Whether a particular event is
recorded before or after a call remains part of the future transition rules.

It adds no parser or source form, Core expression, Wire field or tag,
ABI, storage layout, EVM revision, opcode, gas schedule,
balance, code, host call/create behavior, or frozen artifact.

## Consequences

Future runtime transitions can accumulate finite semantic events explicitly
and combine an earlier trace with a later fragment in one proved order. Event
meaning, trace ownership, nested scheduling, and transaction policy remain
separate decisions.

## Implementation record

The completed slice adds one constructor-private carrier and exactly four
public operations in a 37-line definition module plus one umbrella import.
The carrier and all four operations are axiom-free. No deriving clause,
instance, coercion, default, alias, or helper is added.

A 65-line properties module plus one umbrella import publishes exactly seven
axiom-free laws. The three observation equations and two identity laws are
simp; observation injectivity and associativity are non-simp. The right
identity and associativity proofs use local structural induction rather than
stronger library dependencies.

Exactly six runtime assertions live in an 87-line definition-only test module
with two runner lines. They cover empty and tail observation, duplicate
retention, ordered append through a specialized FrameEffectJournal, both
identities, and association.

The implementation commits are `fc8ecb1` (210 changed lines), `fc9859b` (38),
`4306c0c` (66), and `f1f9245` (89), all below 300 changed lines; this completion
update is the fifth staged commit. Focused and full builds, tests, trust-zero,
axiom, semantic-kernel, document-link, diff, and independent P0-P3
audits pass.
