# ADR-0070: Frame trace prefix relation

- Status: Accepted
- Decision date: 2026-08-28
- Scope: non-strict prefix factorization for ordered frame traces
- Implementation: Complete

## Context

ADR-0069 gives frame effects an opt-in ordered trace algebra. A proposed child
resolver would have accepted a parent trace and a child fragment with the same
`FrameTrace` type, appended them, and resolved the child outcome. That API
could silently append the parent prefix twice when a caller supplied an already
accumulated working trace in the fragment position.

The next layer needs an explicit proposition saying that one accumulated trace
contains another as its initial segment. This proof boundary should exist
before any child-frame carrier or resolver claims trace consistency.

## Decision

Add exactly one public proposition-valued definition:

```lean
universe u

def FrameTrace.IsPrefixOf
    {Event : Type u}
    (earlier later : FrameTrace Event) : Prop :=
  ∃ fragment, later = FrameTrace.append earlier fragment
```

The relation is non-strict: a trace is its own prefix through the empty
fragment. `earlier` occurs first, and the existential fragment accounts for
the rest of `later` in chronological order.

This is algebraic factorization of two values, not runtime provenance. A proof
does not show that a particular invocation produced the fragment, that a
transition appended exactly once, or that either value belongs to a parent or
child frame. It is therefore named `IsPrefixOf`, not `DescendsFrom`,
`ChildTraceOf`, or `Lineage`.

Add no carrier, executable operation, boolean checker, decidability or equality
instance, coercion, alias, default, unique-fragment claim, or other helper.

## Required proof interface

Publish exactly four non-simp laws:

```lean
universe u

theorem FrameTrace.empty_isPrefixOf
    {Event : Type u} (trace : FrameTrace Event) :
    FrameTrace.IsPrefixOf FrameTrace.empty trace

theorem FrameTrace.isPrefixOf_refl
    {Event : Type u} (trace : FrameTrace Event) :
    FrameTrace.IsPrefixOf trace trace

theorem FrameTrace.isPrefixOf_append
    {Event : Type u} (earlier fragment : FrameTrace Event) :
    FrameTrace.IsPrefixOf earlier (FrameTrace.append earlier fragment)

theorem FrameTrace.isPrefixOf_trans
    {Event : Type u} {first second third : FrameTrace Event}
    (firstSecond : FrameTrace.IsPrefixOf first second)
    (secondThird : FrameTrace.IsPrefixOf second third) :
    FrameTrace.IsPrefixOf first third
```

All four laws and the relation definition must introduce no axioms. Empty and
reflexive cases use the ordered trace identities. Transitivity concatenates the
two witness fragments and uses associativity.

None of the laws is simp. Prefix evidence is intended to remain a visible
proof obligation when later frame-transition carriers require it; clients can
invoke the canonical witnesses explicitly.

## Required compile regressions

Add exactly four private compile-time examples importing only the definition
module. Concrete traces over a private two-constructor event type must cover an
empty prefix of a nonempty trace, reflexivity, direct append, and a two-fragment
transitive shape. Each example supplies its existential fragment directly and
must close by `rfl` without importing or replaying the public laws.

The main test module adds exactly one import and no runtime call. This slice
adds a proposition and proof surface, not an executable prefix decision.

## Staged implementation plan

Keep each of five commits below 300 changed lines: documentation; the exact one
relation definition and umbrella import; the exact four laws and umbrella
import; the exact four definition-only compile regressions and one test import;
independent audit and completion evidence.

## Publication and exclusions

This internal relation is not published. It defines no executable prefix
checker, event equality, suffix extraction API, trace mutation, trace creation
history, event authenticity, checkpoint ownership or lifetime, parent/child
identity, call tree, stack, depth, scheduling, or reentrancy.

It chooses no trap disposition, rollback filtering, transaction boundary or
atomicity, concrete event taxonomy, timestamp, serialization, hashing, size
limit, compression, canonical observation, ABI, EVM revision, opcode, gas
schedule, parser or source form, Core expression, Wire field or tag,
balance, code, host call/create behavior, or frozen artifact.

## Consequences

Later frame-transition carriers can require explicit evidence that an
accumulated working trace extends its entry trace, without blindly appending a
same-typed value. The relation alone does not establish who produced either
trace; invocation and checkpoint provenance remain separate decisions.

## Implementation record

The completed slice adds exactly one proposition-valued definition in a
16-line module plus one umbrella import. The relation is axiom-free and adds no
carrier, executable operation, checker, instance, alias, or helper.

A 37-line properties module plus one umbrella import publishes exactly four
non-simp, axiom-free laws for empty, reflexive, direct-append, and transitive
prefixes. A 41-line definition-only compile-regression module plus one main
test import contains exactly four private examples and no runtime call.

The implementation commits are `183e0a2` (165 changed lines), `cb423e4` (17),
`7644bba` (38), and `51f793a` (42), all below 300 changed lines; this completion
update is the fifth staged commit. Focused and full builds, tests, trust-zero,
axiom, semantic-kernel, document-link, diff, and independent P0-P3
audits pass.
