# ADR-0072: Indexed frame trace extension

- Status: Accepted
- Decision date: 2026-08-28
- Scope: safe incremental construction of a trace extending one fixed prefix
- Implementation: Complete

## Context

ADR-0069 permits ordered append between two `FrameTrace` values. ADR-0070
defines prefix factorization, and ADR-0071 can store that proof beside one
continuation context. The only construction path currently demonstrated for
that carrier asks its caller to append a fragment and supply the existential
witness manually.

A public child resolver that accepted two same-typed traces would be unsafe as
an abstraction: an already accumulated working trace could be passed where a
child-local fragment was expected, duplicating the earlier prefix. The next
layer needs a construction path that fixes the earlier trace once and accepts
only individual events afterward.

## Decision

Add exactly one constructor-private indexed carrier:

```lean
universe u

structure FrameTrace.ExtensionFrom
    {Event : Type u} (earlier : FrameTrace Event) : Type u where private mk ::
  private fragment : FrameTrace Event
```

The hidden fragment contains only events recorded after `start`. The fixed
`earlier` trace is a type index. External callers can neither construct the
carrier from an arbitrary fragment nor use a named fragment projection. Lean's
generated eliminators remain available, as for other structures; privacy here
controls the direct construction surface rather than making data secret.

Add exactly three public executable operations:

```lean
universe u

def FrameTrace.ExtensionFrom.start
    {Event : Type u}
    (earlier : FrameTrace Event) : FrameTrace.ExtensionFrom earlier

def FrameTrace.ExtensionFrom.toTrace
    {Event : Type u} {earlier : FrameTrace Event}
    (extension : FrameTrace.ExtensionFrom earlier) : FrameTrace Event

def FrameTrace.ExtensionFrom.record
    {Event : Type u} {earlier : FrameTrace Event}
    (extension : FrameTrace.ExtensionFrom earlier) (event : Event) :
    FrameTrace.ExtensionFrom earlier
```

`start earlier` has an empty hidden fragment. `toTrace` appends that fragment
after the fixed earlier trace. `record` places one event at the chronological
tail of the hidden fragment while retaining the same type index.

The new API accepts no `FrameTrace` after `start`. In particular, add no public
append, fragment constructor, `fromFragment`, fragment projection, reset,
merge, coercion, instance, default, alias, or batch-record helper. The existing
general `FrameTrace.append` remains available when callers intentionally need
ordinary algebra; it is not exposed as an indexed-extension operation.

## Required proof interface

Publish one canonical, non-simp prefix theorem with the definition module:

```lean
universe u

theorem FrameTrace.ExtensionFrom.earlier_isPrefixOf_toTrace
    {Event : Type u} {earlier : FrameTrace Event}
    (extension : FrameTrace.ExtensionFrom earlier) :
    FrameTrace.IsPrefixOf earlier extension.toTrace
```

The hidden fragment is the existential witness. The theorem does not decide a
relation or recover data from `Prop`; it exposes evidence already available
from construction.

Publish exactly two additional simp observation laws:

```lean
@[simp] theorem FrameTrace.ExtensionFrom.toTrace_start
    {Event : Type u}
    (earlier : FrameTrace Event) :
    (FrameTrace.ExtensionFrom.start earlier).toTrace = earlier

@[simp] theorem FrameTrace.ExtensionFrom.toTrace_record
    {Event : Type u} {earlier : FrameTrace Event}
    (extension : FrameTrace.ExtensionFrom earlier) (event : Event) :
    (extension.record event).toTrace =
      FrameTrace.record extension.toTrace event
```

The first law shows that a nonempty prefix is retained exactly once at start.
The second fixes chronological tail behavior for every incremental record.
All three theorems and all new definitions must be axiom-free.

## Required tests

Add exactly three runtime assertions and one private compile-time example. Use
a private event type and a nonempty earlier trace. The runtime assertions cover
start, one recorded event, and the same event recorded twice. Observe through
`FrameTrace.toList` so order and duplicate preservation are explicit.

The compile example builds a `FrameContinuationContextWithTracePrefix` whose
effect checkpoint uses the earlier trace and whose working journal uses
`extension.toTrace`. Supply
`extension.earlier_isPrefixOf_toTrace` directly. Import definition modules
only; do not invoke the two observation laws.

The main test module adds one import and one runtime call.

## What this construction does not prove

`ExtensionFrom` records an algebraic relationship between finite values. It
does not prove that `earlier` belongs to a checkpoint, that a runtime invocation
produced any event, that events are authentic, or that the extension belongs to
a child frame. Starting twice, recording duplicate events, or choosing an
unrelated earlier trace remains possible and has no hidden operational meaning.

The carrier defines no parent/child identity, checkpoint ownership or lifetime,
WorldState or rollback-state relationship, stack, depth, scheduling,
reentrancy, trap disposition, transaction rollback, or atomicity. It also makes
no uniqueness claim about a suffix.

## Staged implementation plan

Keep each of five commits below 300 changed lines: documentation; the carrier,
three operations, canonical prefix theorem, and umbrella import; the exact two
observation laws and umbrella import; three runtime assertions, one compile
example, and runner wiring; independent audit and completion evidence.

## Publication and exclusions

This internal construction API is not published. It fixes no concrete event
taxonomy, timestamp, serialization, hashing, compression, size limit, balance,
code, host call/create behavior, ABI, EVM revision, opcode, gas schedule,
parser or source form, Core expression, Wire field or tag, Profile, or frozen
artifact.

## Consequences

A caller can extend a fixed trace incrementally and obtain the exact prefix
evidence required by ADR-0071 without passing an ambiguous same-typed fragment
to a new API. Child transition and checkpoint provenance remain later,
separate decisions.

## Implementation record

The completed slice adds one constructor-private indexed carrier, exactly three
operations, and the canonical non-simp prefix theorem in a 43-line definition
module plus one umbrella import. The generated eliminators remain public, but
there is no named fragment projection or operation that accepts an additional
`FrameTrace`. The carrier, operations, and theorem are axiom-free.

A 34-line properties module plus one umbrella import publishes exactly two simp
observation laws. Both are axiom-free. A 71-line definition-only test module
plus one main import and one runtime call contains exactly three assertions and
one private ADR-0071 integration example.

The implementation commits are `34b43e8` (206 changed lines), `a68391b` (44),
`0075a51` (39), and `9111f10` (73), all below 300 changed lines; this completion
update is the fifth staged commit. Focused and full builds, tests, trust-zero,
axiom, semantic-kernel, metadata, document-link, diff, and independent P0-P3
audits pass.
