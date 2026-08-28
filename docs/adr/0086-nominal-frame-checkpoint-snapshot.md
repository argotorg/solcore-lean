# ADR-0086: Nominal frame checkpoint snapshot

- Status: Accepted
- Decision date: 2026-08-28
- Scope: nominal value representation of a caller-supplied synchronized checkpoint snapshot
- Implementation: Complete

## Context

The frame semantics already passes synchronized pairs of `WorldState` and
`FrameEffectJournal` through resolution and continuation boundaries. ADR-0073
also uses one such raw pair as the `parentWorking` index of a completed nested
context. None of those APIs gives a prospective checkpoint pair its own
nominal type before a frame is completed.

The next nested-runtime foundation needs to distinguish a designated
checkpoint value from a separate working pair without yet requiring them to be
equal. A dependent parent index would duplicate ADR-0073's completed-context
relationship and prematurely constrain every future consumer. An entry or
capture operation would also overstate what a pure constructor can prove.

This slice therefore names only the value boundary. It does not establish that
an invocation occurred, that the supplied pair was current at frame entry, or
that any runtime owns it.

## Decision

Add exactly one public carrier:

```lean
namespace Solcore.Semantics

universe u v

/-- Caller-designated synchronized values represented as a frame checkpoint. -/
structure FrameCheckpointSnapshot
    (RollbackState : Type u) (TraceState : Type v) : Type (max u v) where
  state : WorldState
  effects : FrameEffectJournal RollbackState TraceState

end Solcore.Semantics
```

The state and effects are grouped in one nominal value. `RollbackState` and
`TraceState` remain fully parametric; do not restrict the carrier to
`FrameTrace`, events, a parent index, or a trap-reason type.

Add exactly one public constructor adapter:

```lean
namespace Solcore.Semantics.FrameCheckpointSnapshot

universe u v

/-- Represent one caller-supplied synchronized working pair as a checkpoint. -/
def fromWorkingPair
    {RollbackState : Type u} {TraceState : Type v}
    (working : WorldState × FrameEffectJournal RollbackState TraceState) :
    FrameCheckpointSnapshot RollbackState TraceState :=
  ⟨working.1, working.2⟩

end Solcore.Semantics.FrameCheckpointSnapshot
```

`fromWorkingPair` is a pure, lossless representation adapter. It does not read
runtime state or perform a transition. Its name deliberately avoids `capture`,
`entry`, `start`, and `begin`, because the function cannot establish time,
provenance, or execution.

The carrier, constructor, operation, and generated operation equation must
report exactly `[propext]`. Add no `toWorkingPair`, coercion, equality proof,
validity predicate, smart default, second operation, identity, owner, or frame
identifier.

## Required proof interface

Publish exactly two simp projection laws:

```lean
namespace Solcore.Semantics.FrameCheckpointSnapshot

universe u v

@[simp] theorem state_fromWorkingPair
    {RollbackState : Type u} {TraceState : Type v}
    (working : WorldState × FrameEffectJournal RollbackState TraceState) :
    (fromWorkingPair working).state = working.1 := by
  rfl

@[simp] theorem effects_fromWorkingPair
    {RollbackState : Type u} {TraceState : Type v}
    (working : WorldState × FrameEffectJournal RollbackState TraceState) :
    (fromWorkingPair working).effects = working.2 := by
  rfl

end Solcore.Semantics.FrameCheckpointSnapshot
```

Both laws are definitional and must report exactly `[propext]`. They expose the
two observations needed by later consumers without publishing an extensionality
alias, eta law, constructor equality law, inverse, or round-trip API.

## Required compile regressions

Add exactly three private definition-only compile examples. Import only the
new definition module; do not import or consume the two laws. Cover:

1. an abstract whole-value equation from an arbitrary working pair to the
   corresponding constructor, closed by `rfl`;
2. a concrete nonempty `WorldState` fixture whose exact state is retained; and
3. a concrete effect journal with distinguishable rollback and nonempty trace
   values whose whole journal is retained.

The test module must contain no public declaration, runtime assertion, test
function, or runtime call. Add exactly one import to the existing test runner
and no call site.

These regressions demonstrate definitional value preservation only. They must
not describe the pair as freshly captured, entry-authentic, owned, valid, or
produced by execution.

## Dependency boundary

`FrameCheckpointSnapshot.lean` imports exactly
`Solcore.Semantics.FrameEffectJournal` and `Solcore.Semantics.WorldState`, both
of whose public names occur directly in the carrier. The properties module
imports exactly the new definition module.

The semantic umbrella imports the definition and properties modules after its
existing `WorldState` import. The compile-regression module imports exactly the
definition module, and the test runner imports that regression module exactly
once. Existing raw-pair resolvers, continuation contexts, and parent-indexed
types remain unchanged.

## What this snapshot does not decide

The adapter does not establish that its input is current working state, was
observed at frame entry, came from a parent, was copied, or belongs to a
particular frame. It proves no freshness, validity, ownership, lifetime,
lineage, or invocation occurrence.

It does not construct or initialize child working state or effects, equate a
checkpoint with a working pair, seed rollback state, append an entry event,
advance a trace, create an account, transfer value, or choose ordering among
those actions.

It does not run or complete a frame, resolve an outcome, schedule nested work,
deliver return or revert data, handle or propagate a trap, enforce call depth
or reentrancy, or decide transaction commit, rollback, or atomicity.

It adds no parser or source syntax, Core expression, resource-limit rule, fuel
or gas policy, Wire or Oracle field, ABI, serialization, EVM revision, opcode
behavior, Profile, canonical delta, or published observation.

## Staged implementation plan

Keep each of five commits below 300 changed lines: this decision and internal
roadmap update; the exact carrier and operation with one umbrella import; the
exact two laws with one umbrella import; the exact three definition-only
compile regressions with one runner import; independent audit and completion
evidence.

The immediately following design must consume this type in a carrier that also
accepts an independent caller-supplied working pair. That relationship must not
assume checkpoint and working equality. This requirement prevents the nominal
adapter from becoming an orphan API while deferring initialization policy.

## Publication and exclusions

This internal value representation is not published. It adds no balance, code,
call data, transferred value, host call/create behavior, concrete event
taxonomy, storage layout, frozen artifact, or public format.

## Consequences

Later APIs can distinguish a designated checkpoint snapshot from a working
pair at the type level while reusing the repository's existing synchronized
state-and-effect representation.

Checkpoint creation time, ownership, lifetime, active-frame transitions,
scheduling, diagnostics, and transaction atomicity remain open. The next slice
will pair this snapshot with independent working values; it will still not
choose how either value was produced.

## Implementation record

The completed slice adds exactly one `FrameCheckpointSnapshot` carrier and one
`fromWorkingPair` operation in a 29-line definition module plus one umbrella
import. The carrier remains generic in rollback and trace types, and the
operation definitionally retains both members of the supplied pair. The
carrier, constructor, projections, operation, and generated equation report
exactly `[propext]`.

A 25-line properties module plus one umbrella import publishes exactly two
definitional simp laws for state and effect projection. Both report exactly
`[propext]`; their one-way reductions introduce no simp overlap or loop.

A 47-line definition-only test module plus one runner import contains exactly
three private compile examples and no runtime declaration, assertion, or call.
They cover the abstract whole constructor, a concrete nonempty world state,
and a complete journal with rollback sentinel `37` and nonempty trace
`[2, 3]`. The module imports the definition only and does not consume the
published laws.

The implementation commits are `cbbc5a8` (237 changed lines), `19e38de` (30),
`447be7f` (26), and `2d1f44d` (48), all below 300 changed lines; this completion
update is the fifth staged commit. Focused and full builds, tests, trust-zero,
axiom, simp-termination, semantic-kernel, metadata, diff, and independent
P0-P3 audits pass.

This nominal value representation establishes no capture time, entry
authenticity, freshness, ownership, lifetime, provenance, working
initialization, scheduling, or transaction policy.
