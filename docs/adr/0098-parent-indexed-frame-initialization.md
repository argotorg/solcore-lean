# ADR-0098: Parent-indexed frame initialization

- Status: Accepted
- Decision date: 2026-08-29
- Scope: pure construction of initial frame state relative to a parent pair
- Implementation: Complete

## Context

ADR-0072 provides a trace extension indexed by one earlier trace, and ADR-0074
uses such an extension to construct a completed parent-indexed continuation
context. ADR-0086 and ADR-0087 provide the checkpoint snapshot and checkpointed
working carriers used by the storage and continuation layers. What is missing
is the matching producer-side value boundary: given one designated parent pair
and caller-supplied initial state values, construct the canonical initial trace
extension and checkpointed working pair.

This boundary must not decide how the caller obtained its values. Deriving the
initial WorldState from the parent would prematurely choose value-transfer,
Account-creation, and other call-entry policies. Deriving the rollback value
would similarly choose effect-seeding policy. Both remain explicit inputs.

## Decision

Add exactly one carrier:

```lean
namespace Solcore.Semantics

universe u v

structure ParentIndexedFrameInitialization
    (RollbackState : Type u) (Event : Type v)
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)) :
    Type (max u v) where
  initialWorld : WorldState
  workingRollback : RollbackState

end Solcore.Semantics
```

`parentWorking` is a type index and is not stored again as a field. The two
fields are caller-supplied and independent of their corresponding parent
values. Construction proves no currentness, provenance, ownership, or runtime
relationship.

Add exactly two operations:

```lean
namespace Solcore.Semantics.ParentIndexedFrameInitialization

universe u v

def initialTraceExtension
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (_initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking) :
    FrameTrace.ExtensionFrom parentWorking.2.trace :=
  FrameTrace.ExtensionFrom.start parentWorking.2.trace

def toCheckpointedWorkingPair
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking) :
    FrameCheckpointedWorkingPair RollbackState (FrameTrace Event) :=
  ⟨FrameCheckpointSnapshot.fromWorkingPair parentWorking,
    (initialization.initialWorld,
      ⟨initialization.workingRollback,
        initialization.initialTraceExtension.toTrace⟩)⟩

end Solcore.Semantics.ParentIndexedFrameInitialization
```

The trace extension starts at the exact parent trace and contains no added
event. Its indexed type lets a later caller record events and pass the resulting
extension directly to ADR-0074.

The checkpointed pair uses the exact parent WorldState and effect journal as
its checkpoint. Its working WorldState and rollback component are the two
caller inputs, while its initial working trace is the observed start extension
and therefore equals the parent trace.

The carrier and operations form a pure construction recipe. Their names do not
claim that a frame was launched, entered, scheduled, or executed. Add no
`checkpoint` alias: ADR-0086 already provides
`FrameCheckpointSnapshot.fromWorkingPair`, and the checkpoint remains directly
observable through the returned ADR-0087 carrier.

Add no payload type parameter, address, call data, transferred value, call
kind, code, outcome, event, frame identifier, depth, stack, scheduler request,
custom constructor, third operation, coercion, instance, or default.

## Required proof interface

Publish exactly two simp laws:

```lean
namespace Solcore.Semantics.ParentIndexedFrameInitialization

universe u v

@[simp] theorem initialTraceExtension_toTrace
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking) :
    initialization.initialTraceExtension.toTrace =
      parentWorking.2.trace

@[simp] theorem toCheckpointedWorkingPair_eq
    {RollbackState : Type u} {Event : Type v}
    {parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event)}
    (initialization :
      ParentIndexedFrameInitialization RollbackState Event parentWorking) :
    initialization.toCheckpointedWorkingPair =
      ⟨FrameCheckpointSnapshot.fromWorkingPair parentWorking,
        (initialization.initialWorld,
          ⟨initialization.workingRollback, parentWorking.2.trace⟩)⟩

end Solcore.Semantics.ParentIndexedFrameInitialization
```

Both rules expose a derived value in its canonical form and have no reverse
form, so they are simplification rules. The carrier, generated declarations,
operations, generated equations, and both laws must report exactly `[propext]`.

Add no projection specializations, parent/initial equality or inequality law,
trace-prefix duplicate, inverse, round trip, execution theorem, or provenance
predicate.

## Required compile regressions

Add exactly three private compile examples importing only the new properties
module. They use the public simp interface to cover:

1. the exact initial trace observation for an arbitrary indexed value;
2. the complete canonical checkpointed working pair; and
3. substitution of that canonical pair through an arbitrary consumer of the
   existing `FrameCheckpointedWorkingPair` type.

There is no public test function, runtime declaration, runtime assertion, or
runner call. The test runner imports the compile-only module exactly once.

## Dependency boundary

`ParentIndexedFrameInitialization.lean` imports exactly
`FrameCheckpointedWorkingPair` and `FrameTraceExtension`.
`ParentIndexedFrameInitializationProperties.lean` imports exactly the new
definition and `FrameTraceExtensionProperties`.

The semantic umbrella imports both modules after the checkpointed working-pair
module. The compile regression imports only the new properties module; the
runner adds one import and no call. Existing definitions and theorem statements
remain unchanged.

## What this slice does not decide

The indexed parent pair is caller-designated. It is not proved to be current,
captured at entry, owned by a runtime, or related to an actual parent frame.
The initialization value does not prove that an invocation, entry transition,
copy, value transfer, Account creation, mutation, or event occurred.

The initial WorldState may equal or differ from the parent WorldState. The
working rollback value may equal or differ from the parent rollback value. No
order is chosen among call preparation, value transfer, effect seeding, or
construction of this value.

The trace extension only fixes the algebraic starting prefix. It does not add
an entry event, authenticate events, claim a child-local trace, or say when
later events are recorded.

The slice adds no caller, callee, storage, code, or origin address; call data,
transferred value, call kind, code lookup, balance, nonce, authorization,
outcome provenance, return delivery, trap handling, stack, depth, scheduling,
recursion, reentrancy, gas, ABI, transaction, host I/O, or published
observation. It adds no parser or source syntax, Core expression, Wire field,
or frozen artifact.

## Staged implementation plan

Keep each of five commits below 300 changed lines: this decision and targeted
documentation updates; the exact carrier and two operations plus one umbrella
import; the exact two laws plus one umbrella import; the exact three compile
regressions plus one runner import and no call; independent audit and completion
evidence.

## Implementation record

The completed slice adds a 48-line definition module plus one semantic umbrella
import. It contains exactly one carrier with two fields and exactly the two
required operations. The carrier, generated declarations, operations, and
generated equations report exactly `[propext]`.

A 36-line properties module plus one umbrella import publishes exactly the two
required simp laws. Both report exactly `[propext]`; their one-way canonical
reductions introduce no simplification loop or divergent overlap.

A 48-line compile-only test module plus one runner import contains exactly
three private examples for the trace start, complete pair, and arbitrary
consumer substitution. It adds no public or runtime declaration, assertion, or
runner call.

The implementation commits are `c4f11d3` (267 changed lines), `5e614a5` (49),
`6b32d3e` (37), and `c7c5515` (49), all below 300 changed lines; this completion
update is the fifth staged commit. Focused trust-zero checks, full build and
test runs, kernel checks, diff checks, simplification review,
declaration inventory, and independent P0-P3 audits pass.

## Publication and consequences

This internal initialization recipe is not published. Its checkpointed working
pair can feed existing storage operations and the ADR-0088 continuation adapter.
Its indexed trace extension can be recorded and later supplied to ADR-0074.
The new carrier therefore has existing consumers without requiring a scheduler.

The next contract-entry decision can wrap this value with independently
designed address and invocation inputs. Payload identity and lifetime must not
be hidden behind an unconstrained generic field before those consumers exist.
