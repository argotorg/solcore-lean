# ADR-0089: Bytes-aware frame resolution continuation

- Status: Accepted
- Decision date: 2026-08-28
- Scope: caller-owned partial dispatch of resolved return and revert payloads
- Implementation: Complete

## Context

`FrameContinuationContext.continue?` and the underlying ADR-0066 operation
continue with synchronized state and effects, but intentionally discard return
or revert bytes and do not distinguish those two branches at the callback
boundary. ADR-0068's `FrameResolutionResult` already retains selected state,
selected effects, bytes, and trapped reasons in a branch-complete value.

The next runtime seam should let a caller consume the complete non-trapping
payload without adding a parent-frame carrier or deciding where bytes are
delivered. Separate return and revert callbacks preserve the branch distinction
while leaving their behavior caller-owned. Traps must stay on the existing
unresolved `Option` boundary.

## Decision

Add exactly one public result-first operation:

```lean
namespace Solcore.Semantics.FrameResolutionResult

universe u v w x

/-- Continue a resolved return or revert with its synchronized pair and bytes. -/
def continue?
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (result : FrameResolutionResult RollbackState TraceState TrapReason)
    (onReturned :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Bytes → Option Next)
    (onReverted :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Bytes → Option Next) :
    Option Next :=
  match result with
  | .returned state effects data => onReturned (state, effects) data
  | .reverted state effects data => onReverted (state, effects) data
  | .trapped _ => none

end Solcore.Semantics.FrameResolutionResult
```

Result-first order supports field notation. The `FrameResolutionResult`
namespace and receiver distinguish this operation from
`FrameContinuationContext.continue?`. The synchronized state/effect pair keeps
the same callback convention as the earlier continuation boundary; `Bytes` is
passed separately and exactly.

The operation matches only the already-total result. It does not rerun
resolution. Its declaration and all three generated match equations must
report exactly `[propext]`.

Add no `deliver` alias, long-name duplicate, single shared callback, trap
callback, default handler, new payload carrier, reverse adapter, coercion,
instance, diagnostic result, or second operation.

## Meaning of `none`

A trapped result produces `none` without selecting either callback. A returned
or reverted callback may itself return `none`. Therefore `none` means only
that this partial dispatch produced no `Next` value. It does not distinguish a
trap from caller rejection and does not diagnose, handle, or propagate the
trapped reason.

The trapped reason remains in the original `FrameResolutionResult` value for
explicit pattern matching; existing reason mapping remains a separate value
operation. This continuation is an opt-in non-trapping boundary, not a total
fold.

## Required proof interface

Publish exactly three simp constructor laws:

```lean
namespace Solcore.Semantics.FrameResolutionResult

universe u v w x

@[simp] theorem continue?_returned
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (state : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (data : Bytes)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Bytes → Option Next) :
    (FrameResolutionResult.returned
      (TrapReason := TrapReason) state effects data).continue?
        onReturned onReverted = onReturned (state, effects) data

@[simp] theorem continue?_reverted
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (state : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (data : Bytes)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Bytes → Option Next) :
    (FrameResolutionResult.reverted
      (TrapReason := TrapReason) state effects data).continue?
        onReturned onReverted = onReverted (state, effects) data

@[simp] theorem continue?_trapped
    {RollbackState : Type u} {TraceState : Type v}
    {TrapReason : Type w} {Next : Type x}
    (reason : TrapReason)
    (onReturned onReverted :
      (WorldState × FrameEffectJournal RollbackState TraceState) →
        Bytes → Option Next) :
    (FrameResolutionResult.trapped
      (RollbackState := RollbackState) (TraceState := TraceState) reason).continue?
        onReturned onReverted = (none : Option Next)

end Solcore.Semantics.FrameResolutionResult
```

All three proofs are `rfl` and must report exactly `[propext]`. Add no bind,
identity, composition, callback extensionality, mapping, resolution coherence,
ADR-0088 coherence, evaluation-count, or reverse simp law.

## Required runtime regressions

Add exactly three runtime assertions importing only the new definition module.
One public test function and one private assertion helper are permitted. The
test runner imports the module and calls the test function exactly once.

Use distinct concrete return and revert states, rollback values, nonempty
traces, and nonempty byte arrays. Each selected callback must inspect the exact
state, effects, and bytes and return a branch-specific sentinel; the unselected
callback returns a distinguishable mismatch sentinel. The trap assertion uses
a two-constructor reason and callbacks that would both return sentinels, then
checks that the result is `none`.

The tests do not import or invoke the three laws. They call no resolver,
continuation context, ADR-0088 adapter, trap payload operation, scheduler, or
external effect.

## Dependency boundary

`FrameResolutionResultContinuation.lean` imports exactly
`Solcore.Semantics.FrameResolutionResult`. Its properties module imports
exactly the new definition module.

The semantic umbrella imports the definition and properties immediately after
the existing `FrameResolutionResultProperties` and before result reason
mapping. The test module imports only the definition. The test runner adds one
import and one call. Existing continuation operations and resolution carriers
remain unchanged.

## What this continuation does not decide

The operation performs no external delivery, parent update, state or effect
mutation, callback scheduling, frame resumption, invocation, checkpoint
creation, initialization, ownership transfer, trace append, or transaction
transition. The callback decides what its pure `Option Next` result means.

It makes no claim about evaluation cost, step count, or exactly-once runtime
invocation. It does not handle, classify, map, or propagate trap reasons and
does not prove how its input was produced.

It adds no parser or source syntax, Core expression, resource rule, fuel or gas
policy, Wire field, ABI, serialization, EVM revision, opcode behavior,
Profile, canonical delta, or published observation.

## Staged implementation plan

Keep each of five commits below 300 changed lines: this decision and internal
roadmap update; the exact one operation and umbrella import; the exact three
constructor laws and umbrella import; the exact three runtime assertions with
one runner import and call; independent audit and completion evidence.

## Publication and exclusions

This internal continuation seam is not published. It adds no balance, code,
call data destination, transferred value, host call/create behavior, concrete
event taxonomy, storage layout, frozen artifact, or public format.

## Consequences

Callers can now distinguish resolved return and revert branches while receiving
their exact synchronized state/effects and bytes. Concrete delivery remains a
later caller policy rather than part of this reusable semantic operation.

Future work can compose ADR-0088 construction, total resolution, and this
continuation after deciding whether a direct coherence theorem is useful.
Actual parent-frame mutation, trap disposition, scheduling, and transaction
atomicity remain open.

## Implementation record

The completed slice adds exactly one `FrameResolutionResult.continue?`
operation in a 28-line definition module plus one umbrella import. Its three
generated match equations cover return, revert, and trap. The operation and
all three equations report exactly `[propext]`.

A 54-line properties module plus one umbrella import publishes exactly three
definitional simp laws, one for each result constructor. All three report
exactly `[propext]`; their disjoint one-way reductions introduce no critical
overlap or simp loop.

An 83-line definition-only test module plus one runner import and one call
contains exactly three runtime assertions in one public test function. Distinct
return and revert fixtures check the selected state, rollback value, nonempty
trace, bytes, and callback sentinel. The trap fixture checks that neither
callback is selected. The tests import no laws and call no resolver.

The implementation commits are `4eb7b0c` (244 changed lines), `e5db941` (29),
`a3d1899` (55), and `695dc84` (85), all below 300 changed lines; this completion
update is the fifth staged commit. Focused and full builds, tests, trust-zero,
axiom, simp-termination, semantic-kernel, metadata, diff, and independent
P0-P3 audits pass.

The continuation establishes no delivery, parent mutation, scheduling,
callback evaluation count, trap handling or diagnosis, frame resumption,
checkpoint lifecycle, or transaction policy.
