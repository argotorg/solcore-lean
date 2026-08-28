# ADR-0060: External-checkpoint frame run result

- Status: Accepted
- Decision date: 2026-08-28
- Scope: minimal state-only result of running one frame
- Implementation: Complete

## Context

ADR-0052 supplies parametric frame halt outcomes. ADR-0057 resolves an outcome
against externally supplied checkpoint and working states. ADR-0056 supplies
the WorldState carried by those states. The next minimal operational seam is to
pair the speculative working state produced by a frame run with its outcome,
without moving checkpoint ownership into the result.

## Decision

Add exactly one public carrier:

```lean
structure FrameRunResult (TrapReason) where
  working : WorldState
  outcome : FrameOutcome TrapReason
```

The generated constructor and projections are an intentional semantic payload
surface. They expose no representation beyond the two values a frame run must
produce. The checkpoint remains externally owned by the caller and is not a
field of `FrameRunResult`. Add no `BEq`, `DecidableEq`, or `Repr` derivation and
no additional extensionality interface.

Add exactly one named public executable operation:

```lean
FrameRunResult.resolvedWorldState?
    (checkpoint : WorldState)
    (result : FrameRunResult TrapReason) : Option WorldState
```

It delegates to `FrameOutcome.resolvedWorldState?`, passing `checkpoint`,
`result.working`, and `result.outcome`. A returned result resolves to
`some result.working`; a reverted result resolves to `some checkpoint`; and a
trapped result resolves to `none`.

That `none` retains ADR-0057's single meaning: trap disposition is not decided
by this slice. It is not rollback, state deletion, Account absence, failed
lookup, or inconclusive execution.

## Required proof interface

Publish exactly these three constructor laws:

```lean
@[simp] theorem FrameRunResult.resolvedWorldState?_returned
    {TrapReason : Type u}
    (checkpoint working : WorldState) (data : Bytes) :
    FrameRunResult.resolvedWorldState? checkpoint
        (⟨working, .returned data⟩ : FrameRunResult TrapReason) =
      some working

@[simp] theorem FrameRunResult.resolvedWorldState?_reverted
    {TrapReason : Type u}
    (checkpoint working : WorldState) (data : Bytes) :
    FrameRunResult.resolvedWorldState? checkpoint
        (⟨working, .reverted data⟩ : FrameRunResult TrapReason) =
      some checkpoint

@[simp] theorem FrameRunResult.resolvedWorldState?_trapped
    {TrapReason : Type u}
    (checkpoint working : WorldState) (reason : TrapReason) :
    FrameRunResult.resolvedWorldState? checkpoint
        (⟨working, .trapped reason⟩ : FrameRunResult TrapReason) = none
```

The laws quantify arbitrary return/revert bytes, trap reasons, checkpoints, and
working states. All three are simp laws. No additional projection or equality
law is required.

## Required tests

Add exactly three runtime assertions with distinguishable checkpoint and
working states. They cover returned, reverted, and trapped results. The tests
also read the public `working` and `outcome` projections, including payload or
reason projections, so the intentional carrier surface is executable coverage
rather than an unused declaration.

## Staged implementation plan

Keep every commit below 300 changed lines:

1. accept this ADR and mark only this slice active;
2. add the carrier and named resolver;
3. add the exact three constructor laws;
4. add the exact three runtime assertions; and
5. independently audit and record completion evidence.

## Publication and exclusions

This internal slice is not published. It defines no nested frame or checkpoint
stack, parent-child commit rule, logs, calls, creations, surviving effects,
transaction boundary or atomicity, ABI, Core-result adapter, trap taxonomy, EVM
revision, opcode, gas schedule, or resource-limit policy.

It adds no parser or source form, Wire field or tag, Profile, Oracle behavior,
state delta, ordering, serialization, or frozen artifact. It does not execute a
frame and does not choose how the external checkpoint was created.

## Consequences

A future frame evaluator can return one explicit state-and-outcome payload and
reuse the completed resolver. Nested effects and transaction semantics remain
separate decisions.

## Implementation record

The completed internal slice adds exactly one public carrier in a 28-line
definition module with one umbrella import. Its two public fields and generated
constructor, projections, and recursor are the intentional payload surface.
There is exactly one named executable resolver and no deriving clause,
instance, extensionality law, or helper.

The 32-line properties module plus one umbrella import publishes exactly three
constructor laws. All three are simp laws proved by `rfl`; each reports exactly
`[propext]`. The resolver definition also reports `[propext]`. Exactly three
runtime assertions in a 68-line definition-only test module plus two runner
lines cover resolution and the public working, payload, and reason projections.

The implementation commits are `0e4baab` (156 changed lines), `cb58b25` (29),
`116f3f9` (33), and `5e83e6d` (70). Each remains below 300 changed lines.
Focused and full builds, tests, trust-zero, semantic-kernel, metadata,
forbidden-declaration, document-link, diff, and independent audits pass.
