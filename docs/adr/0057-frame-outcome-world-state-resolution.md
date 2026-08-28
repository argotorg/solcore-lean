# ADR-0057: Resolve frame outcomes against world-state snapshots

- Status: Accepted
- Decision date: 2026-08-28
- Scope: minimal frame-outcome and WorldState connection
- Implementation: Complete

## Context

ADR-0052 distinguishes returned, reverted, and trapped frame outcomes.
ADR-0056 supplies an explicit WorldState but deliberately defines no transition
or rollback policy. The smallest useful connection selects between an
already-provided checkpoint and working state after a non-trapping outcome,
while leaving trap disposition to a later policy.

## Decision

Add exactly one public executable operation:

```lean
FrameOutcome.resolvedWorldState?
    (checkpoint working : WorldState)
    (outcome : FrameOutcome TrapReason) : Option WorldState
```

A returned outcome resolves to `some working`. A reverted outcome resolves to
`some checkpoint`. A trapped outcome resolves to `none`.

Here `none` means only that this slice has not decided how a trap disposes of
state. It does not mean rollback, state deletion, Account absence, an
inconclusive execution, or a failed WorldState lookup.

## Required proof interface

Publish exactly three constructor laws:

1. `FrameOutcome.resolvedWorldState?_returned` returns `some working`;
2. `FrameOutcome.resolvedWorldState?_reverted` returns `some checkpoint`;
3. `FrameOutcome.resolvedWorldState?_trapped` returns `none` for every
   `TrapReason`.

The laws introduce no custom axioms or unchecked declarations. Standard Lean
dependencies are inspected and recorded at completion.

## Required tests

Provide exactly three runtime assertions, one for each constructor. They use
distinguishable checkpoint and working states, verify returned selects working,
verify reverted selects checkpoint, and verify trapped remains unresolved.

## Staged implementation plan

Keep every commit below 300 changed lines and leave the tree green:

1. accept this ADR and mark the slice active in documentation;
2. add the single executable operation;
3. add the exact three constructor laws;
4. add the exact three runtime assertions; and
5. independently audit the slice and update completion documentation.

## Publication and exclusions

This operation is internal and not published. It fixes no trap policy, nested
checkpoint or frame ownership, survival of logs, calls, or creations,
transaction atomicity, state delta, iteration order, or serialization.

It adds no ABI or Core-result adapter, balance, code, Account lifecycle, EVM
revision, opcode, gas schedule, or resource-limit rule. It does not execute a
frame or mutate either input WorldState.

## Consequences

Later frame execution can reuse one explicit and tested outcome-to-state seam.
All difficult questions about nested effects and trap handling remain visible
instead of being hidden inside this minimal selector.

## Implementation record

The completed internal slice publishes exactly one executable operation, three
constructor laws, and three runtime assertions. The definition module is 24
lines, the properties module is 32 lines, and the test module is 53 lines with
two runner lines. Returned nonempty data selects a distinguishable working
state, reverted empty data selects the checkpoint, and a concrete trap reason
leaves state resolution open.

The work landed in four commits: `345cb95` specifies the decision, `e9f1861`
adds the operation, `d1baf80` adds the laws, and `8ff8bae` adds the tests. Each
commit remains below 300 changed lines.

All three public laws report exactly `[propext]`. No custom axiom, `sorryAx`, or
unchecked declaration is present. Focused and full builds, tests, trust-zero,
semantic-kernel, metadata, document-link, and diff checks pass.
