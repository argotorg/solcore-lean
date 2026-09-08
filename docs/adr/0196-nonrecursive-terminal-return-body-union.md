# ADR-0196: Nonrecursive terminal return-body union

- Status: Accepted
- Decision date: 2026-09-08
- Scope: common body-only interface for the two proven return profiles

## Decision

Unify the existing singleton return and terminal conditional return adapters
behind a separate nonrecursive `TerminalReturnBody` interface. Dispatch by the
original body shape: a singleton return uses `ReturnBody`; a singleton explicit
if/else uses `ConditionalReturnBody`; all other shapes fail. Keep the existing
adapters and runtime-function compilation/preparation/execution unchanged.

Independent typing, exact elaboration, raw evaluation and exact-cost evaluation
are two-constructor unions of their existing judgments. The wrappers add no
Core operation, value conversion, store change, identity or transition cost.
The conditional branch's two arms remain singleton `ReturnBody` judgments,
not recursively terminal bodies. Nested statement conditionals stay rejected.

Prove exact success iff independent elaboration, typing iff elaboration
existence, Core/type uniqueness, static failure characterization, raw and cost
determinism, selected-value type safety, cost erasure/existence, exact stores,
checked Core evaluation correspondence and continuation-local exact paths.
The common typed-input runner retains actual ordered runtime values, exact
completion/exhaustion boundaries and genuine-state resumption. Its source fuel
bound dispatches to the appropriate existing bound without added cost.

## Boundaries

This unit is not runtime-function entry integration and does not broaden old
singleton APIs. In particular, the old entry bound is still singleton-only.
Any later entry change must reconnect its whole typing, exact preparation,
argument factorization, provenance, cost, owner/store, bound and resumption
families together. Body-level owner/store helper dependencies must stay acyclic.

Whole conditional checking still requires a Bool condition and both original
same-typed arms, although raw evaluation visits only the selected arm. Failed
checks remain absent for every fuel; unsupported-shape bounds are not licenses
to execute. No surrounding statements are ignored, no absent else synthesized,
and no source binding, mutation, calls, loops, parser or wire changes introduced.

## Validation

Independent consumers cover both constructors, exact embedding/projection,
bare/typed expression returns, conditional paths with unequal costs, arbitrary
actual values/stores/continuations, exact all-fuel thresholds and checkpoints.
Parsed consumers verify both accepted profiles through the common API, compare
their complete results against the respective original runner, and retain
whole-check rejection including invalid unselected arms and nested statements.
Existing singleton and runtime-entry behavior must remain unchanged.

Audit every new public declaration for standard axioms only. Run focused and
aggregate builds, full tests, kernel/metadata/forbidden-token/whitespace checks.
Use repository-local scratch, small separated commits, proof files below 300
lines, and preserve all paused diagnostic files.
