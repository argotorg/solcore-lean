# ADR-0218: Fuel and resumption for recursive typed let/return trees

- Status: Accepted
- Decision date: 2026-09-09
- Scope: A separate checked body runner, source bound and genuine-state replay

## Decision

Add a separate `LocalInputs.checkTypedLetReturnTree?` / `runTypedLetReturnTree?`
body interface over ADR-0216/0217. Check the actual `toTypeInputs` projection
with the caller's explicit type table and owner, then run the exact accepted
Core with the original ordered environment values and an empty continuation.
Do not rebind parameters, reverse values again, manufacture inhabitants or add
Core transitions. None is whole checker rejection, not exhaustion or a fault.

Known independent cost plus whole acceptance and aligned IDs gives exact
completed/exhausted fuel thresholds for the checked Core. Do not add runtime
typing premises to that generic correspondence. Actual `LocalInputs` supply
aligned, typed values for whole-typing cost existence, exact wrapper done/out
characterizations and fault exclusion. Preserve complete optional results,
including the actual stores and all fields of an exhausted checkpoint.

Define a total source-only `typedLetReturnTreeFuelBound`. Singleton returns reuse
the existing return bound; a mandatory annotated initialized let contributes
initializer bound plus recursive tail bound plus two; a singleton explicit
conditional contributes its condition bound plus the maximum recursive arm
bound plus two. All other original shapes have bound zero. Recurse on full
syntax size, since a singleton conditional may contain a long let-prefix arm.
The bound is an upper bound, not a minimum threshold or acceptance decision.

Bound raw costs without annotation meanings, unused names, whole typing or
runtime environment assumptions. Typed sufficient-fuel completion separately
requires whole acceptance and actual aligned typed values, or a whole-typing
proof at `LocalInputs`. Unknown annotations, shadowing or invalid unselected
children can still have a positive numerical bound and raw paths. In particular,
the new branch-local let can cost seven while the old tree/prefix bound is four;
neither old rejection nor that old bound can replace this new check and budget.

An actual empty-continuation execution that exhausts at `spent` retains the
entire machine state. Prove `spent < cost` and an exact residual `cost - spent`
path to the original final value/store. Resume that genuine checkpoint for any
additional fuel and identify the complete result with the original run at the
sum. Retain pending conditional/let frames, captured old environments, obtained
values and stores. Restarting the body or dropping a continuation is not replay.
Do not treat arbitrary-continuation endpoints as completed body executions.

## Compatibility and boundaries

Singleton-return shapes preserve complete optional equality with the original
return-body runner, including rejection. Old terminal-tree and outer-prefix
runner successes preserve the entire `(type, StatefulRunResult)` at the same
inputs, fuel and store. General old None preservation or conditional/prefix
full optional equality is false when a branch-local binding is newly accepted.
Keep those compatibility statements success-only, using exact static embeddings.

No old body adapter, bound, function-entry policy or record layout changes.
No owner covariance, arbitrary-store replay law, parser/Core/Resolved/Wire
extension, annotation inference, default values, mutation, calls, general scope
policy or early-return unwinding is introduced in this unit.

Validate independent arbitrary-depth source costs/bounds, all threshold cases,
whole rejection with positive bounds, asymmetric selected paths, original parsed
parameters and actual opaque values. Obtain real initializer/conditional/tail
checkpoints and test zero, insufficient, exact and surplus residual fuel across
multiple chunks; contrast restarting or losing captured frames. Check old
successes/full singleton Options, unchanged old entry rejection, all public and
consumer axioms, registration/dependency direction, focused/aggregate builds,
actual parsed execution, full tests and kernel/metadata/whitespace policy. Keep
proof files below 300 lines, commits small and scratch inside the repository;
diagnostic proofs remain paused.
