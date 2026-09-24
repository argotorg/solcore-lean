# ADR-0205: Recursive return-tree evaluation and cost

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Independent recursive evaluation and exact checked Core paths

## Decision

Extend the separate terminal return-tree adapter with independent raw evaluation
and exact-cost judgments. A singleton leaf reuses existing return-body semantics.
Each internal node evaluates its condition and only the selected recursive arm,
threading the original initial, intermediate and final stores. There is no
evaluation premise for an unselected subtree, even when it is arbitrarily deep
or unsupported. Whole static acceptance remains a separate judgment.

A conditional node costs the condition's cost plus the selected arm's cost plus
two existing Core transitions. A bare leaf costs one Unit transition; expression
leaves retain the exact local-expression cost. Return-tree wrappers add no
operation, identity, value conversion or store effect.

Prove raw and cost determinism, unchanged stores, cost erasure and existence,
and positive costs by recursive source evidence. These laws do not require whole
checking, static typing or a typed runtime environment. Whole source typing plus
actual aligned and typed runtime inputs gives evaluation existence and a typed
result. Keep the identity alignment and runtime typing premises separate.

Prove raw evaluation iff evaluation of the exact accepted Core with identity
alignment only. Do not add runtime typing: correspondence still applies when
an actual value disagrees with the static context, without granting type safety.
An arbitrary same-typed Core or an environment with differently ordered IDs is
not a substitute for exact accepted Core and alignment.

Transport checked source costs to exact Core transition paths under any pending
continuation. The original continuation is retained, not executed at the path
endpoint. Use the existing conditional path composition and singleton-return
continuation laws. Include the empty-continuation specialization, but no inverse
or path-length uniqueness claim for arbitrary pending continuations.

Embed old singleton, conditional and terminal-union raw/cost evidence into the
recursive judgments, retaining value, both stores and cost exactly and without
adding checking premises. These embeddings are one-way on arbitrary blocks;
the recursive semantics can visit deeper selected arms than the old profiles.

## Boundaries and validation

This unit adds no runner or runtime-function integration. Fixed-fuel boundaries,
recursive bounds and genuine-checkpoint resumption follow separately. Identity
and store replay invariance are also separate from the unchanged-store result.
Existing checker, parser, Core, Resolved, allocator, function entry and frozen
interface definitions are unchanged. No source calls, loops, mutation, fallthrough
or general early-return unwinding is introduced.

Independent and parsed consumers cover deep asymmetric selected paths, exact
costs, arbitrary stores and continuations, actual typed opaque values, untyped
but aligned environments, identity misalignment, and invalid skipped subtrees
with raw success but whole rejection. Use original parsed bodies and their real
accepted Core, not hand-built compilation records. Audit all public declarations
and consumers with standard axioms only; run focused/aggregate builds, full
tests and kernel-policy and whitespace checks. Keep proof files below 300 lines,
commits small, diagnostics paused and scratch files inside the repository.
