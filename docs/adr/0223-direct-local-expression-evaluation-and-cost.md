# ADR-0223: Direct local-expression evaluation and exact cost

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Execute the existing raw local-expression semantics on original syntax

## Decision

Add a total, syntax-size-recursive evaluator on the original `Syntax.Expr`,
explicit `LocalNameTable` and actual `Resolved.Environment`. Return
`Option (Core.Value × Nat)` containing the selected value and exact existing
Core transition cost. The implementation traverses source syntax directly;
it does not resolve, lower, check, or execute Core to obtain either result.
Reuse the existing strict Word literal interpretation and Word primitives.

The evaluator implements exactly `LocalExpressionEvaluatesWithCost`, not a new
source typing or checking policy. Exact first-match names and environment lookup
retain arbitrary sparse, duplicate or unaligned caller rows. No runtime typing,
name uniqueness, lexical/span validity or store validity is presumed. Identifiers
can return opaque supplied values, without allocating cells or invoking closures.
Unsupported selected syntax, missing selected references and wrong primitive
operand shapes return `none`; that is raw evaluation absence, not source rejection.

Conditionals evaluate their Bool condition and only the selected branch.
Short-circuit operators likewise skip the unused right operand and, when selected,
forward its actual value without imposing an extra Bool check. Existing whole
typing separately requires Bool operands and checks every written child. Raw
success may therefore coexist with whole rejection and is never acceptance.

Strict Word operators evaluate both operands in their original left-to-right
order, including zero-divisor division/remainder. Preserve all canonical values
and costs: leaf one, grouping zero overhead, unary plus two, ordinary strict
binary plus three, inequality/less-equal plus five, less plus nine and
greater-equal plus eleven. Selected conditional/short-circuit pairs add two;
short-circuit skipped-right results add three. Costs measure existing machine
transitions, not source traversal, gas, lookup, decoding or elapsed time.

## Proof boundary

Prove independent soundness and completeness against the existing raw cost
constructors. Complete successful output corresponds iff to a raw derivation at
any unchanged store. A general final-store equivalence must explicitly retain
`finalStore = initialStore`; this cannot be erased by the store-free interface.
Characterize `none` by absence of independent raw cost, and relate the projection
to the existing uncosted evaluation without requiring whole resolution.

Lift successful results through existing whole-checking and identity-alignment
premises to exact checked Core paths and fuel thresholds. The executable result
does not manufacture those premises. Conversely, actual completed checked runs
recover the same value and cost. Typed aligned inputs supply successful output;
uninhabited nominal static types do not supply actual values. Do not assign a
whole-run guarantee to a retained-continuation endpoint.

## Boundaries and validation

No change to existing evaluators, raw judgments, checker policies, bounds,
body/entry APIs, argument records, parser/Core/Resolved/Wire or source syntax.
Recursive body evaluation is a later composition, not hidden in this unit.
No new calls, mutation, allocation, inference, defaults or shadowing policy.

Use independent source proofs plus completely parsed expression fixtures with
original tables and actual values. Cover every supported operator, strict
noncommutative/unused work, short-circuit raw/whole contrasts, malformed literal
payloads, duplicate names/IDs, missing and unaligned environments, arbitrary
opaque values, exact costs, stores, checked paths and real fuel boundaries.
Keep definitions/proofs/consumers/publication in small separate commits, proof
files below 300 lines, and public/consumer axiom and dependency audits explicit.
Run focused and aggregate builds, actual parsed execution, full tests and
kernel/metadata/whitespace checks. Diagnostics remain paused; scratch stays local.
