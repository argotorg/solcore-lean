# ADR-0199: Canonical unsigned Word division and remainder

- Status: Accepted
- Decision date: 2026-09-08
- Scope: Word-only `/` and `%` in the canonical local frontend adapter

## Decision

Extend the existing canonical expression adapter with binary `divide` and
`modulo`. Both operands must have the structural Core Word type and the result
is Word. Resolve to existing `Resolved.Expr.binary .wordDiv` or `.wordMod`, with
the original left and right children under their original identity table. Core
lowering retains that exact binary tree and operand order. No temporary local
identity allocation, overloaded operator lookup or implicit conversion is added.

Adopt the existing unsigned Core primitive policy from ADR-0011: quotient uses
`Core.Word.udiv`, remainder uses `Core.Word.umod`, and a zero divisor gives zero
for both operations. In particular, do not give canonical remainder Lean's raw
remainder-by-zero behavior. Nonzero-divisor laws can reuse the focused Core
unsigned-division interface; nonzero is not a precondition for checking,
evaluation, safety, or cost correspondence.

Evaluate the left child exactly once before the right child, exactly once.
Zero dividend or divisor does not skip either child. Raw source evaluation
threads both stores through these child judgments. Exact transition cost and
source fuel bound are left plus right plus three; two variable/literal leaves
therefore require five transitions, including zero-divisor cases. Whole source
checking still checks every written child, including skipped conditional arms.

Extend independent resolution, typing, avoidance, raw evaluation and cost
constructors plus every existing correspondence, safety, determinism, renaming,
fresh-input insertion, store, bound and resumption proof family. Preserve their
existing premises and conclusions; no new typing, nonzero, alignment, world or
freshness assumptions may be introduced to cover the new cases. Existing return
body and integrated terminal-function contracts reuse the expanded expressions
without an additional wrapper cost or weakened compilation/preparation provenance.

## Boundaries and validation

This is a local explicit-table adapter policy, not general Solcore overloading.
Syntax, parser precedence/associativity, Core and Resolved constructors,
primitive definitions, and Core Wire remain unchanged.
Literal input stays strictly range-checked. Signed division, source calls, mutable
bindings and general recursive statement/early-return semantics are not added.

Independent and parsed consumers cover unequal ordered operands, nonzero quotient
and remainder, zero divisors and dividends, maximum/high-bit values, left-to-right
actual checkpoints, exact five-step thresholds and genuine-state resumption.
Retain actual argument values, differing nonempty stores, injective IDs and whole
entry provenance. Test non-Word operands on both sides and invalid skipped syntax.
Migrate obsolete unsupported-operator negatives only where this decision changes
acceptance. Update structural-bound expectations even for still-ill-typed expressions;
do not erase unrelated rejection coverage. Audit all public declarations and
consumers, run focused/aggregate builds and full tests, and keep standard axioms,
kernel policy, files below 300 lines and small commits. Leave diagnostic
proofs paused and use repository-local scratch.
