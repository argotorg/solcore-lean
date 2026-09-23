# ADR-0194: Canonical unsigned Word greater-than-or-equal

- Status: Accepted
- Decision date: 2026-09-08
- Scope: canonical explicit-table local-expression and runtime-entry adapter

## Decision

Resolve canonical `Syntax.BinaryOp.greaterEqual` to
`Resolved.Expr.unary .boolNot (.wordLt left right)`, retaining both original
children under the original name table. The existing identity-free comparison
lowers to two ordered positional Core lets; the outer Boolean negation adds no
local identity. Evaluate the left then right operand exactly once, producing
the unsigned Boolean `!(decide (leftWord < rightWord))`. Equality yields true.

Independent source typing requires two Words and returns Bool. Raw evaluation
retains exact operand order and stores. Exact source cost and the structural
fuel bound add eleven to the child costs: two leaves take thirteen transitions.
Compose the ordered comparison path with the existing unary cost rule, without
adding typing, freshness, runtime-world or original-scope premises to generic
cost correspondence. At twelve transitions the less-than Boolean is returned
with negation still pending; a further transition produces the final result.

Extend every generic resolution, shape, typing, evaluation, safety, renaming,
name-avoidance, input-extension, cost, store and fuel proof. Preserve arbitrary
structural ID maps, existing semantic injectivity and runtime alignment, exact
checkpoint resumption, type-only compilation and actual-argument provenance.
Whole resolution and typing still check all written children, including skipped
branches. Strict literal spelling and range validation remain unchanged.

## Boundaries

This is unsigned Word comparison, not polymorphic or signed comparison,
overloading, constant folding or an operand swap. No Core primitive, Resolved
constructor, parser, wire, or diagnostic-proof change is required.
Division, remainder, unary signs, calls, assignment and general source binding
remain outside the adapter. Remove only the seven obsolete `>=` rejection
fixtures, retaining division/remainder and chained-comparison rejection.

## Validation

Independent source consumers exercise the six new APIs, exact resolved/Core
shape, arbitrary Word pairs and stores, equal/strict/reverse/high-bit/maximum
results, both-child type rejection, exact cost and all fuel thresholds, genuine
checkpoints and their pending frames, structural maps and semantic invariance,
independent Bool-returning compilation/preparation and Word-return rejection.
Parsed tests retain actual ordered arguments, provenance, precedence, short
circuiting and nested arithmetic/conditional composition.

Audit all changed public proofs and new declarations for standard axioms only.
Run focused and aggregate builds, full tests, kernel/metadata/forbidden-token
and whitespace checks. Keep proof files below 300 lines and commits small;
separate static/dynamic/consumer/publication changes. Use repository-local
scratch and preserve all paused diagnostic files.
