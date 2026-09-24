# ADR-0193: Canonical unsigned Word less-than

- Status: Accepted
- Decision date: 2026-09-08
- Scope: canonical explicit-table local-expression and runtime-entry adapter

## Decision

Resolve canonical `Syntax.BinaryOp.less` into the dedicated identity-free
`Resolved.Expr.wordLt` form (ADR-0192). Resolve both children in their original
table/scope. No source or temporary LocalIds are allocated. Lowering uses the
existing ordered two-let Core expansion, evaluating left then right exactly
once and comparing the retained Word values in the required reverse positions.

Extend independent source typing with Word operands and Bool result, raw
evaluation with original ordered Word operands and unsigned
`decide (leftWord < rightWord)`, and exact-cost evaluation with
`leftCost + rightCost + 9`. The source fuel bound uses that same overhead;
two leaves cost eleven. Compose exact Core paths from both original operand
paths using ADR-0191 and the right operand's lowering-membership proof. No extra
runtime-world, freshness, scope or typing premise is added to existing contracts.

Extend all generic resolution, shape, typing, evaluation, safety, renaming,
input-extension, name-avoidance, store and cost proofs. Preserve arbitrary-map
structural renaming, existing injectivity/runtime-ID-order requirements,
type-only versus actual-runtime-input separation, and compilation provenance.
Whole resolution/typing checks both written children and every conditional
branch, even when raw evaluation skips one. Span replacement retains the exact
resolved shape. Existing fuel and genuine-checkpoint resumption APIs continue
to apply without rewriting suspended states.

## Boundaries

This selects the existing unsigned Word operation, not polymorphic comparison,
Bool comparison, overloaded operators, signed comparison or general source
resolution. Parser precedence and chained-comparison rejection are unchanged.
`>=`, division/remainder, unary signs, calls and mutation remain outside the
adapter. Strict Word literal spelling/range validation stays unchanged.
The explicit-ID comparison builder remains a separate interface. No new Core
primitive, wire change, or diagnostic-proof work is included.

## Validation

Independent source consumers cover all six new public APIs, exact resolved/Core
shape, arbitrary actual Word pairs and unsigned boundaries, equal/strict/reversed
results, operand order, typing rejection, renaming/extension/store invariance,
exact cost/fuel and genuine checkpoints/resumption. Parsed fixtures exercise
precedence and nested arithmetic/conditional composition, real runtime inputs,
Bool-returning function compilation with its own provenance and Word-return
rejection. Migrate only six obsolete source `<` rejection fixtures to still
unsupported `>=`, removing duplicate entries where necessary.

Register and audit all new public declarations and every changed public proof.
Run focused and aggregate builds, full tests, and standard-axiom, kernel-policy,
forbidden-token, and whitespace checks. Keep proof files below 300 lines and commits
small, separate static/dynamic/consumer/registration changes, use repository-local
scratch and preserve paused diagnostic files.
