# ADR-0161: Canonical local Word complement

- Status: Accepted
- Decision date: 2026-09-08
- Scope: fixed Word-only `~` in the internal local-expression adapter

## Decision

Add canonical `Syntax.UnaryOp.bitNot` to the existing local-expression adapter,
resolving its operand recursively to `Resolved.Expr.unary .wordNot`. Reuse the
direct Core primitive and its existing 256-bit complement semantics from
ADR-0011/0033. No new primitive, desugaring, runtime value, or machine rule is
introduced. The reference-only adapter remains unchanged.

Independent source typing requires a Word operand and gives a Word result.
Independent evaluation evaluates the operand once to `.word w` and returns
`.word w.bitNot` with the operand's final store. Unlike Boolean `!`, this is
not truth-value negation. Boolean and reference operands are not coerced.
Outer and operator source ranges have no semantic effect.

This is a fixed monomorphic interpretation only within the explicit-table
adapter. It does not settle general source overload or class resolution,
numeric-literal interpretation, conversions, or source declarations. Caller
bindings supply the Word values; numeric literal syntax remains unsupported.
Earlier accepted identifier, Boolean-operator, and conditional expressions
keep their exact behavior.

## Guarantees and boundaries

Extend independent resolution, typing, evaluation, determinism, safety, and
Core correspondence to this constructor. Whole-resolution correspondence
remains valid without typing: an untyped operand that evaluates to a Word can
be complemented, even when its own syntax is rejected by the checker. For
example, a selected Word-valued right operand of raw conjunction can be
complemented, but the conjunction still fails Boolean source typing.

Unused-name insertion and injective identity relabeling follow the operand
and retain their existing exact guarantees. A named operand completes after
three Core transitions; double complement after five. Larger sufficient fuel
does not change the result. These are execution counts, not checker complexity
or gas bounds.

Tests cover arbitrary Word values and double-complement involution; zero, one,
and maximum; Bool/reference rejection; missing names and unsupported literals;
grouping, conditionals, and raw short-circuit boundaries; exact insufficient
and sufficient fuel; unused inputs and ID relabeling; and actual parsed-source
execution. Earlier tests of unsupported `~` are updated to assert its new
Word-only boundary. Audit all affected public proofs using standard axioms,
compile public consumers, and run focused, aggregate, and full tests.

The canonical parser, Core machine, and Core Wire remain unchanged.
No source execution endpoint or general binary-operator support is
added.
