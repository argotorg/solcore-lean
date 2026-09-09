# ADR-0260: Recursive negated Word comparisons

Status: Accepted
Date: 2026-09-09

## Context and reference boundary

ADR-0259 supports recursive calls under direct operations, conditionals and
fixed lazy operators. The existing derived Word inequality and less-or-equal
interpretations still use the old pure fallback, preventing recursive children.

The primary reference remains Rust commit
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
`crates/parser/src/parse/expr_pat.rs:307-336` retains non-associative relational
precedence above equality/inequality. `crates/parser/src/lower/body.rs:205-221`
retains original left/right children and the operator span.
`crates/hir-ty/src/infer/expr.rs:1125-1179` resolves named ne/le/lt/ge functions.
`std/std.sol:367-391` defines ne by negating equality and le by negating greater
comparison; lt/ge exchange already-bound parameter values. Successful operator
resolution becomes a call with original left/right arguments in
`crates/specialize/src/specialize/call_resolver.rs:208-254`.

Residual emission in `crates/hull/src/emit/emitter.rs:1193-1232` similarly wraps
inequality and non-strict comparisons in iszero. This change extends only the
established fixed Word interpretations of ADR-0185 and ADR-0186. It does not
implement general named-function/class resolution or prove general differential
agreement. The existing ordered two-let Core representation of less/greater-equal
needs a separate recursive-fragment extension and is not added here.

## Decision

Extend the existing recursive checker at the original notEqual and lessEqual
roots. Check both original children as Word in the same caller scope. Emit
exactly `unary boolNot (binary wordEq left right)` for inequality and
`unary boolNot (binary wordGt left right)` for unsigned less-or-equal. Return
Bool without swapping operands, folding negation or synthesizing source nodes.
Preserve source/operator spans, grouping and precedence.

Add notEqual and lessEqual constructors to each independent typing, elaboration,
raw evaluation and cost judgment. Successful raw rules evaluate the left actual
Word and then the right actual Word, threading the real intermediate store.
Return Boolean negated equality or negated unsigned greater comparison. Cost is
left cost plus right cost plus five, including both binary and unary application.
Retain the separate pending binary and negation frames even for known values.

As in existing strict binaries, a non-Word actual left value does not prevent
evaluation of the right child before the primitive faults. A fault in the left
child does prevent the right child. Right effects therefore remain observable
on a later wrong-payload fault. Structural type tags alone do not validate stores
or provide a successful raw derivation in those cases.

## Proof structure and integration

Keep existing public theorem names, signatures and import entry points.
Reconcile old pure and new recursive derivations privately without introducing
a whole-checking or global call-free premise into raw correspondence.
Move the existing public cost determinism theorem together with its private
pure-overlap proof to a dedicated determinism module, reexported through the old
evaluation properties module. Keep cost existence/erasure there. Maintain the
static and continuation proofs below 300 lines with local private refactoring,
without publishing helpers merely to cross file boundaries.

Add eight source constructors and two elaboration membership cases. The existing
recursive unary/binary Core fragment and insertion/path rules already cover the
exact expansion; do not add a fragment constructor or operator-map family.
Reuse shared body and explicit-entry implementations unchanged. Keep older pure
and nonrecursive endpoints unchanged. Migrate only the two original recursive
inequality/less-or-equal rejection fixtures, preserving their source and ordered
caller tables. Less/greater-equal, tuples, wrong types and unknown names retain
their existing boundaries.

## Validation and limits

Use independently constructed source typing/elaboration/raw-cost evidence and
separately fixed Core/value/store/manual paths. Cover zero, maximum and high-bit
Words, equality and both operand orders, recursive depth, prefix/lazy/conditional
interactions, actual left/right effects and captures, wrong-payload/missing-cell
faults, genuine saved binary/negation frames, exact fuel and resumed outcomes.
Directly consume the existing recursive, body and entry laws, including literal
caller-slot insertion and overlap with pure derivations that skip unknown syntax.

Run focused, aggregate and full tests, complete public/consumer standard-axiom
audits, kernel, metadata and whitespace checks, and independent reviews before
publication. Keep proof/consumer files below 300 lines and commits small.
Parser, diagnostics, Core machine and frozen wire/metadata semantics do not change.
Source closure construction, general operator resolution, early returns,
source-only execution bounds and arbitrary-store safety remain separate.
