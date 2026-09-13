# ADR-0302: Computable source depth for closed data expressions

## Status

Accepted.

## Context

The closed source evaluator searches with a recursive depth budget. Existing
soundness and completeness connect successful searches to the original
evaluation judgment, and the threshold theorem describes an eventual successful
cutoff. They do not supply a bound computed from the source syntax alone.
The recursive data-expression gate now covers references, numeric or string
literal syntax, unit, groups, pairs, many tuples, conditionals, both unary
operators, short-circuit operators and all fourteen strict Word binary operators.
Admission deliberately does not require successful lookup or valid payloads.

## Decision

Define `closedSourceDataDepthBound` by recursion on the original expression.
Leaves cost one source-search level. Group and unary nodes add one. Pairs and
binary operators use the maximum child depth plus one. Each original many-tuple
tail is reconstructed with the original expression and tuple ranges, and pays
another recursive level. A conditional counts its guard and both potential
branches; short-circuit operators also count both potential operands.

Unhandled root shapes receive zero. A supported outer node still recurses even
when its child lies outside the gate, so nonmembership does not imply zero.
The independent `ClosedSourceDataExpression` premise is required by every new
evaluation law. Zero is not a sound search bound
for arbitrary source syntax: creation and application can succeed outside this
gate. The function is an executable upper bound, not a minimum-depth classifier.

Prove `ClosedSourceDataExpression.evaluates_at_depthBound` by induction on the
twelve syntax constructors and cases of the original successful evaluation.
Every recursive call preserves its actual input store, returned mixed value and
complete final store. Strict binary evaluation keeps both original ordered Word
children and checks all fourteen primitive meanings. The proof does not use an
existing completeness, threshold or image theorem as its oracle.

Compose this direct result with existing soundness and success monotonicity:

- `evaluate_at_depthBound_iff` equates a successful sufficiently deep search
  with the original judgment for every actual value and entire final store.
- `evaluate_depth_stable` equates the whole Option result at the bound with
  every greater budget, including None.
- `evaluate_depth_none_iff` equates sufficiently deep None with the absence of
  every original successful endpoint.
- `evaluate_depth_none_iff_all_budgets` equates bound None with None at every
  search budget, including smaller budgets.

The absence result concerns successful evaluation in the existing judgment. It
does not distinguish a missing name, absent capture, invalid literal, wrong
operand payload, or any other failure cause.

## Independent checks

Symbolic consumers construct original reference/group/pair/many witnesses before
using the new laws. Arbitrary group depth and tuple arity have sharp boundaries
for those particular examples. Existing independent witnesses cover all fourteen
strict operators. Short-circuit selection returns arbitrary mixed values, while
arbitrarily deep skipped string syntax demonstrates that the global bound need
not be minimal.

Negative consumers independently exclude successful original endpoints for
missing names or captures, strings, out-of-range numeric literals and non-Word
strict operands before deriving bound and all-budget failure. Duplicate lexical
and captured rows retain first-match behavior. A zero operand cannot skip its
missing counterpart. Separate original creation/application witnesses show why
the gate premise cannot be removed from a zero-bound case.

Parsed checks use actual whole expressions and every source range, EOF and zero
diagnostics. A many tuple exercises reconstructed right tails. A conditional
with deeply grouped missing data succeeds early when that branch is skipped and
fails when the branch is selected. Inputs include duplicate rows and mixed
runtime payloads; results retain every actual value and complete store.

## Preserved boundaries

No source evaluator, original evaluation rule, primitive meaning, syntax gate,
body form, image law, lowering rule or typing contract changes. The existing six
public image statements and proofs are untouched. This adds no Core transition
cost bound, runtime typing, fault classification, global function dispatch,
effects, closure conversion or whole-language totality. Source-call and body
search bounds remain distinct work.

All new proof files remain below 300 lines. Focused and full builds, complete
tests, kernel policy, metadata, whitespace and public axiom checks are required
before committing. Only the standard three proof axioms are permitted.
