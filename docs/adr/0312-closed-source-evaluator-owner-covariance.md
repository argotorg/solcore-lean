# ADR-0312: Exact same-budget covariance of closed source evaluators

## Status

Accepted.

## Context

ADR-0311 maps all finite nested runtime owners and transports original successful
evaluations. Forward success alone cannot preserve absence at a fixed executable
budget: None also covers unsupported syntax, failed lookups and wrong value tags.
The existing expression and body runners therefore need a direct full Option law.

## Decision

For every injective declaration-owner map, prove covariance at the same literal
budget and source syntax for both closed source runners. Map the current owner,
all name IDs, captured keys and complete captured values, and every initial store
element. The output is exactly the old Option mapped over the complete returned
value and every final store element. This preserves both Some and None without a
success, depth-existence, unique-row, typing, heap or surjectivity premise.

Prove the law by joint budget induction over the existing executable definitions.
A separate body-layer theorem consumes both complete predecessor laws, quantified
over all owners, names, captures, stores and source children. It includes empty or
unsupported bodies, trailing returns, singleton blocks, typed/inferred bindings,
discard, actual Boolean branches and ordered Word matching. Fresh IDs commute on
the exact saved names before extending names and captured rows. Selection retains
the actual selected body and literal comparison count; that count is not a budget.

The expression proof handles zero and all executable branches, including tuple
shapes, actual unary/strict Word tags, short circuiting, malformed or unsupported
forms and failed lookups. Strict results commute through the existing Core value
embedding. Calls retain the actual callee-to-argument-to-saved-body order; argument
evaluation is not moved behind a function-tag check. Map complete saved closure
fields and use the saved owner's fresh scope, never substitute caller rows.

## Independent checks

Symbolic examples first build original ordered evaluations and directly calculate
old runner results. A tuple combines an arbitrary opaque value, strict Word work
and a skipped malformed child. Ordered matching uses an arbitrary number of
literal misses before the first hit, with duplicate-hit and malformed suffix
controls. It retains depth three independently of the literal comparison count.
Only then apply covariance at arbitrary budgets, including exact low-depth None.
Nonempty stores and mixed source/Core/source captures retain every field.

Separate controls establish missing names/captures, unsupported host/Core calls,
wrong Boolean/Word tags, typed/inferred wrong-tag bindings and exact fresh-slot
shadowing before applying the law. Distinct self-applicative source lambdas retain
independent original creation and full saved fields, while the old non-return
proof supplies all-budget None. A nonsurjective injection remains admissible.
None itself is not used to identify which of these failure reasons occurred.

Parsed tests independently compare four complete handwritten AST shapes, every
span, EOF and empty diagnostics. Eight typed/inferred, mixed-argument and nonempty
store contexts exercise seven profiles at four budgets: zero, H-1, H and H+3.
The resulting 224 comparisons execute both original and mapped runners. Successful
old endpoints are checked through old soundness and original determinism before
the new law; mapped results retain complete value/store equalities and Option
shape. Creation, callee, argument and the actual saved body are checked separately,
with occupied fresh slots and typed then inferred shadowing. Short-circuit tests
retain an actual saved closure in one branch and skip a missing name in another.

## Preserved boundaries

This adds proofs, consumers and registration only; existing runners, original
rules, selectors, gates, image proofs, parser and diagnostics remain unchanged.
There is no new original converse, exact cost, semantic failure classifier, host
or Core dispatch, mutation, runtime typing or world-validity theorem. Cell
locations and source spans remain literal. No whole-program termination follows.

Keep proof files below 300 lines and commits within 300 changed lines. Verify
import-only ports, all public premises, independent consumers, full builds/tests,
standard public axioms and actual module-owned declarations. Retain every source
version and complete validation output, including failures.
