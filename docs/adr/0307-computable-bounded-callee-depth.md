# ADR-0307: Compose outer-call depth from a successful bounded callee

## Status

Accepted.

## Context

ADR-0306 bounds calls under independent original data-callee selection. An inner
application in `f(x)(y)` is not admitted by the data-expression gate, even when
that inner call already returned the exact saved closure needed by the outer
call. Its independently available finite successful run can instead be reused.

## Decision

Define `boundedCalleeLambdaDepthBound calleeBudget argument body` as the maximum
of the supplied callee budget and the existing data argument/body bounds, plus
one. This is a compositional outer bound, not a search for a callee budget.

Require an exact successful evaluator equation at the supplied callee budget,
including the actual saved source, owner, name rows, capture rows and callee
store. Keep independent `SourceUnaryLambdaShape`, `ClosedSourceDataExpression`
for the outer argument, and `ClosedSourceDataBody` for the actual saved body.
The callee need not be a data expression. No successful outer argument or body
evaluation is an admission premise. All decision laws explicitly retain the
supplied successful finite callee equation.

Use existing evaluator soundness on that equation to obtain an independent
original callee witness. Invert an original whole call and use determinism to
fix every actual selected field and callee store. Shape uniqueness fixes the
parameter and body. Success monotonicity raises the supplied callee run to the
predecessor budget, while the direct data bounds evaluate the actual outer
argument and freshly extended saved body. Preserve the actual intermediate
stores, complete mixed result and full final store throughout.

Derive full-endpoint success iff, whole Option stability above the bound,
sufficient-depth None iff no original whole-call success, and bound None iff
None at all budgets. These four laws assume the finite callee run; they do not
find it, classify a failed callee or imply unconditional language termination.
No eventual-completeness, threshold or image oracle supplies a child budget.

## Independent checks

Symbolic consumers first construct original creation and call witnesses for a
saved identity closure passed through the caller's `f` and `x` rows. Start with
`f(x)` and append n outer calls to `(x)`. Independent evaluator recursion proves
the exact all-budget cutoff n+3, retaining the full saved datum and store.
Each outer application consumes its predecessor's independently computed finite
run. Every chain is explicitly outside the data-expression gate; no such gate
is fabricated for the inner application. A second theorem supplies a larger
already successful callee budget and proves that the resulting outer bound
need not be minimal. Arbitrary annotations and separate caller/saved lexical
inputs and creation/invocation stores are retained.

Negative consumers first build an original inner identity call and independently
evaluate it at depth three, obtaining the actual returned target closure. A
selected target string-return body still has no original outer-call success.
A saved target value cannot supply a missing outer caller argument. Both retain
the successful inner run and prove its callee syntax is outside the data gate
before consuming the new outer failure laws. Concrete independent applications
use three distinct owners, duplicate rows and nonempty mixed stores.

Parsed consumers compare complete handwritten nested ASTs, every source span,
EOF and zero diagnostics for `f(x)(y)`. The first identity closure and returned
target closure are created independently with different saved environments.
Actual creation fields and actual inner results flow into outer argument/body
evaluation without replacement. Independent original witnesses or exclusions
precede the depth laws; complete actual values and stores are compared at both
call levels. The 32 mixed-context cases cover fresh target-parameter and saved
free-value returns, missing saved captures and missing outer arguments while
the inner callee succeeds.

## Preserved boundaries

No existing evaluator, original judgment, source gate, primitive, image statement
or proof, selector, lowering or typing definition changes. Inert annotations do
not establish runtime typing or canonical staging. This is not an algorithm for
finding a callee budget, a general failed-callee decision, Core cost, effect,
fault-classification, closure-conversion or whole-language termination theorem.

Keep proof files below 300 lines. Require focused/full builds, complete tests,
kernel policy, metadata, whitespace, independent semantic consumers and reviews,
exact source ports, public axiom checks and actual formal-module ownership
inspection before small exact-path commits. Only the standard three proof
axioms are permitted; retain actual generated names and flags as observed.
