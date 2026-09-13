# ADR-0306: Computable depth under independent data-callee selection

## Status

Accepted.

## Context

ADR-0305 bounds identifier calls when first-match lookup fixes a saved closure.
The existing data-expression gate also admits groups, conditionals and logical
short-circuit expressions which may return saved source closures as mixed values.
The actual selected body still belongs to the runtime closure, not caller syntax.

## Decision

Define `dataCalleeLambdaDepthBound callee argument body` as the maximum of the
existing data-callee, data-argument and actual saved-body bounds, plus one.
The original call gives each of its three children the same predecessor budget.

Require independent `ClosedSourceDataExpression` gates for callee and argument,
`ClosedSourceDataBody` for the selected body, and `SourceUnaryLambdaShape` for
the saved source. Also require an independent original successful callee witness
which explicitly identifies the actual source, saved owner, name rows, capture
rows and callee store. This successful-selection premise remains explicit in
every decision law. Neither argument nor body success is an admission premise.

The public contract is conditional on that selection, not a callee recognizer
or an unconditional termination claim. It does not decide whether an arbitrary
callee selects a usable closure. Unmarked typed or inferred parameter syntax and
return annotations do not establish runtime typing or canonical staging.

Invert the original whole call. Callee determinism against the independent
selection fixes all actual saved fields and the intermediate callee store;
shape uniqueness fixes the actual parameter and body. Apply the existing direct
data-depth proofs to the three actual children. Preserve the caller argument,
freshly extended saved body, mixed value and all intermediate/final stores.
No eventual-completeness, threshold or image theorem supplies the bound.

Compose with existing soundness and success monotonicity for full-endpoint
success iff, whole Option stability above the bound, sufficient-depth None iff
no original whole-call success, and bound None iff None at every budget.
All four laws retain the same independent successful-selection premise.

## Independent checks

Symbolic consumers construct original creation, pickup, grouped callee, fresh
body and whole-call witnesses before using the new laws. Independent runner
recursions cover arbitrary callee groups and saved-body nesting. Conditional
selection of a saved closure can skip deeply nested invalid callee syntax,
showing that the written-source bound is sufficient rather than minimal.
Actual caller and saved fields, annotations, mixed payloads and stores remain
separate. The saved-body dependence is not a caller-syntax-only bound.

Negative consumers independently exclude original whole-call success. A selected
string-return body cannot fall back to an unselected bare-return closure even
though that other closure's separate call succeeds. A false logical-or guard
can select a saved closure whose existing saved value still cannot supply a
missing caller argument. Original selections and those independent comparison
successes precede the new finite-depth failure laws.

Parsed consumers check complete handwritten ASTs, every source range, EOF and
zero diagnostics for `(f)(x)`, `(b ? f : z)(x)`, `(b && f)(x)` and `(b || f)(x)`.
Actual evaluator-created closure fields feed independent original selections;
actual selected callee and body endpoints are compared in full before the new
laws. The 32 mixed-context cases cover fresh parameter and saved free-value
returns, missing selected captures and missing caller arguments, with duplicate
rows and opaque source/Core closures. The grouped reference call needs depth
three; the grouped conditional and logical cases need four in these fixtures.

## Preserved boundaries

No existing evaluator, original rule, data gate, primitive, selector, image
statement or proof, lowering rule or typing definition changes. The new results
do not cover arbitrary callee evaluation, direct creation within the data gate,
general nested calls, runtime typing, Core costs, fault classification, effects,
closure conversion or whole-language totality.

Keep proof files below 300 lines. Require focused/full builds, complete tests,
kernel policy, metadata, whitespace, independent consumers, public axiom checks,
exact source ports and actual formal-module ownership inspection before small
commits. Permit only the standard three proof axioms and retain all actual
compiler-generated names and flags without normalizing prototype differences.
