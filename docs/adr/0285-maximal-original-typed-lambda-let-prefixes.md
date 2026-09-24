# ADR-0285: maximal original typed-lambda let prefixes

## Status

Accepted; a standalone opt-in adapter for a maximal consecutive prefix of
original explicitly typed lambda lets, followed by the unchanged shared body.
Canonical Rust remains fixed at
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
All old source entry points, shared checkers, insertion and runtime contracts
remain unchanged. Parser and diagnostic proof work stays paused.

## Motivation and fixed canonical evidence

ADR-0284 connects only one original annotated lambda let to its unchanged shared
tail. With the concrete recursive child that tail rejects another lambda let.
Several consecutive declarations therefore need a new ordered adapter, not an
extra function-entry wrapper. Each later initializer may refer to an earlier
closure, including an earlier binding of its own spelling.

The fixed `crates/hir/src/nameres/body_resolver.rs:40–55` resolves a let's
annotation and initializer before installing its new local. Its lambda rule at
166–184 opens a separate parameter scope. The fixed
`crates/hir-ty/src/infer/stmt.rs:64–103` passes an explicit annotation as the
initializer's expected type. Repeating these steps preserves lexical order:
each initializer sees exactly the preceding outer rows, plus its own inner
parameter when checking its body; only its original tail sees its new let row.
No implicit recursive or simultaneous binding is introduced.

## Source-only prefix boundary

Expose one total source-only Boolean classifier for the current original block.
It is true exactly when the first statement has the original form
`let name : annotation = initializer;` and the initializer's expression form is
a direct lambda. It examines neither annotation meaning nor lambda arity,
compile-time markers, component well-formedness, body typing or checker success.
Do not normalize a grouped lambda, drop source statements or inspect later
statements to choose this boundary.

At a true boundary, process that head with the unchanged expected-lambda
judgment/checker and recurse on its untouched tail under the fresh let binding.
If the head is ill-typed or unsupported, fail there; never fall back to the old
shared body checker. At a false boundary, delegate the complete remaining
original block to the unchanged shared body and stop prefix processing.
An ordinary let or grouped lambda therefore terminates the prefix, even if a
later statement looks like a typed lambda head. What a generic child admits
inside the delegated old body remains determined by that old interface.

This explicit boundary is necessary for exact generic-child correspondence.
An arbitrary child relation can assign a direct source lambda a different Core
output or type. Unconditionally allowing both an old-body terminal derivation
and a new head derivation would overlap, while a maximal-prefix checker selects
only one. Require the source-only false boundary on every terminal constructor.
Do not manufacture child determinism, lambda rejection or Core typing premises
to hide the overlap.

## Definitions and proofs

Add `ExpectedLambdaLetSpine`: the source-only classifier, independent elaboration
with disjoint terminal/head constructors, and a total maximal-prefix checker.
A terminal retains the original shared-body elaboration. A head retains the
original annotation meaning, the expected lambda elaboration in the current
old inputs, and recursively elaborated original tail in exactly
`initial.bindFresh owner name.value declaredType`. The literal output is a
Core let around the initializer and recursive tail. No Core rewriting or fresh
row from the lambda parameter leaks into that recursive tail.

Prove exact checker/elaboration correspondence and absence using only exact
child checker correspondence. Separately prove Core typing using only child
Core typing. Provide a one-layer provenance inversion distinguishing the
source-only terminal boundary from an original head with the exact pre-binder
initializer, fresh tail-row layout and literal Core let. The recursive relation
itself retains all remaining layers; no extra public counting wrappers are needed.

In `ExpectedLambdaLetSpineTyping`, define an independent source-only typing
judgment with the same terminal/head split. Terminal evidence is the false AST
boundary and old shared HasType; head evidence is original annotation meaning,
expected lambda source HasType and recursive tail source HasType. Its definition
must mention neither Core expressions, existential elaboration nor checker graphs.
Prove typing iff elaboration existence from the child's typing correspondence,
then typing iff checker-result existence with exact child checking additionally.
Target two small modules, seven plus three public declarations.

## Consumers and validation

Cover zero, one and arbitrarily many consecutive heads, original same-name
shadowing, aliases with first-match priority, sparse owner-filtered IDs, and
later initializers capturing earlier closures. Construct source-only typing
before requesting elaboration/checker results. Each parameter and corresponding
outer let may reuse a fresh number in disjoint scopes; later heads start from
the previous tail inputs, not previous lambda inner inputs.

Use an artificial exact generic child to demonstrate why a true-boundary
failure cannot be rescued by old-body checking. Keep ordinary/grouped-head
terminal behavior and no restart after an ordinary let explicit. The previous
one-head adapter embeds only with an appropriate non-head tail condition or a
separately justified concrete-child restriction; do not claim an unconditional
generic embedding. Such comparisons may remain consumer-local.

Any generated-Core capture, effect or resumption examples remain Core consumers,
not raw source closure evaluation or canonical backend execution. Keep actual
environments and stores. Run focused/aggregate/full tests, exact standard-only
public and consumer axiom catalogs, independent reviews, old byte/header/import
audits, and kernel-policy, EOF, and whitespace checks. Every new Lean file stays below
300 lines; record separately verified small commits.

## Non-goals

No old admission changes, inferred-let nominal closure inference, recursive
expected-type propagation inside lambda bodies or delegated shared bodies,
implicit recursion, general raw source closure/value/store conversion, new
runtime-safety claim or canonical backend closure-execution theorem.
