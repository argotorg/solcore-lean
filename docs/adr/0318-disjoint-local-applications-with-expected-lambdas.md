# ADR-0318: Disjoint local applications with expected lambda arguments

## Status

Accepted; add one opt-in singleton-application entry that selects the existing
expected direct-lambda path or the unchanged ordinary recursive path solely from
the original source shape.

## Context

ADR-0317 supplies the parameter type of a locally inferable callee to one direct
unary lambda argument. The older recursive local checker already accepts ordinary
singleton applications, but callers currently have to choose between two public
entry points. Trying one checker and falling back when it returns `none` would
make dispatch depend on checker success and could silently reinterpret a malformed
recognized lambda as the recursive checker grows.

Grouped and nested lambda arguments are feasible later extensions, but neither
provides a single entry for the two application forms already checked today. A
source-only disjoint seam is smaller and fixes the precedence needed before more
expected-expression branches are admitted.

## Decision

Add `LocalApplicationWithExpectedLambda` as an additive adapter. A total Boolean
classifier returns true exactly for a singleton call whose sole argument payload
is a direct `Syntax.ExprValue.lambda`. It does not inspect names, types, checker
results, annotations, bodies, spans, or diagnostics.

The independent elaboration judgment has two disjoint constructors:

- the expected constructor requires a true classifier result and reuses the
  complete ADR-0317 application judgment;
- the ordinary constructor retains the exact singleton call and spans, requires
  a false classifier result, and reuses the unchanged recursive-local judgment
  for that whole original call.

Expose `elaborateLocalApplicationWithExpectedLambda?`. It first rejects every
outer shape except an exact singleton call. It then evaluates the classifier
once. The true branch invokes `elaborateExpectedLambdaArgumentApplication?`; the
false branch invokes `elaborateRecursiveLocalComputation?` on the original whole
call. A recognized direct lambda that fails expected checking returns `none` and
is never retried through the ordinary branch. Do not implement this as
`Option.orElse`, checker-success fallback, AST rewriting, or source normalization.

Prove exact checker correspondence, exact absence, Core typing by delegation to
the selected independent child, and provenance that exposes the source-disjoint
branch. The proof must not rely on the current accidental fact that the recursive
checker cannot infer a literal lambda; contradictory classifier equalities alone
establish branch disjointness.

## Independent consumers

A symbolic consumer constructs the direct expected and ordinary recursive
derivations before using the combined checker law. It fixes duplicate names,
foreign-owner rows, sparse indices, literal Core results, and an independently
executed direct-lambda application over opaque values and a nonempty store.

A parsed consumer checks complete diagnostic-free source, EOF, exact AST and
spans for both `apply(lam(x){return x;})` and `apply(ordinary)`. It consumes both
branches through the same entry point only after independent relations are built.
It also proves that a recognized lambda with a bad body cannot be rescued by the
ordinary path.

Negative controls cover a non-function callee, invalid direct-lambda headers,
grouped and nested lambda arguments, zero and multiple arguments, top-level
lambdas and identifiers, tuples, conditionals, return-position lambdas, and
inferred-let propagation. Each absence is adapter-local, not a language-wide
rejection.

## Preserved boundaries

This integration adds no new accepted source union member: it combines exactly
the ordinary singleton calls already accepted by the recursive checker and the
direct-lambda singleton calls already accepted by ADR-0317. Both underlying
checkers and all existing public entry points remain unchanged.

No grouped, nested, tuple, conditional, return, inferred-let, multi-argument, or
global expected-type propagation follows. There is no global catalog, shadowing
policy, owner assignment, currying, recursive closure environment, source closure
construction or evaluation, runtime inhabitant, world safety, cost/fuel theorem,
backend guarantee, principal inference, coercion, or overload resolution.

Keep every proof and consumer file below 300 lines and every commit within 300
changed lines. Verify focused and aggregate builds, full tests, exact public
axioms and declaration ownership, masked source-policy scans, independent
consumers, and preservation of the paused parser/diagnostic work.
