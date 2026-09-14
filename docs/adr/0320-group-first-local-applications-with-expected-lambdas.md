# ADR-0320: Group-first local applications with expected lambdas

## Status

Accepted; add one standalone opt-in source dispatcher that checks the exact
one-level grouped direct-lambda shape before delegating every other source to
the unchanged ADR-0318 local-application entry.

## Context

ADR-0318 combines direct expected-lambda applications and ordinary recursive
singleton applications behind a source-only classifier. ADR-0319 separately
accepts an exact singleton call whose sole argument is one group containing an
immediate computation lambda. The standalone APIs do not form a safe union:
ADR-0318 classifies a group payload as ordinary before its recursive checker
rejects the inner literal lambda.

Trying ADR-0319 and falling back to ADR-0318 when it returns `none` would make
precedence depend on semantic success. A malformed recognized grouped lambda
could then be reinterpreted if the recursive checker later learns more grouped
forms. Intercepting every group would instead remove ordinary grouped arguments
such as `apply((ordinary))` from ADR-0318's existing recursive path.

## Decision

Add `LocalApplicationWithGroupedExpectedLambda` as a separate additive wrapper.
A total Boolean classifier returns true exactly for a call with one argument
whose payload is one group and whose immediate child payload is a direct
`Syntax.ExprValue.lambda`. It ignores spans, names, types, annotations, lambda
validity, bodies, diagnostics and checker results.

The independent judgment has two constructors:

- `grouped` requires a true classifier result and retains the complete
  ADR-0319 grouped elaboration;
- `existing` requires a false classifier result and retains the complete
  ADR-0318 combined elaboration.

The second constructor is not called ungrouped because a false result includes
grouped non-lambda and deeper-group sources. Nesting the ADR-0318 judgment gives
grouped, direct and ordinary semantic leaves without duplicating or reopening
its already frozen disjoint relation.

Expose `elaborateLocalApplicationWithGroupedExpectedLambda?`. It evaluates the
new classifier once. A true result invokes only
`elaborateGroupedExpectedLambdaArgumentApplication?`; a false result invokes
only `elaborateLocalApplicationWithExpectedLambda?` on the unchanged original
source. Do not use checker-success fallback, `Option.orElse`, AST rewriting,
recursive group removal or a broadened ADR-0318 classifier.

Expose branch equations for both classifier results. They make recognized
grouped failure and complete ADR-0318 preservation explicit for arbitrary
sources, rather than only for currently successful examples. Prove exact
executable/declarative correspondence, exact absence, Core typing by delegation
and provenance retaining the classifier result and complete selected child.
Branch disjointness follows only from contradictory Boolean equalities.

## Independent consumers

A symbolic consumer constructs grouped, direct and ordinary child derivations
before consuming the new relation. It checks the two generic branch equations,
nested provenance, exact absence after recognized grouped failures, preservation
of grouped ordinary input through ADR-0318, duplicate names, foreign owners,
sparse indices, opaque runtime values, a nonempty store and independently
executed Core applications.

A parsed consumer checks diagnostic-free complete parsing, EOF, exact ASTs and
spans for grouped, direct, ordinary and grouped-ordinary calls. It then verifies
the exact selected child and Core result. The grouped path retains the ADR-0319
call, argument-list, group and inner spans; the direct and ordinary paths are
exactly equal to ADR-0318. Runtime checks retain the existing exact fuel
boundary and store.

Negative controls include malformed recognized grouped lambda headers and
bodies, a non-function grouped callee, a malformed direct lambda, second groups,
nested calls, tuples, conditionals, zero and multiple arguments, top-level
forms, return-position lambdas and inferred-let propagation. These are local
dispatcher observations, not language-wide rejection claims.

## Preserved boundaries

Only the new wrapper exposes the three semantic leaves. ADR-0317, ADR-0318,
ADR-0319, the recursive checker, canonical source unions and every existing
entry point remain unchanged. A false new classifier means exact delegation to
ADR-0318, not rejection and not absence of all grouping. A true classifier
commits to ADR-0319 even when its checker fails.

No second or arbitrary group propagation, recursive expected-expression
checking, nested-call, tuple, conditional, return, inferred-let, typed-body or
multi-argument propagation follows. There is no global catalog, resolution
policy, source closure, runtime inhabitant, world safety, cost/fuel theorem,
backend guarantee, principal inference, coercion or overload policy. Parser and
diagnostic proof work remains paused.

Keep every proof and consumer file below 300 lines and every commit within 300
changed lines. Verify focused and aggregate builds, full tests, exact public
axioms and declaration ownership, masked source-policy scans, independent
consumers, branch preservation and the paused parser/diagnostic files.
