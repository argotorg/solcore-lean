# ADR-0321: Two-level grouped expected lambda applications

## Status

Accepted; add one standalone opt-in adapter that passes a locally inferred
callee parameter type through exactly two source groups to a direct computation
lambda argument.

## Context

ADR-0319 handles exactly one group around a direct lambda, and ADR-0320 places
that shape before the frozen direct-or-ordinary entry. A direct lambda inside
two groups remains outside both expected branches even though the unchanged
recursive checker already treats groups around ordinary inferable expressions
as transparent.

A finite two-or-more group-spine design was prototyped. Its recursive executable
retained all spans and proved exact correspondence, but its structural recursion
compiled to a public helper marked partial. That violates the repository's
compiled-declaration policy even though the authored source used no partial
declaration. Replacing it with a fuel or recursion certificate would introduce
a separate public totality boundary. Exact depth two has no such recursion and
is the smallest policy-clean semantic extension.

## Decision

Add `TwoLevelGroupedExpectedLambdaArgumentApplication` as a separate additive
adapter. Its source is exactly one call with exactly one argument. That argument
must be an outer `Syntax.ExprValue.group` whose immediate child is one inner
group, whose immediate child must satisfy the unchanged expected computation-
lambda judgment at the parameter type inferred from the original local callee.

The independent judgment retains:

- the outer call span;
- the argument-list span;
- both group spans in outer-to-inner order;
- the original callee and terminal lambda source;
- independent callee and expected-lambda elaborations; and
- the literal Core application and inferred result type.

Expose `elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?`. It matches
the complete two-group singleton shape, invokes the unchanged recursive local
checker on the original callee, requires a unary function type, and invokes the
unchanged expected computation-lambda checker once on the original terminal
child. Both groups are transparent only in the Core result. Do not rebuild the
AST, recursively peel groups, inspect another checker result for dispatch, use
`Option.orElse`, or retry after a recognized two-group source fails.

Prove exact executable/declarative correspondence, exact absence, Core typing
from the two independent semantic children, and provenance exposing every
original source component and the exact Core apply.

## Independent consumers

A symbolic consumer constructs the callee and expected terminal-lambda
derivations before using checker correspondence. It retains duplicate names,
foreign owners, sparse indices, opaque runtime values, a nonempty store and an
independently executed Core application. It checks exact two-group provenance,
typing and failure boundaries without appealing to the current recursive
lambda rejection.

A parsed consumer checks diagnostic-free complete parsing, EOF, the exact AST
and all nested spans for `apply(((lam(x){return x;})))`: call `0..28`, argument
list `5..28`, outer group `6..27`, inner group `7..26`, and lambda `8..25`.
The exact Core endpoint keeps the established fuel 10/11 and store boundary.

Negative and preservation controls include direct and one-group lambdas through
ADR-0320, a three-group lambda, ordinary expressions inside zero through three
groups, malformed two-group lambda headers and bodies, a non-function or
unresolved callee, nested calls, tuples, conditionals, calls inside groups,
zero and multiple arguments, top-level forms, return-position lambdas and
inferred-let propagation. Ordinary multi-group acceptance remains ADR-0318 and
ADR-0320 behavior; it is not intercepted by this standalone adapter.

## Preserved boundaries

Only the new standalone adapter accepts the exact two-group expected-lambda
shape. ADR-0317, ADR-0318, ADR-0319, ADR-0320, the recursive checker, canonical
source unions and every existing entry point remain unchanged. A later unified
entry must use a new exact-two source classifier before ADR-0320 and must commit
recognized failure to this adapter.

No three-or-more group policy, general group-spine recursion, nested-call,
tuple, conditional, return, inferred-let, typed-body or multi-argument expected
propagation follows. There is no global catalog, source closure, runtime
inhabitant, world safety, cost/fuel theorem, backend guarantee, principal
inference, coercion or overload policy. Parser and diagnostic proof work remains
paused.

Keep every proof and consumer file below 300 lines and every commit within 300
changed lines. Verify focused and aggregate builds, full tests, exact public
axioms and declaration ownership, compiled totality, masked source-policy scans,
independent consumers and preservation of the paused parser/diagnostic files.
