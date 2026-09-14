# ADR-0319: One-level grouped expected lambda applications

## Status

Accepted; add one standalone opt-in adapter that passes a locally inferred
callee parameter type through exactly one source group to a direct computation
lambda argument.

## Context

ADR-0317 checks an exact singleton call whose argument payload is a direct
lambda. ADR-0318 combines that path with ordinary singleton applications behind
a source-only two-way dispatcher. Both intentionally reject
`apply((lam(x){return x;}))`: the direct classifier sees a group payload, while
the unchanged recursive checker cannot infer the inner lambda.

Grouping is transparent in Core but significant in the original syntax. The
group span must not be erased from the frontend evidence, and recursively
stripping arbitrary groups would hide a larger expected-expression policy.
Changing ADR-0318 now would also change a frozen two-way public contract.

## Decision

Add `GroupedExpectedLambdaArgumentApplication` as a separate additive adapter.
Its source is exactly one call with exactly one argument. That argument must be
one `Syntax.ExprValue.group`, and the immediate child of that group must satisfy
the unchanged expected computation-lambda judgment at the parameter type
inferred from the original local callee.

The independent judgment retains:

- the outer call span;
- the argument-list span;
- the one group span;
- the original callee and inner lambda source;
- independent callee and expected-lambda elaborations; and
- the literal Core application and inferred result type.

Expose `elaborateGroupedExpectedLambdaArgumentApplication?`. It matches the
complete grouped singleton shape, runs the unchanged recursive local checker on
the callee, requires a unary function type, and invokes
`elaborateExpectedComputationLambda?` once on the unwrapped immediate child.
Only the group is transparent in the Core output. Do not rewrite the AST,
recursively remove groups, use `Option.orElse`, or retry another checker after a
recognized grouped argument fails.

Prove exact executable/declarative correspondence, exact absence, Core typing
from the two independent children, and provenance exposing every original
source component and the exact Core apply.

## Independent consumers

A symbolic consumer constructs the callee and expected inner-lambda derivations
before using the checker iff. It retains duplicate names, foreign owners, sparse
indices, opaque runtime values, a nonempty store, and an independently executed
Core application.

A parsed consumer checks diagnostic-free complete parsing, EOF, exact AST and
nested spans for `apply((lam(x){return x;}))`. It then constructs the independent
static path and checks the exact Core result and execution boundary.

Negative controls include the ungrouped direct form, two groups, grouped
identifiers, tuples and conditionals, malformed lambda headers and bodies, a
non-function callee, zero and multiple arguments, and top-level groups. These
are absences from this adapter, not language-wide rejection claims.

## Preserved boundaries

The new standalone adapter intentionally accepts one new opt-in grouped shape.
It does not change the accepted set or definitions of ADR-0317, ADR-0318, the
recursive local checker, any canonical source union, or any existing entry
point.

The three existing standalone API families are not themselves a three-way
disjoint dispatcher: ADR-0318's ordinary selector is the complement of its
direct classifier and therefore also selects group payloads before its ordinary
checker rejects them. A future single entry must be a new group-first,
source-only wrapper whose recognized expected branches never fall back.

No second group, nested application, tuple, conditional, return, inferred-let,
typed-body, multi-argument, or global expected-type propagation follows. There
is no global catalog, source closure, runtime inhabitant, world safety,
cost/fuel theorem, backend guarantee, inference principle, coercion, or overload
policy. Parser and diagnostic proof work remains paused.

Keep every proof and consumer file below 300 lines and every commit within 300
changed lines. Verify focused and aggregate builds, full tests, exact public
axioms and declaration ownership, masked source-policy scans, independent
consumers, and preservation of the paused parser/diagnostic files.
