# ADR-0322: Two-level-group-first local applications

## Status

Accepted; add one source-disjoint opt-in entry that places the exact two-group
expected-lambda adapter before the complete unchanged ADR-0320 entry.

## Context

ADR-0321 checks a direct computation lambda through exactly two source groups,
but deliberately exposes only a standalone adapter. ADR-0320 already unifies
the direct, one-group expected-lambda and ordinary recursive application paths;
its one-group classifier is false on the new two-group lambda shape, so it
cannot reach ADR-0321.

Extending ADR-0320 in place would change a frozen public checker and relation.
Using checker success as dispatch would allow recognized failure to fall
through, while a recursive group-spine dispatcher would reopen the totality and
public-partial-helper problem recorded by ADR-0321. A new source-only wrapper is
the additive boundary.

## Decision

Add `LocalApplicationWithTwoLevelGroupedExpectedLambda` as a separate entry.
Its total classifier is true exactly for one call with one argument whose value
is an outer group containing an inner group whose immediate child is a direct
lambda. It examines only the original syntax tree.

When the classifier is true, invoke
`elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?` on the complete
unchanged source. Its `Option` result is final: do not invoke ADR-0320 after
recognized callee, header, body or expected-type failure. When the classifier
is false, return exactly
`elaborateLocalApplicationWithGroupedExpectedLambda?` for every source. Do not
rebuild the AST, inspect checker success for dispatch or use `Option.orElse`.

The declarative relation retains either the complete ADR-0321 child together
with a true classifier equation, or the complete ADR-0320 child together with
a false equation. Expose generic branch equations for both cases, exact
executable/declarative correspondence, exact absence, Core typing and nested
provenance.

## Independent consumers

A symbolic consumer constructs the depth-two callee and terminal-lambda
derivations before using the new correspondence theorem. It also constructs or
reuses the ADR-0320 direct, one-group and ordinary children. Duplicate names,
foreign owners, sparse indices, opaque runtime values, a nonempty store and an
independently executed Core application remain visible.

A parsed consumer fixes the complete AST and nested spans for
`apply(((lam(x){return x;})))`: call `0..28`, argument list `5..28`, outer group
`6..27`, inner group `7..26` and lambda `8..25`. It checks diagnostics, EOF,
exact branch equality, nested provenance and the established Core fuel 10/11
store boundary.

Preservation controls cover direct and one-group lambdas plus ordinary
arguments at group depths zero through three. Negative controls cover a
three-group lambda; malformed recognized depth-two headers and bodies;
non-function and unresolved callees; nested calls, tuples, conditionals and
calls inside groups; zero and multiple arguments; top-level forms;
return-position lambdas and inferred-let propagation. Every recognized
depth-two rejection must first be equal to the ADR-0321 checker result.

## Preserved boundaries

ADR-0317, ADR-0318, ADR-0319, ADR-0320, ADR-0321, the recursive checker,
canonical source unions and all existing entry points remain unchanged. This
wrapper adds no third-group or arbitrary group-spine policy. It does not make
expected lambdas recursively inferable and does not propagate expected types
through nested calls, tuples, conditionals, returns, inferred lets, typed
bodies, multiple arguments or global resolution.

There is no global catalog, source closure, runtime inhabitant, world safety,
cost/fuel theorem, backend guarantee, principal inference, coercion or overload
policy. Parser and diagnostic proof work remains paused.

Keep every proof and consumer file below 300 lines and every commit within 300
changed lines. Verify focused and aggregate builds, full tests, exact public
axioms and declaration ownership, compiled totality, masked source-policy
scans, independent consumers and preservation of the paused parser/diagnostic
files.
