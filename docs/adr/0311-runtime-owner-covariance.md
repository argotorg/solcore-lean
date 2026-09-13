# ADR-0311: Owner relabeling of complete runtime values and original evaluation

## Status

Accepted.

## Context

Raw source closures save declaration owners, name rows and mixed captured values.
Relabeling only the current caller's local IDs would leave saved closure owners
and nested captures inconsistent. The existing local-owner maps and fresh-ID
theorem provide the key-level foundation, but do not transport runtime payloads.

## Decision

Define an executable structural owner map over every finite runtime value.
For source closures, map the saved owner, every saved name ID, every captured key
and every captured value recursively. Descend through Core closure captures too:
they may contain source closures even though their Core body and types are inert.
Preserve exact source syntax and spans, spellings, binder indices, row order and
duplicates, Core bodies/types/constructor tags, words, host tags and cell locations.
No stored closure is executed and no cell is dereferenced by the transformation.

Prove identity and composition for complete values and capture tables. Embedded
Core values are unchanged; Core projection has the same complete Option result,
including failure. An injective declaration-owner map induces an injective value
map. This last representation proof uses a logical left inverse derived from
injectivity; surjectivity is not required and the executable map uses no inverse.

For an injective owner map, first-match runtime lookup at a mapped key returns
the mapped complete value, or the same absence. Transport independent lookup
witnesses and prove exact names-only fresh allocation commutes with relabeling.
No unique-row, canonical-name, runtime-typing or store-validity premise is added.
Ordered Word matching preserves selected syntax and visited literal count for
every owner map, without injectivity: only the unchanged outer Word is inspected.

Transport every finite original expression success by the mutual evaluation
induction, including the nine body cases. Rebuild creation with all saved fields;
for calls, use the actual mapped callee, argument and saved body, not caller rows
as a substitute for saved rows. Fresh parameter and local-binding IDs commute
before extending the mapped name/capture lists. Derive the public body theorem
through the existing independent body compatibility relation. All seventeen
expression and nine body rules are covered, with complete initial/final stores
mapped elementwise and source syntax unchanged.

## Independent checks

Handwritten nested source/Core/source captures, duplicate rows, constructor tags,
literal Core bodies and cell references have directly calculated expected values
and nonempty stores before the representation laws are consumed. Successful and
failed Core projections, a nonsurjective injection and a collapsing map are checked.

Independent first-match and fresh calculations demonstrate the injectivity
boundary: collapsing distinct owners with equal binder indices changes a selected
Boolean and changes fresh allocation from index zero to eight. Positive examples
retain foreign owners, duplicate names/captures and missing-name/key results.
Independent ordered matching judgments check literal miss/hit position and count,
wildcard/default selection on mixed closures, and rejection by a leading literal.

Parsed tests compare whole handwritten ASTs, all spans, EOF and diagnostics.
Typed/inferred unary parameters, typed then inferred shadowing bindings, two mixed
arguments and two nonempty stores give eight contexts. Independent original
creation, lookup, binding and call derivations precede covariance. Actual callee
store feeds actual argument evaluation; the actual argument/store feed the saved
body, and its complete endpoint feeds the actual original whole call. Occupied
fresh capture slots are shadowed, not removed. No unrelated source occurrence or
assumed successful child replaces the observed endpoint.

## Preserved boundaries

This is forward transport of original successful derivations, not an original
converse or a same-budget executable Option covariance theorem. Fixture runs do
not establish preservation of finite-depth failure or a general runtime cost.
Existing evaluators, rules, gates, image proofs, parser and diagnostics are unchanged.
Cell locations remain literal; mapped stores are not claimed to satisfy a runtime
world, typing or heap-validity invariant. No host/Core dispatch, mutation, canonical
name/staging alignment, whole-program termination or failure classifier is added.

Keep proof files below 300 lines and commits within 300 changed lines. Verify exact
import-only ports, independent consumers, full builds/tests, standard public axioms
and actual module-owned declarations. Preserve all source versions and failures.
