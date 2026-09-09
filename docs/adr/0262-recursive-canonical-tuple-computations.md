# ADR-0262: Recursive canonical tuple computations

- Status: Accepted for implementation
- Decision date: 2026-09-09
- Scope: Recursive children of original binary and right-associated tuples

## Primary reference and context

The canonical reference stays `argotorg/solcore-rs` at
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
The product convention in `crates/hir-ty/src/desugar.rs:71–108,990–1000`,
original traversal in `crates/specialize/src/specialize/body.rs:1144–1157`,
and right-associated construction in
`crates/specialize/src/specialize/products.rs:109–149` remain as recorded in
ADR-0237. Pair lowering visits left before right in
`crates/yul/src/translate/lower.rs:296–300` and
`crates/sonatina/src/lower.rs:769–787`.
These observations support the existing product shape, not an equivalence claim
about Rust backend faults or exact execution costs.

The pure adapter already supports empty, binary and longer original tuples.
Recursive applications, operators and conditionals still fall back to that pure
adapter at tuple roots. Existing Core pairs and shared body/entry contracts can
support those recursive children without another representation or runner.

## Decision

Extend recursive checking with the exact binary and three-or-more-element cases.
Add independent `pair` and `many` constructors to recursive source typing,
elaboration, raw evaluation and cost evaluation. Retain empty tuples through
the existing pure rule. Do not introduce a singleton tuple rule: canonical
`(e)` and `(e,)` are groups, while a manually constructed singleton tuple
remains unsupported.

Keep ADR-0237's original-source decomposition. A longer tuple retains its head
and a synthetic tail occurrence with the same outer/delimited spans and untouched
remaining element list. This is internal recursion, not source rewriting,
explicit-child flattening, element reordering or fabricated ranges. Recursion
decreases the original source size. No new mutual judgment family is needed.

Check every written child in the same original caller scope. Arbitrary child
types form the existing right-associated product type. Evaluate the original
head then original tail in the same environment, threading actual stores and
retaining arbitrary actual child values. No runtime typing premise is added.
Each pair contributes three existing Core transitions: costs are head plus tail
plus three, with no terminal Unit for a nonempty tuple. Empty tuples still cost
one. Explicit nesting and grouping retain their existing meanings.

Add one generic pair constructor to the recursive caller fragment. Its two
children weaken at the same cutoff and use the same arbitrary caller prefix.
Insertion keeps literal values, captures and stores and chooses each paired cost
once before every continuation. No new public composition helper is needed.

Extend the existing fourteen proof contracts without changing their names,
types, premises or old import paths. Private compatibility proofs reconcile
old pure tuple derivations with recursive pair/many derivations, including raw
selected branches that skip unsupported original syntax. Shared body/function
definitions and old-success embeddings remain unchanged. Proof files stay below
300 lines; reduce private repetition or use import-compatible structural splits
only when needed, without exporting implementation-only helpers.

## Consumers and boundaries

Migrate all six original recursive-tuple rejection fixtures into independent
positives with identical source strings, file/owner identities, ordered caller
tables, duplicate first matches and original scopes. Preserve all neighboring
negatives and the older nonrecursive endpoints.

Use independent original-source and literal right-associated Core/value/type/
cost evidence, arbitrary tuple lengths and actual recursive callee depths.
Exercise empty/singleton-group/manual-singleton boundaries, trailing commas,
explicit nesting, opaque values/captures, strict children, raw-versus-whole
acceptance, caller insertion, genuine pair frames and exact residual fuel.
Parsed full entries must retain original declarations, parameter order, actual
arguments, supplied stores and declared return types. Check ordered effects,
left/right child faults, same-typed swaps and full checkpoint resumption through
the existing shared contracts.

This adds no source lambdas, global resolution, projection/index/array forms,
new tuple-type policy, source-only fuel bound, store invariance or arbitrary-store
safety. Core/Resolved semantics, parser, diagnostics and frozen wires do not change.
Run focused/aggregate builds, full tests, public/consumer axiom audits, kernel/
metadata/whitespace checks and independent reviews. Keep phase commits small,
leave paused diagnostics untouched and use repository-local scratch.
