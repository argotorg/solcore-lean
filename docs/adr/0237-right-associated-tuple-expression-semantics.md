# ADR-0237: Right-associated canonical tuple expression semantics

- Status: Accepted for implementation
- Decision date: 2026-09-09
- Scope: Three-or-more-element tuples in the existing local expression adapter

## Primary reference and context

The canonical reference remains `argotorg/solcore-rs` at
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
`crates/hir-ty/src/desugar.rs:71–108,990–1000` uses the same original-order
right-associated product convention for expressions as for types.
`crates/specialize/src/specialize/body.rs:1144–1157` visits original elements
in order; `crates/specialize/src/specialize/products.rs:109–149` builds
`Pair(head, product(tail))`, stopping at the final single element. Existing
pair backends retain left-before-right order in
`crates/yul/src/translate/lower.rs:296–300` and
`crates/sonatina/src/lower.rs:769–787`.

ADR-0230/0231 already support exact binary tuples and empty Unit expressions.
ADR-0236 supports arbitrary finite structural tuple types. The existing
Resolved/Core pair machinery can execute longer original expression lists
without adding another representation, transition or runner.

## Decision

Add a three-or-more-element branch to the existing resolver, direct evaluator
and source fuel bound. Add corresponding independent `many` constructors to
resolution, source typing, spelling avoidance, raw evaluation and costed
evaluation. Preserve the old empty/binary cases and canonical grouping.
The synthetic tail occurrence keeps both original outer and delimited spans
and the untouched remaining elements. This is an internal decomposition, not
source AST rewriting, explicit-child flattening or fabricated source ranges.
Executable recursion and source-shape proofs decrease the original source size.

Resolve/type/avoid every written element in its original caller scope. Evaluate
the head once, then the tail once in the same original names/environment with
the actual intermediate store. The result is right-associated, with no implicit
terminal Unit. Cost is head plus tail plus three existing pair transitions:
for a nonempty list it is the sum of child costs plus three per pair. Three and
four one-step leaves therefore cost nine and thirteen. Traversal has no extra
runtime cost. Unsupported children remain strict except where the existing
raw conditional/short-circuit semantics legitimately skip them.

Extend the existing generic resolution/typing, whole-shape, lowering, evaluation,
cost erasure/correspondence, determinism, safety, store replay, renaming,
unused-input, lookup and fuel proofs. Keep all 80 old public theorem statements
without stronger scope, uniqueness, typing, runtime-world or range premises.
Split the near-limit typing proof module through an import-compatible module
if needed, preserving each theorem's exact name/type and the old import path.

## Consumers and preserved boundaries

Independently construct arbitrary-length original lists, exact right-associated
Resolved/Core/value/type/cost evidence, and original-scope child evaluations.
Check explicit nesting and source order, arbitrary raw ranges and tables,
nominal static types, opaque actual values, strict missing children, whole versus
selected acceptance, owner/input/store transport and exact Core provenance.
Complete parsed tests must retain flat elements, original ranges and grouping,
not replace original source with generated nested binary syntax. Whole entries
retain parameter-only records, typed actual arguments, all fuel thresholds,
actual saved-environment/continuation checkpoints and genuine residual execution.

Explicitly rename the obsolete generic nonempty/nonbinary rejection to the true
manual-singleton/old-named-type boundary. Migrate the original parsed three/four
variable tuples, three/four Unit tuples and the existing three-variable return
expression into independent positives with fixed ordered Core and costs. Keep
all neighboring negatives. A many-element value against a binary product return
annotation remains a type mismatch; association and extra Unit are not coerced.

Manual singleton tuple nodes remain outside this canonical adapter because the
parser produces grouping there. Projection/index/array/call, shadowing, inference,
multiple return annotations, earlier named-only prefix adapters, Core/Resolved
definitions, parser, diagnostics, and Core Wire remain unchanged.
Run focused/aggregate builds, full tests, all public/consumer axiom audits,
kernel-policy and whitespace checks and independent reviews. Keep new proof and test files
under 300 lines, phase commits small and scratch repository-local.
