# ADR-0231: Canonical empty tuple expressions denote Unit

## Status

Accepted for implementation.

## Context and evidence

ADR-0019 retains Unit as the Core nullary product, but leaves source syntax
outside its decision. ADR-0230 connects exactly binary canonical tuples while
leaving empty expressions unsupported. The syntax pin recorded in ADR-0153,
`18fd9f75d290df0070e21ee56e0a5691f232596f`, supplies relevant evidence:
`crates/parser/src/parse/expr_pat.rs` preserves empty tuple elements;
`crates/hir-ty/src/desugar.rs` maps an empty product to `ProductShape::Unit`;
`crates/hir-ty/src/infer/desugar_view.rs` assigns its existing builtin Unit type;
and `std/std.sol` contains explicit `return ();` expressions.

These fixed-revision observations support, but do not replace, the explicit
Lean semantic decision below. No moving upstream checkout becomes normative.

## Decision

The exact original expression `.tuple` with an empty delimited element list
denotes the existing resolved/Core unit expression, Unit type and unit value.
Add independent nullary `unit` constructors to source resolution, typing,
name avoidance, raw evaluation and exact-cost evaluation. The raw rule keeps
the same initial/final store and has cost one, matching the single existing
Core unit transition. Neither caller lookup, actual-value typing, row alignment,
name uniqueness nor source-span validity is required by this constant leaf.

Extend resolution, direct evaluation and the source fuel bound with this exact
empty case. Extend all generic static, dynamic, renaming, fresh-input, store,
cost and evaluator correspondence proofs with unchanged public contracts.
Core, resolved semantics and existing recursive body/entry gates remain unchanged.
Use the original parsed syntax and ranges without a parser rewrite or allocator.

Empty and two-element tuple expressions now have independent nullary/binary
product meanings. Explicit nesting retains each binary pair; `((), ())` is a
pair of units, not unit. Grouping, including existing singleton parenthesized
syntax with trailing commas, preserves its child's meaning and costs no step.
Manually constructed singleton tuple nodes and three-or-more-element tuples
remain unsupported; no implicit larger-product nesting convention is selected.

## Boundaries

This adds an expression meaning, not tuple type syntax or a reserved type-name
meaning. Existing caller type aliases may denote Unit, and omitted return
annotations retain their existing Unit gate. Explicit empty return annotations,
multiple returns, projections and other unsupported syntax remain unchanged.
An identifier spelled `Unit` still performs ordinary caller lookup.

Whole checking continues to inspect all written children. True-and/false-or
can forward a selected raw unit value while whole Boolean typing rejects it;
do not add an actual Boolean-result premise to those raw rules. Unit initializes
strict lets normally, without removing their two Core binding transitions.
Diagnostics, Core/resolved semantics, parameter layout and frozen wires do not change.

## Validation

Construct independent source and Core evidence for arbitrary caller rows/spans,
the one-step constant, nested unit/products, grouping, selected/raw-versus-whole
boundaries, store replay, exact fuel and genuine checkpoints. Test complete
parsed Unit-return entries, typed lets, unused actual arguments, named aliases
and wrong return types. Migrate the former expression-empty negative and the
general unsupported-arity consumer to exclude both supported arities zero/two;
add independent empty positives. Keep `returns(Pair){return ();}` rejected by
return typing, along with empty type/header and other unchanged negatives.
Run focused/aggregate builds, full tests, public/consumer axiom audits,
kernel/metadata/whitespace checks and independent reviews. Retain proof files
below 300 lines, separate small commits, paused diagnostics and repository scratch.
