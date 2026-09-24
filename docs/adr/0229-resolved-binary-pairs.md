# ADR-0229: Ordered binary products in resolved expressions

## Status

Accepted for implementation.

## Context

Core binary products already have ordered evaluation. ADR-0228 makes pair
construction available to the independent local-fragment insertion theorems.
The resolved immutable-expression layer still lacks a representation for pairs,
so a canonical two-element tuple cannot yet use its generic frontend bridges.

## Decision

Add `Resolved.Expr.pair left right` and matching independent lowering, typing,
whole-scope and evaluation constructors. Lower both original children in the
same scope to the existing ordered `Core.Expr.pair`. Pair component types are
arbitrary and determine the existing binary product type. Raw evaluation uses
the same input environment for both children, threads the initial/intermediate/
final stores in left-to-right order and returns their actual ordered pair value.

Extend structural ID renaming with both children. Preserve the existing total
checker definition as lowering followed by Core inference. Extend all generic
lowering/checking, typing, whole-scope, Core-evaluation correspondence, store,
determinism, renaming and fresh-insertion/reflection proofs through the pair
case, retaining existing theorem names, statements and assumptions.

The structural ID-map laws keep arbitrary maps. Semantic first-match transport
keeps its existing injectivity requirement. Duplicate identities retain first
match. Fresh insertion keeps its existing suffix-fresh boundary; reflection
keeps original whole-scoping. A pair creates no binder, so it adds no freshness
or allocation requirement and the right child never inherits a left-local let.

The structural lowering-to-local-fragment bridge uses ADR-0228's pair constructor.
Keep the Core-to-Resolved-to-Frontend dependency direction. Existing execution
wrappers and ordered Word-comparison builders should inherit the case without
new cost judgments, runtimes, evaluator or hidden LocalId allocation.

## Boundaries

Static product types require no runtime inhabitants. Nominal component types
can type open expressions even when no actual value has that type under the
existing empty data environment. Untyped raw component values may contain
opaque closures, cell references or constructors without executing them.

Both written children must lower and type; raw selected conditional paths can
still skip an unresolved or ill-typed arm. Product construction does not weaken
the existing distinction between raw success and whole acceptance. Wrong
ordered Core output is not accepted merely because it has the same type.

Do not change Core semantics, canonical expression acceptance, source type-name
interpretation, runtime-entry gates, parsing, diagnostics, or Core Wire.
Canonical two-element tuple integration is the next separate adapter step;
empty/larger tuples, tuple type syntax, projection spelling and multiple returns
are not decided or enabled here. Existing source tuple negatives remain valid.

## Validation

Independent proofs and executable boundary consumers must fix exact ordered
Core, values and types for nested pairs/lets, duplicate first matches, raw/whole
contrasts, arbitrary structural maps versus injective semantic maps, and fresh
insertion/reflection boundaries. Use independently constructed Core paths for
pair cost five, nesting and actual checkpoints/resumption; retain both stores
and distinguish wrong same-typed output. Include nominal static/opaque raw
examples without manufactured inhabitants or typing premises.
Run focused/aggregate builds, full tests, old/new public and consumer axiom
audits, kernel-policy and whitespace checks and independent reviews. Keep proof
files below 300 lines and definitions, proofs, consumers and publication in
separate small commits. Preserve all paused diagnostics and repository scratch.
