# ADR-0230: Canonical binary tuple expression semantics

## Status

Accepted for implementation.

## Context

Canonical expression syntax already retains delimited tuples in written order.
Core and resolved binary products have independent ordered semantics and the
local-fragment insertion prerequisites (ADR-0228 and ADR-0229). The frontend
adapter still rejects every tuple, preventing this existing representation from
flowing through the checked expression and recursive runtime-entry bridges.

## Decision

Accept precisely a canonical `.tuple` whose original delimited elements are
`[left, right]`. Resolve both original children with the same caller name table,
and lower them to the ordered resolved/Core pair. Preserve all original spans
and syntax; the parser already restores written order, so do not reverse or
rewrite elements in this adapter. Name the five independent source constructors
`pair` in resolution, typing, name avoidance, raw evaluation and cost evaluation.

Both children use the same original context/environment. Product types are the
existing binary product of arbitrary child types. Raw evaluation is strict and
left-to-right, threads initial/intermediate/final stores, and retains the actual
ordered child values without requiring runtime typing. Its exact Core cost is
left cost plus right cost plus three; the structural fuel bound uses the same
composition. Extend the total direct evaluator by original-syntax recursion,
returning the same ordered value and cost without consulting the checker.

Extend existing generic resolution/checker, typing, name avoidance, renaming,
fresh insertion, raw/Core correspondence, store/safety, exact-cost, fuel-bound,
lookup-extensionality and direct-evaluator proofs with unchanged public names
and premises. Keep proof modules below 300 lines; if a split is needed, preserve
the old import path through re-export and retain every public theorem statement.
The recursive body, function-entry and execution layers should inherit the
expression case through their existing generic contracts, without new gates,
allocators, runners or argument-layout policies.

## Boundaries

Accept explicitly nested binary tuples, not an invented nesting convention for
larger tuples. Existing parser grouping and trailing-comma behavior is unchanged:
`(x)` and `(x,)` are groups, while `(x, y,)` has the same two tuple elements.
Empty, manually constructed singleton, and three-or-more-element tuples remain
unsupported. Arrays, tuple type syntax, projections and multiple return
annotations remain outside this adapter. A caller-provided named type alias may
denote an existing product without introducing tuple type syntax.

Whole lowering and typing still inspect both children and all written branches.
Raw conditionals and short-circuit operators retain their selected-path rules;
in particular the existing true-and/false-or rules may forward an arbitrary raw
pair value even when whole Boolean checking rejects that expression. Do not
strengthen those rules with an actual-value typing assumption. Opaque values,
nominal static types, duplicate first matches and existing freshness/alignment
boundaries retain their old meaning. Parsing, diagnostics, Core semantics,
resolved semantics and Core Wire are unchanged.

## Validation

Use independent original-syntax resolution/type/raw/cost and fixed Core path
certificates, including ordered and nested pairs, grouping/trailing commas,
arbitrary raw values, nominal types, strict/missing children, raw/whole contrasts,
freshness, renaming, real checkpoints and exact residual fuel. Migrate existing
two-element tuple negatives to independently justified positives, while retaining
unsupported arity/type/projection/entry negatives. Exercise actual parsed function
entries through a named product alias, preserving original parameter positions.
Run focused/aggregate builds, full tests, old/new public and consumer axiom
audits, kernel-policy and whitespace checks and independent reviews. Separate
definitions, proofs, consumers and publication in small commits. Leave paused
diagnostics untouched and keep scratch files inside the repository.
