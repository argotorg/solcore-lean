# ADR-0189: Typing reflection for local Core environment insertion

- Status: Accepted
- Decision date: 2026-09-08
- Scope: static counterpart of the local Core evaluation insertion theorem

## Decision

For `Core.Expr.LocalFragment`, prove retained-prefix typing equivalence between
`expr.weakenAt leading.length` under `leading ++ insertedType :: suffix` and
`expr` under `leading ++ suffix`. Retain the same result type and arbitrary
data definitions. Under a let, extend the prefix with the recovered bound type.
Expose empty-prefix equivalence and directional preservation/reflection helpers.
Prove directly from the independent Core predicate and Core typing, with no
Resolved dependency, original-scoping or runtime-environment premise.

Use the typing equivalence and checker soundness/completeness to show literal
equality of `Core.infer?` results under the two contexts. This includes both
successful inference and rejection; insertion cannot enable a missing positional
reference when its index is correctly shifted. No inhabitant, well-formedness or
runtime allocation assumption is imposed on the inserted type or context types.

## Boundaries

Use an explicit retained prefix, not unrestricted `Context.insertAt` reflection:
the latter clamps an out-of-range position to the end, whereas weakening uses
the requested position. Inserting into an empty context at cutoff one can thus
enable an unshifted variable zero. Do not drop or weaken this position boundary.

Keep the predicate's whole-expression requirement, including all unselected
conditional children. Evaluation of a selected branch does not imply typing of
the whole conditional. Keep this unit local even though more general Core typing
preservation already exists. Do not change constructors, parser, resolver ID-map
contracts, supported canonical operators or executable semantics. Exact-cost
insertion, canonical `<`/`>=` support and diagnostic proofs remain separate.

## Validation

Independent consumers cover every local form, arbitrary retained prefixes and
inserted types, nested lets, successful inference/reflection, missing references,
rejected primitives and unselected ill-typed branches. Include an opaque nominal
context type without inventing a runtime inhabitant, a lowered Resolved term,
and counterexamples for unshifted lookup and clamped insertion positions.

Register and audit all new public declarations and consumers. Run focused and
aggregate builds, full tests, standard-axiom, kernel, metadata, forbidden-token
and whitespace checks. Keep proof files below 300 lines, use small exact-path
commits and repository-local scratch, and preserve paused diagnostic files.
