# ADR-0188: Exact environment insertion for the local Core fragment

- Status: Accepted
- Decision date: 2026-09-08
- Scope: independent untyped insertion/reflection prerequisite for frontend lowering

## Decision

Define an independent `Core.Expr.LocalFragment` predicate for exactly unit,
Bool, Word, variable, unary primitive, binary primitive, let and conditional
forms. Require every syntactic child, including unselected branches. This
predicate describes syntax, not typing, scope validity or successful execution.
It excludes closure creation/application, cell operations and other Core forms.
An existing closure or cell reference may still be returned as an arbitrary
runtime value; the fragment cannot create/call closures or access cells.

Prove closure under positional weakening and an independent retained-prefix
evaluation equivalence: evaluating `expr.weakenAt leading.length` under
`leading ++ inserted :: suffix` has exactly the same value and both stores as
evaluating `expr` under `leading ++ suffix`. Prove directly on Core syntax and
evaluation, without depending on Resolved correspondence. Under a let, extend
the retained prefix with the actual bound value. Expose useful empty-prefix
preservation/reflection corollaries without adding type or runtime-world premises.

No freshness or original-scoping premise is required: positional shifting also
preserves missing lookups, unlike inserting a named binding that can enable an
absent name. Runtime values and stores are arbitrary and unchanged literally,
not merely related by a renaming relation. Connect existing `Resolved.Lowers`
to this structural predicate in a separate small bridge. This direction is
acyclic, so future resolved lowering proofs may consume the Core theorem.

## Boundaries

Do not change Core or Resolved constructors, runners, supported canonical
operators, parser, wire formats or existing resolver identity-map guarantees.
`Expr.CellFree` alone is not sufficient: it permits lambda/application, and a
lambda captures the inserted environment even without writing a store. Do not
claim exact insertion for arbitrary effectful Core or unrestricted closures.
This unit proves successful evaluation equivalence, not equality of intermediate
machine states, exact-cost transport, typing reflection or canonical `<` support.
Diagnostic proofs remain paused.

## Validation

Independent consumers cover every local form, arbitrary retained prefixes,
insertion at nonzero depth, nested lets and shadowing indices, selected and
unselected conditional children, arbitrary returned runtime values, and missing
variables on both sides. Consume the Resolved lowering bridge. Explicit boundary
tests distinguish the local predicate from CellFree, show a lambda's changed
captured environment, and show that an unshifted free variable reads the wrong
value. Keep full suspended states distinct instead of asserting state equality.

Register/audit every new public declaration, including predicate constructors.
Run focused and aggregate builds, full tests, and standard-axiom, kernel-policy,
forbidden-token, and whitespace checks. Use small exact-path commits, proof files below
300 lines and repository-local scratch. Preserve all paused diagnostic files.
