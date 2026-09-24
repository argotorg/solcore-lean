# ADR-0234: Structural parameter declarations and actual bindings

- Status: Accepted for implementation
- Decision date: 2026-09-09
- Scope: Atomic static/runtime parameter annotation integration

## Context

ADR-0232 independently specifies structural types; ADR-0233 connects the single
return annotation to that interpretation. Parameter declarations and actual
bindings still use named-only annotations. Extending just one side would break
the existing erasure/restoration and preparation-factorization contracts: an
empty-tuple parameter with a typed Unit argument is already a counterexample.

## Decision

Use `StructuralTypeDenotes` and `interpretStructuralType?` in both parameter
adapters at once. Intentionally widen the annotation premises of
`RuntimeParametersDeclareFrom.cons`, `RuntimeParametersBindFrom.cons`,
`RuntimeParameterDeclarationRow.typed` and `RuntimeParameterRow.typed`.
Likewise, the annotation-meaning conclusions of `RuntimeParametersDeclare.position`
and `RuntimeParametersBind.position` become structural. These six public
contracts change meaning; this is not merely a proof repair.

Keep all other general theorem statements, including exact correspondence,
rejection, freshness, source positions, layout, typed-argument restoration,
value erasure and preparation factorization. Named-reference and named-selector
specializations keep their existing `TypeNameDenotes` premises and explicitly
transport that evidence internally. The old named-only API and its membership
law do not change.

Unit, singleton and ordered binary product annotations follow ADR-0232,
recursively retaining written association. Each original parameter remains
exactly one parameter, row, identity and actual argument: do not flatten products
or omit Unit arguments. Named leaves use the original caller-owned exact
first-match table. Arbitrary nominal types require no inhabitants for static
declaration, while every supplied actual value must still have its declared type,
even if the function never references that parameter.

Preserve original syntax and spans, left-to-right identity allocation, fresh
owner-relative identities for arbitrary initial rows, and the one reversal into
Core contexts/environments. Duplicate names, count/type mismatches, untyped or
otherwise unsupported parameter syntax, unknown leaves and unsupported structural
constructors remain rejected. Larger tuple type lists stay outside this slice.

Typed let annotations remain named-only. Header clause policy, whole-body
checking, Core/resolved semantics, execution, costs, fuel, checkpoints, diagnostics
and Core Wire do not change. No parallel compiler or argument layout is
introduced.

## Consumer migration

Move the three previously rejected parsed Unit/singleton/product parameters and
the value-free product declaration into independently checked positives. Preserve
all unrelated negative examples with valid argument counts and types.
The old source theorem rejecting every tuple parameter is no longer true: replace
its parameter claim with the unchanged old named-only interpreter boundary,
rename it accurately, retain its let rejection, and add independent positive
declaration/binding coverage. This is an explicit consumer contract migration.
The fixed three-named-parameter position consumer retains its old named-only
conclusion by recovering the original annotation shape.

## Validation

Construct independent original-annotation and declaration/binding evidence with
exact bundles, positions, inverse argument order, erase/restore correspondence,
sparse/mixed-owner initial rows and semantic table extensions. Include arbitrary
nominal static types and opaque actual values without inventing inhabitants.
Exercise complete parsed entries with separately specified Core, values, costs
and paths, both stores, fuel boundaries and real checkpoint resumption. Check
unused parameters, Unit argument retention, single product arguments, wrong
arity/order/association, and same-typed incorrect Core provenance.

Run focused/aggregate builds, full tests, old/new public and consumer axiom
audits, kernel-policy and whitespace checks and independent reviews. Use
repository-local scratch; leave paused diagnostics untouched. Keep new proof
files below 300 lines and phase commits where possible; existing combined
definition/exactness modules require their bridge repairs in the definition phase.
