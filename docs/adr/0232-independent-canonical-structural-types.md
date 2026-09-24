# ADR-0232: Independent canonical structural product types

- Status: Accepted for implementation
- Decision date: 2026-09-09
- Scope: A separate monomorphic type adapter, before entry integration

## Context and evidence

ADR-0167 deliberately restricts `interpretTypeName?` and `TypeNameDenotes`
to named types without arguments. Its public `TypeNameDenotes.mem` contract
states that the whole interpreted type occurs in the caller table. Extending
that relation with structural Unit/products would falsify this contract, even
for an empty table. Preserve that API and every existing consumer unchanged.

The fixed canonical pin from ADR-0153,
`18fd9f75d290df0070e21ee56e0a5691f232596f`, provides supporting evidence:
`crates/parser/src/parse/types.rs` preserves all parenthesized type element
lists, including a singleton; `crates/hir-ty/src/desugar.rs` records tuple
types with `ProductShape::from_slice`, whose Unit/Single/Pair cases interpret
zero/one/two elements as unit/the child/an ordered pair. The current canonical
Lean type parser likewise retains `.tuple [child]`, unlike expression grouping.
These observations motivate the explicit Lean decision; upstream is not normative.

## Decision

Add `interpretStructuralType?` and independent `StructuralTypeDenotes`
over the original canonical `Syntax.TypeExpr`. Use four independent rules:
named/no-arguments with the existing first-match table relation, empty tuple
as Core Unit, singleton tuple as its child's type, and exactly binary tuple
as the ordered product of its two child meanings. All recursive children use
the same original caller table; no source rewrite, flattening or allocation
is performed. Explicit nested products preserve their association.

Only these recursive shapes belong. Larger tuple lists, named applications,
mapping, proxy, function, comptime and recovery errors return none. Three-or-more
element product conventions remain a separate decision, even though the pin
also supplies evidence for right-nested larger products. No spelling is reserved;
named leaves may denote arbitrary Core types, including nominal types with no
runtime inhabitants. Exact qualified components, duplicate first matches and
arbitrary raw occurrence ranges retain the named-only policy.

Prove total interpretation soundness, completeness, unique meaning and exact
success/failure against the independent rules. Connect old named-only meanings
and successful results to the new adapter without weakening the old contract.
Prove outer-range invariance, whole optional-result lookup extensionality,
successful transport under semantic table extension and full equality under
mutual extension. One-way extension must not imply preserved rejection.
Do not claim whole structural results are entries in the caller table.

## Boundaries and next integration

This prerequisite adds an opt-in type interpretation API, not a second syntax
tree or a new Core type. Existing parameter declarations, initialized-let
annotations, function return/header gates and runtime entry functions continue
to use the old named-only adapter in this change. Their tuple-type rejection
tests stay unchanged. A subsequent separately scoped integration must transport
those independent contracts and preserve original source/parameter records.
Expression arities and evaluation, Core/resolved semantics, diagnostics, parser
ranges, source module policy, and Core Wire remain unchanged.

## Validation

Independent source and complete parsed-type consumers cover arbitrary nested
Unit/singleton/products, exact ordered Core types, same-shaped wrong meanings,
qualified and duplicate names, absent leaves, nominal non-inhabitation, invalid
raw spans and every unsupported constructor. Check actual parenthesized type
nodes and trailing commas rather than inventing expression group nodes.
Contrast old named-only rejection with new structural acceptance and test old
entry rejection explicitly. Cover safe append/prepend, meaning-changing
shadowing, and newly enabled names under one-way extension. Run focused and
aggregate builds, full tests, old/new public and consumer axiom audits,
kernel-policy and whitespace checks and independent reviews. Keep proof files
under 300 lines, commits small and phased, diagnostics paused and scratch local.
