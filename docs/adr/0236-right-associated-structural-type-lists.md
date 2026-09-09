# ADR-0236: Right-associated structural type lists

- Status: Accepted for implementation
- Decision date: 2026-09-09
- Scope: Arbitrary finite tuple-type arity at the existing structural adapter

## Primary reference and context

Use canonical PR-20 syntax and the existing local reference pin
`18fd9f75d290df0070e21ee56e0a5691f232596f` of `argotorg/solcore-rs`.
`crates/parser/src/parse/types.rs:73–80,136–140` retains every written tuple
element, including singleton and trailing-comma forms. In
`crates/hir-ty/src/desugar.rs:71–108,1070–1077`, type products use source-order
`ProductShape::from_slice`: zero elements are Unit, one is the element, and
longer lists are head paired with the recursive tail. The type-specific
`crates/hir-ty/src/lower.rs:211–214,703–718` independently confirms this rule.
Thus `(A,B,C)` means `A × (B × C)`, not `(A × B) × C` and not a product
terminated by an extra Unit.

ADR-0232 already interprets zero/one/two-element type lists. ADR-0233–0235
connect that shared meaning to single-return headers, original parameters and
recursive typed lets. Supporting longer type lists needs no new entry API or
runtime representation.

## Decision

Extend only the structural type interpreter and independent meaning relation.
Keep the existing named, Unit, singleton and binary constructors and equations.
Add one `many` rule exclusively for three or more elements: its premises give
the first original element's meaning and the remaining list's product meaning;
its conclusion is the ordered product of those two types.

The recursive tail occurrence reuses the original outer span and untouched
remaining elements. This is a decomposition of the original type, not a parser
rewrite, source replacement or flattening of explicitly nested children.
Use decreasing source size for executable interpretation and soundness. For
outer-span independence, recurse on the tail with its original span before
transporting it to the arbitrary replacement span.

Extend complete/sound and semantic-extension proofs with the new case. Retain
all 13 generic theorem statements, including exact optional rejection, unique
meaning, arbitrary outer ranges, first-match lookup congruence, successful
one-way extension and full optional equality under mutual extension. Every
written leaf still uses the same caller table. Missing leaves remain strict;
no spelling becomes reserved and no nominal inhabitant is manufactured.

## Existing boundaries and consumer migration

The old named-only API and whole-result table membership stay unchanged.
Each original parameter still consumes one original typed argument and row,
even when its annotation is Unit or a many-element product. Single annotations
remain distinct from empty/multiple return-clause lists. Recursive lets retain
strict old-scope initialization, fresh tail-only binding and complete arm checks.

Two obsolete generic source rejections must be explicitly renamed: preserve
the true old named-only tuple rejection and missing-child conjuncts in one,
and absent/single-Unit versus multiple-return-list rejection in the other.
Replace their false structural-arity claims with separately justified positive
coverage. Migrate the original parsed triple/quadruple types and triple parameter
declaration into independent positives without dropping neighboring negatives.
Existing triple annotations paired with binary or left-associated actuals or
initializers remain rejected for type mismatch, not unsupported arity.

Add independent arbitrary-length, ordering, explicit-association, span, table
and nominal source consumers. Complete parsed consumers must check the original
flat annotation elements and nested child ranges, not only a computed type.
Whole entries use separately specified exact Core, typed actual arguments,
values, costs, stores and real checkpoint/resumption paths. Explicitly nested
binary expressions can supply these products without broadening expression syntax.

No tuple-expression arity, projection, inference, shadowing, call, Core transition,
fuel bound, parser, diagnostic, wire format or broader language policy changes.
Validate focused and aggregate builds, full tests, all public/consumer axioms,
kernel/metadata/whitespace and independent reviews. Keep files under 300 lines,
commits small and scratch repository-local; leave paused diagnostics untouched.
