# ADR-0233: Structural single-return annotations at the existing entry

- Status: Accepted for implementation
- Decision date: 2026-09-09
- Scope: Shared return/header gate; parameters and let annotations stay named-only

## Context

ADR-0232 provides independently specified structural type interpretation while
retaining the old named-only API and its whole-type table membership contract.
The existing compile, prepare and run entry paths already share one return/header
gate. Connecting that gate makes structural return annotations executable without
a parallel compiler, new Core values or parameter-layout changes.

ADR-0170 accepts exactly one explicit return annotation, or an absent clause as
Unit. Preserve that clause-list policy and the nongeneric/no-where/no-public/
no-payable restrictions. Only the meaning of the one written annotation expands.

## Decision

Change `RuntimeReturnTypeDenotes.single` to take independent
`StructuralTypeDenotes` evidence, and interpret that one annotation with
`interpretStructuralType?`. This constructor premise is an intentional documented
semantic widening. Old named-only evidence remains valid through
`TypeNameDenotes.structural`; the old named-only relation/interpreter and its
membership law themselves do not change.

An explicitly written `returns(())` contains one empty tuple type and denotes
Unit. A single parenthesized named type denotes its child; a single binary tuple
annotation denotes an ordered product, retaining explicit nested association.
No spelling is reserved and all named leaves use the caller's original exact
first-match table. Types need no runtime inhabitants for static compilation.

An absent clause still denotes Unit. Explicit `returns()` contains no annotation
and remains unsupported; `returns(Word,Bool)` contains two annotations and remains
unsupported. These are not identified with `returns(())` or
`returns((Word,Bool))`. Larger type tuple lists and other unsupported structural
type constructors retain the ADR-0232 boundary.

## Preserved contracts

Retain the seven general return/header correspondence, uniqueness, rejection
and semantic-extension theorem names and statements. Their existing consumers
receive the new accepted cases through the same independent header relation.
Only the small shared definition/bridge and the structural extension import
need change; do not redefine compilation, parameter binding, Core construction,
runtime evaluation, cost, fuel bounds or resumption.

Parameters and typed let annotations still use the old named-only adapter;
tuple annotations there remain rejected. Exact original source/ranges, parameter
identity/order, reversed actual environments, complete records and whole-body
checking stay unchanged. New return types add no Core steps. Same-typed wrong
Core is not correct compilation. Raw selected evaluation remains distinct from
whole-header/body acceptance. Diagnostics, Core/resolved semantics and frozen
wire formats do not change.

## Validation

Construct independent structural header, original body and fixed Core evidence
for Unit, singleton, ordered/nested products, typed strict lets and conditionals.
Exercise actual complete parsed declarations, arbitrary/nominal static types,
opaque actual values, exact costs, both stores and real checkpoints/resumption.
Check all old parameter/argument/header gates with otherwise valid inputs.
Migrate only previously rejected structural return annotations into independently
checked positives; retain empty/multiple clauses, structural parameter/let
negatives and all unrelated rejected cases. Legacy named-only proof consumers
may explicitly transport their old evidence with `.structural`; do not weaken
their generic theorem headers.

Run focused and aggregate builds, full tests, all old/new public and consumer
axiom audits, kernel/metadata/whitespace checks and independent reviews. Keep
files below 300 lines and phase commits where possible; the existing combined
header module requires a one-line exactness bridge update with its definition.
Use repository-local scratch and leave paused diagnostics untouched.
