# ADR-0345: Collision-free program trait and implementation identities

## Status

Implemented as the identity boundary for compiler-provided trait evidence.

## Context

Whole-program trait predicates and implementation evidence previously used
`Resolved.DeclarationId` directly.  That is sufficient while every trait and
implementation comes from source, but the target-compatible numeric-literal
path needs a compiler-provided `Int` trait and primitive implementations which
have no source declaration.  Assigning them invented declaration IDs would
allow collisions with real modules and would make source-catalog lookup appear
valid for entries that have no source body.

## Decision

Represent program-wide trait and implementation identities as disjoint sums:

- `ProgramTraitId.builtin` or `ProgramTraitId.declaration`;
- `ProgramImplId.builtin` or `ProgramImplId.declaration`.

The builtin namespaces initially reserve `Int`, `Int<integer>`, and
`Int<Word>` identities.  This ADR does not yet install their resolution rules.

There is a one-way coercion from `Resolved.DeclarationId` into each program
identity so source signature construction remains concise.  There is no
reverse coercion.  Consumers that require source declarations must use the
explicit `declaration?` projection and handle the builtin case.

`ProgramPredicate`, `ProgramImplRule`, typed trait resolution, retained
evidence, and inconclusive-search reports now carry the tagged identities.
Source trait and implementation catalogs keep their original declaration IDs,
including trait-method and implementation-method ownership.

The source-method executor and the operator/coercion linker remain source-only
boundaries.  They reject builtin trait or implementation evidence explicitly
rather than attempting a source-catalog lookup or fabricating a method body.

## Consequences

Builtin and source traits cannot match merely because a declaration happens to
reuse an index or spelling.  Evidence retains whether its implementation is a
compiler primitive or a source declaration, while all existing source trait
resolution and executable-method behavior remains unchanged.

The next slice may prepend primitive `Int<integer>` and `Int<Word>` rules to a
combined resolution view without changing source catalog counts.  Literal
inference and Core execution remain separate later changes.

## Verification

Regression tests prove declaration projection, constructor injectivity,
builtin/source disjointness, non-crossing head matching, and preservation of
the selected implementation tag.  Existing source signature, inference,
method execution, and direct-linking tests continue to pass.  Dedicated tests
also confirm that builtin evidence is rejected at the source-only method
boundary.
