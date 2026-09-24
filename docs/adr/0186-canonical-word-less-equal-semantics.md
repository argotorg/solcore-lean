# ADR-0186: Canonical unsigned Word less-than-or-equal comparison

- Status: Accepted
- Decision date: 2026-09-08
- Scope: ordered derived Word `<=` in the monomorphic frontend

## Decision

Interpret canonical `Syntax.BinaryOp.lessEqual` (`<=`) as the resolved tree
`.unary .boolNot (.binary .wordGt left right)`, lowering exactly to the existing
`Core.Expr.wordLe` expansion. This is not a new binary primitive. Require Word
operands and return Bool `!(decide (leftWord > rightWord))`, using unsigned Word
order. Equal operands return true. No signed interpretation, Word-valued flag,
truthiness conversion, polymorphic ordering or swapped operand tree is implied.

Resolve and type both written children, including those under unselected paths.
Independent source evaluation remains strict left to right with initial,
intermediate and final stores. The sum of child costs plus five counts the
ordered greater-than comparison and its enclosing Boolean negation. Two leaves
leave the right Word under `binaryApply wordGt leftWord` and `unaryApply boolNot`
at fuel five; the greater-than Bool is pending under negation at six; the final
less-than-or-equal Bool is returned at seven. Preserve every frame and transition
even for equal or known values. Source fuel bounds add the same five transitions.

Extend independent resolution, typing, evaluation, costs, name avoidance,
identity renaming, unused-input and store-replay proofs. Compose the binary path
under the unary continuation and reflect both resolved nodes, preserving generic
safety, complete-run reflection, whole entry compilation and exact checkpoint
resumption. Keep existing public APIs, prior import paths and actual ordered
typed arguments; no dummy value, wrapper runner or acceptance assumption is added.

## Boundaries

The canonical parser already accepts `<=` at non-associative relational
precedence, above equality/inequality and below bitwise operators; do not modify
it. Chained relational forms remain parse failures. Mixed relational/equality
forms can parse but must satisfy the existing Word-only equality types. Source
calls, mutation, division/remainder, other orderings (`<` and `>=`), unary signs
and general overloads remain outside this unit. Diagnostic proofs remain paused.

## Validation

Independent consumers check arbitrary unsigned comparisons (including equality),
ordered exact lowering and costs, distinct fuel-five/six checkpoints and resumed
execution, structural bounds/store replay, wrong operand and return types, and
independent Bool entry compilation. Parsed consumers retain all tested parameter
positions, zero/high-bit/max boundaries, both argument orders, arithmetic and
short-circuit guards, whole unselected rejection, source precedence and exact
entry contracts. Migrate only the three current frontend semantic-negative `<=`
fixtures; leave parser/wire tests and other unsupported operators unchanged.

Register and audit each new public declaration, preserve standard-axiom-only
proofs and run focused/aggregate builds, full tests, kernel, forbidden
token and whitespace checks. Keep proof files below 300 lines and commits small
with exact paths. Scratch work stays inside the repository's ignored directory.
