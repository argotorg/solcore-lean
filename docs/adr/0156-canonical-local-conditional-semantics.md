# ADR-0156: Canonical local conditional semantics

- Status: Accepted
- Decision date: 2026-09-08
- Scope: explicit-table identifier, grouping, and conditional expression fragment

ADR-0158 subsequently extends the internal adapter and these semantic
guarantees with fixed Boolean negation; existing supported inputs are unchanged.

## Decision

Extend the canonical frontend semantic boundary with a separate local-expression
adapter. It supports identifiers, grouping, and the canonical
`condition ? thenBranch : elseBranch` AST constructor. It preserves the existing
AST nesting and lowers the conditional structurally to `Resolved.Expr.ifE`.
All three children use the same explicit caller-supplied name table. The earlier
local-reference adapter remains unchanged and continues to exclude conditionals.

Identifier spelling and first-match name/identity tables retain ADR-0155's
contracts. Grouping is transparent. Neither the outer source range nor question
and colon ranges select names or change meaning. The adapter consumes an existing
AST; it does not parse text or revalidate lexical and source-span invariants.

The condition must have the existing Core Boolean type, and both branches must
have exactly the same Core type. There is no truthiness conversion, implicit
coercion, overloading, or branch-type join in this fragment. The result has that
common branch type. `true` and `false` are still ordinary caller-bound names,
not newly introduced source literal constructors.

Evaluation first evaluates the condition, then only its selected branch, following
ADR-0009. The fragment is pure: evaluation preserves the store exactly. Independent
source rules specify typing and evaluation; neither relation is defined by the
checker or executor. All three children must resolve and type-check statically,
even though dynamic evaluation inspects only one branch. In particular, an
independent evaluation can exist when an unselected unsupported or unmapped
branch prevents whole-expression elaboration.

## Correspondence and resources

The total adapter returns a Core expression and its checked type. Successful
elaboration corresponds exactly to independent source typing and structural
resolution/lowering. No absent name receives a default index, and a missing
first selected identity does not trigger a retry of later name-table entries.

For structurally resolved expressions, independent canonical evaluation agrees
with resolved evaluation. For checked elaborations, matching identity order
between the runtime environment and type context then gives exact Core
evaluation correspondence, including the value and both stores. Equal lengths
or positional value typing alone do not replace the identity-order premise.
With a typed, identity-aligned environment, evaluation exists and preserves the
result type; all sufficiently large Core fuel amounts return that value.

Fuel counts Core machine transitions, not parsing, name lookup, AST traversal,
or EVM gas. Grouping introduces no Core node. Unselected branch size does not
add execution transitions. Exhaustion is inconclusive, not source rejection.

## Deliberate limits and validation

This is an additive Lean library fragment, not a whole-language type checker
or source-text execution service. An absent adapter result denotes unsupported,
unmapped, or ill-typed input for this fragment; it is not a universal language
verdict. Source scope construction, declaration traversal, global ID allocation,
numeric/string literals, operators, calls, mutation, and staging remain separate.
Existing parser behavior, Core constructors, Oracle versions, and wire bytes do
not change.

Tests cover both branch choices, nested/grouped ASTs, exact local positions,
non-Boolean conditions, branch-type disagreement, static checking of unselected
branches, repeated names and identities, source-range independence, and exact
Core fuel boundaries. Independent evaluation of a statically unsupported
unselected branch protects the whole-resolution premise in correspondence.
Public declarations receive kernel checks, axiom audits, and boundary consumers;
focused and aggregate builds and the full test suite validate integration.
Additional executable regressions begin with source strings, require complete
diagnostic-free expression parsing, and execute the checker-returned Core.
The older reference adapter is proved to embed with identical resolution,
checked results (including missing-context failure), values, and stores.
