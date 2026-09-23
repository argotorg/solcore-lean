# ADR-0158: Canonical local Boolean negation

- Status: Accepted
- Decision date: 2026-09-08
- Scope: additive Boolean negation in the internal local-expression adapter

ADR-0159 subsequently extends this internal adapter with Boolean `&&` and `||`
without changing the accepted negation semantics described here.
ADR-0161 later adds the distinct Word-only `~` operation; `!` remains Bool-only.

## Decision

Extend ADR-0156's internal canonical local-expression adapter with the
`Syntax.UnaryOp.logicalNot` (`!`) constructor. Resolve its operand recursively
and produce the existing `Resolved.Expr.unary .boolNot` expression. No new
Resolved or Core operator, value, type, or machine rule is needed. The
identifier/group-only reference adapter is unchanged.

Independent source typing requires a Boolean operand and assigns the Boolean
result type. Independent evaluation evaluates the operand once to a Boolean,
then returns its negation with the operand's final store. This is the existing
Core `boolNot` meaning from ADR-0011/0033, not implicit truthiness or a Word
complement. Outer and operator source ranges do not change the meaning.

The extension is a fixed monomorphic Boolean operation in this limited adapter,
not general source overload, class, or dictionary resolution. `true` and `false`
remain ordinary caller-bound identifier spellings. Numeric and string literals,
bitwise `~`, binary operators, calls, and other previously unsupported forms
remain unsupported. In particular, this step does not add `&&` or `||`.

## Preserved guarantees

The new constructor participates in the existing independent resolution,
typing, and dynamic relations. The checker remains sound and complete for the
extended fragment. Resolution gives exact evaluation correspondence with
Resolved/Core, including the value and both stores. Raw evaluation of `!`
requires a Boolean operand even without a whole-expression typing premise.

Typed aligned local environments still guarantee evaluation existence, value
type preservation, sufficient-fuel execution, and exclusion of machine faults.
The typed input bundle and its runner retain these guarantees automatically.
The unused-name judgment now follows the negated operand, so fresh insertion
also preserves negated expressions, their checked type, and Core free-index
weakening. Earlier accepted identifier/group/conditional expressions retain
their exact behavior; this is growth of an internal unsupported-input boundary.

## Resources and publication

Negation introduces the existing Core unary evaluation frame and application
transition. A named operand therefore takes three Core transitions: fuel two
is insufficient, and every fuel of at least three returns its negated value.
Grouping adds no Core transitions, and nesting follows the actual Core tree.
These are execution bounds, not parser/checker complexity or EVM gas.

This is not a new external source service or a change to any frozen publication.
Canonical parser behavior, Semantic Core constructors, and schemas remain
unchanged.

Tests cover both Boolean inputs, double negation, grouping and conditional
nesting, arbitrary source ranges, caller-controlled names, non-Boolean operands,
continued rejection of unsupported operators, the exact fuel boundary, bundled
input execution, and unused-name preservation. Source-text tests parse and
execute the actual checker-returned Core. All affected public proofs are
re-audited, with focused/aggregate builds, kernel/metadata checks, and full tests.
