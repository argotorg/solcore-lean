# ADR-0159: Canonical local short-circuit Boolean semantics

- Status: Accepted
- Decision date: 2026-09-08
- Scope: additive `&&` and `||` in the internal local-expression adapter

ADR-0161 later adds Word-only `~`; the short-circuit semantics and Boolean
typing requirements here remain unchanged.

## Decision

Extend ADR-0156/0158's internal adapter with canonical binary
`Syntax.BinaryOp.logicalAnd` and `logicalOr`. Both operands resolve recursively.
Use exactly the existing conditional expansion fixed by ADR-0011/0026:

```text
resolve(x && y) = ifE resolve(x) resolve(y) (bool false)
resolve(x || y) = ifE resolve(x) (bool true) resolve(y)
```

These are ordinary Resolved/Core conditionals, not new eager primitives or new
expression tags. The inserted Boolean values are internal constants, never
lookups of source spellings. Caller bindings named `true` and `false` retain
their usual meaning and cannot change the inserted constants. Operator and
outer source ranges carry no semantic meaning.

Independent source typing requires both operands to have Boolean type and gives
a Boolean result. The checker resolves and checks the whole expression even
when the right operand would be skipped. Missing names, unsupported syntax, or
wrong types in that operand therefore prevent checked execution.

## Independent evaluation and the unchecked boundary

The left operand is evaluated once to a Boolean. Conjunction evaluates the
right operand only when that Boolean is true; disjunction does so only when it
is false. A selected right operand starts at the left operand's final store and
forwards its resulting value and store. Otherwise evaluation returns the fixed
Boolean false/true and the left operand's final store.

As with raw conditional evaluation, these rules intentionally describe the
untyped expansion too: a selected right operand may forward a non-Boolean
value when no source typing premise is assumed. This is not truthiness,
coercion, or acceptance of an ill-typed program. The left operand must still be
Boolean, both operands must be Boolean in source typing, and checked execution
can only return a Boolean. Keeping this distinction explicit preserves exact
resolution-only correspondence with raw Resolved/Core evaluation. A raw
evaluation may also skip a missing or unsupported right operand even though
whole resolution and checking fail.

## Guarantees and tests

Extend the existing independent resolution, typing, evaluation, determinism,
type/store preservation, and execution proofs. Typed aligned inputs retain
evaluation existence, sufficient fuel, and absence of faults. Unused-name
avoidance follows both operands, including a skipped operand, preserving its
existing resolution, typing, evaluation, and checked Core weakening laws.

Tests cover all Boolean pairs; exact expansions and caller-controlled names;
selected and skipped right operands; non-Boolean rejection and the raw-value
boundary; missing/unsupported skipped syntax; nested negation/conditionals;
exact fuel for selected/skipped paths; and unused input insertion. Parsed text
tests execute the actual checked Core, including operator precedence and
grouping. Public declarations are audited using only standard kernel axioms.

Existing accepted inputs keep their exact behavior. Other binary operators,
bitwise `~`, literals, calls, source declarations, overload resolution, and
implicit truthiness remain outside this adapter. The reference-only adapter,
canonical parser, Core machine, Wire versions, and schemas do not change. This
is not a new source execution service.
