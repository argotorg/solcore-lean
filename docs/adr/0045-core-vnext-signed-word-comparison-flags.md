# ADR-0045: Derive word-valued signed comparison flags

- Status: Accepted
- Decision date: 2026-08-27
- Scope: twenty-seventh internal Semantic Core vNext slice
- Implementation: Complete

## Context

ADR-0043 provides boolean signed greater-than, and ADR-0044 derives boolean
signed less-than without reversing source evaluation. Internal semantic
composition also needs canonical word-valued results, but it does not need
another primitive or operation tag.

## Decision

Add two derived builders with these exact expansions:

```text
wordSgtFlag(left, right) = boolToWord(binary wordSgt left right)
wordSltFlag(left, right) = boolToWord(wordSlt(left, right))
```

Both builders return `Word.ofNatModulo 1` when the signed comparison is true
and `Word.zero` when it is false. Source left evaluates exactly once before
source right, and the result retains the right operand's final store.
`wordSltFlag` inherits `wordSlt`'s nested bindings: only the computed values are
reversed before `wordSgt`; swapping the source expressions is forbidden.

## Implemented proof interface

The implementation publishes exactly twenty focused theorems. Each builder
owns five static laws:

- its named expansion;
- `HasType` and executable `infer?` results;
- arbitrary `Expr.rename`; and
- `Expr.weakenAt`.

Each builder also owns five evaluation laws: one general store-threaded theorem
and four sign-quadrant corollaries covering both-nonnegative, both-negative,
nonnegative/negative, and negative/nonnegative operands. Same-sign results use
the corresponding unsigned-order decision; cross-sign results reduce directly.
Every result is canonical word one or zero.

Do not add a Word operation, primitive application theorem, Core tag, or
duplicate generic typing and Safety APIs.

## Implemented tests

Focused regressions cover:

- compile-time use of all twenty theorem names;
- zero, the sign boundary, maximum, same-sign order, cross-sign order, and
  equality;
- word result types, a wrong declared result, and wrong left/right operands;
- unchecked operands exposing the underlying `wordSgt` invalid-operation fault;
- a left fault that skips the right and a right fault that observes the
  completed left store;
- allocating and writing operands evaluated left then right exactly once with
  the final store retained;
- insufficient/sufficient literal and effectful CEK fuel boundaries:
  7/8 and 31/32 for `wordSgtFlag`, 13/14 and 37/38 for `wordSltFlag`.

## Publication and exclusions

This slice composes existing internal expressions. It adds no Core form,
primitive tag, source spelling, ABI rule, opcode lowering, gas rule, schema,
or public byte.

## Consequences

Internal Core gains canonical word-valued strict signed comparisons while
retaining the established boolean basis, evaluation order, faults, effects,
stores, and publication boundary.

The ten static and ten evaluation theorems cover both exact builders. Same-sign
cases conditionally return canonical word one or zero from their order;
cross-sign cases return the corresponding constant result. Executable
regressions cover values and types, invalid payloads on both sides, ordered
faults, effects and final stores, and exact fuel boundaries: 7/8 and 31/32 for
`wordSgtFlag`, and 13/14 and 37/38 for `wordSltFlag`. The independent audit
found no P0-P3 issue.
