# ADR-0046: Derive boolean signed non-strict word comparisons

- Status: Accepted
- Decision date: 2026-08-27
- Scope: twenty-eighth internal Semantic Core vNext slice
- Implementation: In progress

## Context

Core has boolean signed greater-than and an effect-safe derived signed
less-than. Signed less-than-or-equal and greater-than-or-equal can reuse those
operations through boolean negation. They need no new primitive meaning or tag.

## Decision

Add two derived boolean builders with these exact expansions:

```text
wordSle(left, right) = unary boolNot (binary wordSgt left right)
wordSge(left, right) = unary boolNot (wordSlt(left, right))
```

Each builder evaluates source left exactly once before source right exactly
once and retains the right operand's final store. `wordSge` inherits
`wordSlt`'s nested bindings: only the computed values are reversed before
`wordSgt`; swapping source expressions is forbidden.

For same-sign operands, the result negates the corresponding unsigned strict
greater-than decision. Equality is therefore true for both builders. Across
signs, nonnegative ≤ negative is false and negative ≤ nonnegative is true;
nonnegative ≥ negative is true and negative ≥ nonnegative is false.

## Required proof interface

Publish exactly twenty focused theorems. Each builder owns five static laws:

- its named expansion;
- `HasType` and executable `infer?` results;
- arbitrary `Expr.rename`; and
- `Expr.weakenAt`.

Each builder also owns one general store-threaded evaluation theorem and four
sign-quadrant corollaries: both nonnegative, both negative,
nonnegative/negative, and negative/nonnegative.

Do not add a Word operation, primitive application theorem, Core tag, or
duplicate generic typing and Safety APIs.

## Required tests

Focused regressions cover:

- compile-time use of all twenty theorem names;
- zero, both sign-boundary neighbors, maximum, same-sign order, cross-sign
  order, and equality;
- boolean result types, a wrong declared result type, and wrong left/right
  operands;
- unchecked operands exposing the underlying `wordSgt` invalid payload on
  either side;
- left faults that skip the right and right faults that observe the completed
  left store;
- allocating and writing operands evaluated left then right exactly once with
  their final store retained;
- insufficient/sufficient literal and effectful CEK fuel boundaries: 6/7 and
  30/31 for `wordSle`, 12/13 and 36/37 for `wordSge`; and
- frozen Wire v1/v2 rejection of each builder and handwritten expansion, plus
  Wire v2 rejection of the underlying `wordSgt` operation.

## Publication and exclusions

This slice adds derived builders, not Core forms or primitive tags. It adds no
source spelling, ABI rule, opcode lowering, gas rule, schema, Oracle behavior,
Wire version, public enum member, or public byte. Frozen Wire v1/v2 remain
unchanged.

## Consequences

Internal Core gains boolean signed non-strict comparisons while retaining the
signed strict basis, source evaluation order, faults, effects, stores, and
publication boundary.
