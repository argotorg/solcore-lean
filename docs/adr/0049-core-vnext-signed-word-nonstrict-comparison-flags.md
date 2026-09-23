# ADR-0049: Derive word-valued signed non-strict comparison flags

- Status: Accepted
- Decision date: 2026-08-27
- Scope: thirty-first internal Semantic Core vNext slice
- Implementation: Complete; independent audit found no P0-P3 issue

## Context

ADR-0046 provides boolean signed less-than-or-equal and greater-than-or-equal.
Internal semantic composition also needs their canonical word-valued forms,
without adding another primitive operation or changing public syntax.

## Decision

Add two derived expression builders with exact expansions:

```text
wordSleFlag(left, right) = boolToWord(wordSle(left, right))
wordSgeFlag(left, right) = boolToWord(wordSge(left, right))
```

True becomes `Word.ofNatModulo 1` and false becomes `Word.zero`; no other word
is a possible result. Both builders evaluate the source left expression before
the source right expression, each exactly once, and retain the right operand's
final store. `wordSgeFlag` inherits `wordSge`'s nested bindings: only already
computed bound values are swapped for the underlying signed comparison. The
source expressions themselves must never be reordered.

## Implemented proof interface

Publish exactly twenty focused theorems. Each builder owns five static laws:

- its named expansion;
- its `HasType` result;
- its executable `infer?` result;
- arbitrary `Expr.rename`; and
- `Expr.weakenAt`.

Each builder also owns five evaluation laws: one general store-threaded theorem
and four sign-quadrant corollaries for both nonnegative, both negative,
nonnegative/negative, and negative/nonnegative operands. Same-sign cases use
the corresponding unsigned non-strict order. Cross-sign cases reduce to a
constant canonical word, and equal operands produce word one for both builders.

Do not add a Word operation, primitive application theorem, Core tag, or
duplicate generic typing, machine, Safety, or renaming infrastructure.

## Implemented tests

Focused regressions cover:

- compile-time use of all twenty theorem names;
- same-sign order, both cross-sign directions, equality, zero, the sign
  boundary, and the maximum word;
- canonical word one or zero and word result typing;
- a wrong declared result type and wrong left or right operand types;
- unchecked expressions exposing the underlying `wordSgt` invalid-operation
  payload from either operand;
- a left fault that skips the right and a right fault that observes completed
  left effects;
- two allocating and writing operands evaluated left then right exactly once,
  retaining the right operand's final store;
- exact literal and effectful CEK fuel boundaries: 9/10 and 33/34 for
  `wordSleFlag`, and 15/16 and 39/40 for `wordSgeFlag`; and
- frozen Wire v1/v2 rejection of each builder and its handwritten expansion,
  plus Wire v2 rejection of the underlying `wordSgt` operation.

## Publication and exclusions

This slice only composes existing internal expressions. It adds no Core form,
primitive tag, source spelling, standard-library API, ABI rule, opcode
lowering, gas rule, schema, Wire version, or public byte. Frozen Wire v1/v2 and
their public operation enums remain unchanged.

## Consequences

Internal Core gains canonical word-valued signed non-strict comparisons while
preserving the established truth conditions, source evaluation order, faults,
effects, stores, and publication boundary.

## Implementation result

The exact twenty-theorem interface is complete: five static and five
store-threaded evaluation theorems for each builder. Focused regressions cover
canonical word one and zero, same-sign order, both cross-sign directions,
equality, types, underlying invalid-operation payloads, ordered faults,
left-to-right effects evaluated exactly once, and the retained final store.
Exact CEK boundaries pass at 9/10 and 33/34 for `wordSleFlag`, and 15/16 and
39/40 for `wordSgeFlag`.

Frozen Wire v1/v2 reject each builder and handwritten expansion, and Wire v2
rejects the underlying `wordSgt` operation. Public schemas and bytes remain
unchanged. Focused and full warning-free builds, the full test runner, kernel
policy, and metadata verification pass. The independent audit found no P0-P3
issue.
