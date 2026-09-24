# ADR-0040: Add internal word byte selection

- Status: Accepted
- Decision date: 2026-08-27
- Scope: twenty-second internal Semantic Core vNext slice
- Implementation: Complete

## Context

Core has 256-bit words but no direct operation for selecting one of their 32
bytes. A precise internal operation supports later bit-level work without
committing source syntax.

## Decision

Add internal `BinaryOp.wordByte` and `Word.byteAt(index, value)`. Operand order
is normative: left is the index and right is the value. Core evaluates index
first, then value, each exactly once, retaining the value's final store.

Indices are big-endian: zero selects the most significant byte and 31 the least
significant byte. Define:

```text
byteAt(index, value) = 0,                                  if index >= 32
byteAt(index, value) =
  Word.ofNatModulo ((value.val / 2^(8*(31-index.val))) % 256), otherwise
```

Thus `byteAt(30, 0x1122) = 0x11` and `byteAt(31, 0x1122) =
0x22`; indices zero and 29 select zero from that value.

Add the tag only to internal Core syntax and extend existing typing, inference,
renaming, weakening, evaluation, machine, Safety, and proof cases. Do not add
an `Expr` alias or duplicate generic theorem surfaces.

## Required proof interface

Publish exactly nine focused theorems:

- `Word.byteAt_of_lt_32`, `Word.byteAt_of_ge_32`, `Word.byteAt_zero`,
  `Word.byteAt_index30_1122`, and `Word.byteAt_index31_1122`;
- `BinaryOp.apply_wordByte`; and
- store-threaded `Evaluates.wordByte`, `Evaluates.wordByte_lt_32`, and
  `Evaluates.wordByte_ge_32`.

The general evaluation exposes the intermediate store after the index and the
final store after the value. The cases state the exact in-range formula and
total out-of-range zero result.

## Required tests

Focused regressions cover:

- value `0x1122` at indices 0, 29, 30, 31, 32, and maximum;
- zero and maximum values, including boundary bytes;
- Word result typing, wrong declared result, and wrong index/value types;
- raw invalid binary operands;
- an index fault that skips value evaluation and a value fault that observes
  index effects;
- two allocating and writing operands evaluated index then value exactly once,
  with the final store retained;
- exact literal 4/5 and effectful 28/29 fuel boundaries.

Compile-time examples exercise all nine theorem names.

## Exclusions

This decision adds no source or standard-library API, ABI rule, opcode lowering,
or gas rule. Existing operation values, types, faults, effects, fuel, evaluation
order, and publication boundaries remain unchanged.

## Consequences

Internal Core gains total, explicitly ordered, big-endian byte selection while
leaving source syntax unchanged. Further primitives require separate ADRs.

## Implementation result

Internal Core now has `BinaryOp.wordByte` and total `Word.byteAt`. All nine
focused theorems are implemented: five Word laws, one exact application
equation, and three store-threaded general/range-case evaluations.

Compile-time and runtime tests cover `0x1122` at indices 0, 29, 30, 31, 32,
and maximum; zero and maximum values; Word result typing and wrong result,
index, and value types; raw invalid operands on both sides; ordered index/value
faults; and two allocating, writing operands evaluated exactly once with their
final store.
Literal evaluation has the exact 4/5 fuel boundary and effectful evaluation the
exact 28/29 boundary.

The implementation and focused semantic validation are complete. The
independent audit found no P0-P3 issue, no source trust escape hatch, and only
the repository-approved Lean foundational dependencies.
