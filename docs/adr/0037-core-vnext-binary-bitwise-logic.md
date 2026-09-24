# ADR-0037: Complete binary bitwise logic interfaces

- Status: Accepted
- Decision date: 2026-08-27
- Scope: nineteenth internal Semantic Core vNext slice
- Implementation: Complete

## Context

Core already represents three direct 256-bit bitwise operations:

```text
binary(wordAnd, left, right)
binary(wordOr, left, right)
binary(wordXor, left, right)
```

Generic typing, inference, renaming, weakening, evaluation, Safety, and machine
layers support all three. Focused reusable value laws,
primitive-application equations, and strict store-threaded evaluation results
remain missing.

## Decision

Keep the existing raw expressions. Do not add Expr aliases, operation tags,
forms, frames, or evaluation rules. Do not duplicate generic typing, inference,
renaming, weakening, Safety, totality, or correspondence proofs.

Each operation evaluates the left expression exactly once before evaluating the
right expression exactly once. The result retains the right evaluation's final
store. Although all three value operations are commutative, that fact never
permits an implementation or proof to swap arbitrary operand expressions,
because their effects and faults remain ordered.

## Required proof interface

Publish exactly fifteen named theorems. Nine reusable Word laws are:

- `Word.bitAnd_zero`, `Word.bitAnd_self`, and `Word.bitAnd_comm`;
- `Word.bitOr_zero`, `Word.bitOr_self`, and `Word.bitOr_comm`; and
- `Word.bitXor_zero`, `Word.bitXor_self`, and `Word.bitXor_comm`.

The remaining six are:

- `BinaryOp.apply_wordAnd`, `BinaryOp.apply_wordOr`, and
  `BinaryOp.apply_wordXor`; and
- store-threaded `Evaluates.wordAnd`, `Evaluates.wordOr`, and
  `Evaluates.wordXor`.

Each evaluation theorem exposes the intermediate and final stores and returns
the existing Word operation. Compile-time examples exercise all fifteen names.

## Required tests

Focused regressions cover:

- masks `0xAA` and `0xCC`, producing `0x88`, `0xEE`, and `0x66`;
- zero, maximum, and equal-operand boundaries;
- word result types and wrong left, right, and result types;
- raw invalid-operand faults for all three operations;
- left faults that prevent right evaluation and right faults that observe left
  effects;
- two allocating and writing operands evaluated exactly once in order;
- final stores and exact literal 4/5 and effectful 28/29 fuel boundaries.

## Boundaries

This slice does not add universal maximum-mask or complement identities. It
does not define source or standard-library APIs, ABI behavior, opcode lowering,
or gas. It changes no type, value, fault, evaluator, frame, tag, schema,
version, byte encoding, or published boundary.

## Consequences

Callers gain concise algebraic and evaluation results for the existing binary
bitwise operations without changing semantics or publication boundaries. The
next feature is selected by a separate ADR.

## Implementation result

All fifteen theorems are complete: nine Word laws, three exact
primitive-application equations, and three store-threaded evaluations. The
commutativity theorems apply only to Word values; no theorem or implementation
swaps operand expressions.

Tests confirm `0xAA` and `0xCC` produce `0x88`, `0xEE`, and `0x66`, together
with zero, maximum, and self boundaries. Type rejection, raw and ordered faults,
two exactly-once effectful operands, and the final store are covered for all
three operations. Literal execution has the exact 4/5 fuel boundary and
effectful execution the exact 28/29 boundary. The final audit found no P0-P3
issue. No alias, generic proof duplicate, tag, or schema changed. The next
feature is selected by a separate ADR.
