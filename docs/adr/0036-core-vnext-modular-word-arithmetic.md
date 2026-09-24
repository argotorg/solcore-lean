# ADR-0036: Complete modular word arithmetic interfaces

- Status: Accepted
- Decision date: 2026-08-27
- Scope: eighteenth internal Semantic Core vNext slice
- Implementation: Complete

## Context

Core already represents direct modular arithmetic with raw binary expressions:

```text
binary(wordAdd, left, right)
binary(wordSub, left, right)
binary(wordMul, left, right)
```

ADR-0011 fixes every result modulo `2^256`. Generic typing, inference, renaming,
weakening, evaluation, Safety, and machine layers already support all
three operations. Focused value and store-threaded proof names and symmetric
strict-evaluation regressions are still missing.

## Decision

Keep the existing raw expressions. Do not add Expr aliases, operation tags,
expression forms, machine frames, or evaluation rules. Do not duplicate generic
typing, inference, renaming, weakening, Safety, totality, or correspondence.

The left expression evaluates exactly once before the right expression, which
then evaluates exactly once. This order is observable through faults and
effects even when addition or multiplication produce commutative values. It is
also the value order for subtraction: `wordSub(left, right)` computes left minus
right, not the reverse. The result retains the right evaluation's final store.
Value-level commutativity never permits an implementation or proof to swap
arbitrary addition or multiplication operand expressions.

Arithmetic remains modular. Overflow and underflow wrap modulo `2^256`; they do
not fault and do not return a separate status.

## Required proof interface

Publish exactly fourteen named theorems. Eight reusable Word facts are:

- `Word.add_zero` and `Word.add_maximum_one`;
- `Word.sub_zero`, `Word.sub_self`, and `Word.zero_sub_one`;
- `Word.mul_zero`, `Word.mul_one`, and `Word.maximum_mul_two`.

The constant one is `Word.ofNatModulo 1`. The two in
`Word.maximum_mul_two` is `Word.ofNatModulo 2`, and its expected result is
`Word.ofNatModulo (wordModulus - 2)`. The remaining six theorems are:

- `BinaryOp.apply_wordAdd`, `BinaryOp.apply_wordSub`, and
  `BinaryOp.apply_wordMul`; and
- store-threaded `Evaluates.wordAdd`, `Evaluates.wordSub`, and
  `Evaluates.wordMul`.

Each evaluation theorem exposes the intermediate and final stores and returns
the existing `Word.add`, `Word.sub`, or `Word.mul` result. Compile-time examples
exercise all fourteen names.

## Required tests

Focused regressions cover:

- ordinary addition, subtraction, and multiplication;
- overflow, underflow, and multiplication wraparound;
- zero, one, and maximum-word boundaries;
- word result types and wrong left, right, and result types;
- raw invalid-operand faults for all three operations;
- a left fault that prevents right evaluation;
- a right fault that observes completed left effects;
- two allocating and writing operands evaluated exactly once in order;
- the final store and exact literal 4/5 and effectful 28/29 fuel boundaries.

## Boundaries

This ADR does not define checked arithmetic, overflow reports, signed
arithmetic, exponentiation, ternary modular operations, source overloads,
standard-library APIs, ABI behavior, opcode lowering, or gas. It changes no
type, value, fault, evaluator, frame, tag, schema, version, byte encoding, or
published boundary.

## Consequences

Callers can use concise named results for modular arithmetic while the raw Core
operators and every published boundary remain unchanged. Further conversions
and primitives are selected by separate ADRs.

## Implementation result

All fourteen theorems are complete: eight reusable Word identities and
boundaries, three exact primitive-application equations, and three
store-threaded evaluations. Tests cover ordinary arithmetic plus addition
overflow, subtraction underflow, and multiplication wraparound; zero, one, and
maximum; and the left-minus-right order of subtraction.

Type rejection, raw and ordered faults, two exactly-once effectful operands, and
the final store are checked for all three operations. Literal execution has the
exact 4/5 fuel boundary and effectful execution the exact 28/29 boundary. The
final independent audit found no P0-P3 issue. No alias, generic proof duplicate,
tag, schema, or other published boundary changed. The next feature is selected
by a separate ADR.
