# ADR-0035: Complete bounded logical shift interfaces

- Status: Accepted
- Decision date: 2026-08-27
- Scope: seventeenth internal Semantic Core vNext slice
- Implementation: Complete

## Context

Core already has direct logical shift operators:

```text
binary(wordShl, value, shift)
binary(wordShr, value, shift)
```

ADR-0011 fixes their 256-bit behavior. A shift below 256 uses the existing
logical operation; a shift of 256 or more returns zero. Generic typing,
inference, renaming, weakening, evaluation, Safety, machine, and Wire v2 layers
already support both operators. What is missing is a focused value and
store-threaded proof interface plus symmetric boundary regressions.

This work follows a semantics-first order. It does not resume grammar-dependent
proof work or choose source syntax.

## Decision

Keep the existing raw `.binary .wordShl` and `.binary .wordShr` expressions.
Do not add Expr aliases, operation tags, expression forms, frames, or evaluation
rules. Do not duplicate generic typing, inference, renaming, weakening, Safety,
totality, or machine-correspondence theorems.

The left Core operand is always the value and the right Core operand is always
the shift amount. Both operands evaluate exactly once, left to right, and the
result retains the right operand's final store. EVM and Yul helpers conventionally
place the shift first. A future elaborator must bind source operands in source
order before reordering them into this Core order.

Both operations are unsigned logical shifts. They do not interpret a sign bit.

## Required proof interface

Publish exactly fourteen named theorems:

- `Word.shiftLeft_zero` and `Word.shiftRight_zero` preserve the value;
- `Word.shiftLeft_of_lt_256` and `Word.shiftRight_of_lt_256` unfold shifts below
  256;
- `Word.shiftLeft_of_ge_256` and `Word.shiftRight_of_ge_256` return zero at 256
  or more;
- `BinaryOp.apply_wordShl` and `BinaryOp.apply_wordShr` give exact application
  results;
- general store-threaded `Evaluates.wordShl` and `Evaluates.wordShr`;
- below-256 cases `Evaluates.wordShl_lt_256` and
  `Evaluates.wordShr_lt_256`; and
- at-least-256 cases `Evaluates.wordShl_ge_256` and
  `Evaluates.wordShr_ge_256`.

The small and large Word lemmas state assumptions with `shift.val < 256` and
`256 ≤ shift.val`. Evaluation consumes the value and shift expressions in that
order and introduces no new semantic case.

## Required tests

Focused semantic regressions cover:

- zero, one, and maximum input words;
- shift amounts zero, one, 255, 256, and the maximum word;
- exact logical left and right boundary results;
- word result types, wrong left and right operands, and wrong result types;
- raw invalid-operand faults for both operations;
- a left fault that prevents shift evaluation;
- a right fault that observes completed value effects;
- two allocating and writing operands evaluated exactly once in order;
- final-store preservation and exact literal and effectful fuel boundaries;
- Wire v1 rejection of both raw expressions; and
- exact Wire v2 operator and operand-order projection and round trips.

Compile-time examples exercise all fourteen named theorems.

## Boundaries

This ADR does not define arithmetic shift, signed words, source spelling,
standard-library APIs, ABI behavior, opcode lowering, or gas. It changes no
type, value, fault, evaluator, frame, Wire tag, schema, version, byte encoding,
or published boundary. Existing Core and Wire versions retain their exact
meanings.

## Consequences

Callers can reason directly about ordinary, zero, and oversized logical shifts
without unpacking the generic binary rule. Additional conversions and
primitives remain planned as separate closed decisions.

## Implementation result

The implementation provides all fourteen required theorems: six Word boundary
and unfolding results, two exact primitive-application results, and six
store-threaded evaluation results. Tests cover values zero, one, and maximum;
shift amounts zero, one, 255, 256, and maximum; and the fixed value-left,
shift-right operand order.

Raw faults, left-to-right effects, and the final store are checked directly.
Literal expressions finish exactly at fuel 5 after failing at 4; two effectful
operands finish at 29 after failing at 28. Both operators are rejected by Wire
v1 and have exact Wire v2 projection, Core round trips, and JSON round trips.
The final independent audit found no P0-P3 issue. No alias, tag, generic proof,
schema, or other boundary changed. The next feature is chosen by a separate
ADR.
