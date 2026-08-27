# ADR-0041: Add internal arithmetic right shift

- Status: Accepted
- Decision date: 2026-08-27
- Scope: twenty-third internal Semantic Core vNext slice
- Implementation: In progress

## Context

Core has bounded logical shifts but no sign-extending right shift over its
256-bit words. The operation can be total and precise internally without
committing source syntax or extending frozen public formats.

## Decision

Add internal `BinaryOp.wordSar` and
`Word.shiftArithmeticRight(value, shift)`. Raw Core operand order is normative:
left is value and right is shift. Core evaluates value first, then shift, each
exactly once, retaining the shift operand's final store.

Let `M = 2^256` and `S = 2^255`. Define:

```text
shift < 256 and value < S:
  Word.ofNatModulo (value.val / 2^shift)

shift < 256 and value >= S:
  Word.ofNatModulo (M - 1 - ((M - 1 - value.val) / 2^shift))

shift >= 256 and value < S:  Word.zero
shift >= 256 and value >= S: Word.maximum
```

This is a total 256-bit two's-complement arithmetic right shift. Add the tag
only to internal Core and extend existing typing, inference, renaming,
weakening, evaluation, machine, Safety, and proof cases consistently. Do not
add an `Expr` alias or duplicate generic theorem surfaces.

## Operand-order boundary

Pinned source/EVM helper evidence presents arguments as `(shift, value)`, the
reverse of raw Core `(value, shift)`. A future elaborator must evaluate and bind
source arguments in source order first, then construct Core from those bound
values in Core order. It must not directly swap effectful source expressions.
This ADR adds no source elaborator or source API.

## Required proof interface

Publish exactly eleven focused theorems. Five Word results are:

- `Word.shiftArithmeticRight_zero`;
- `Word.shiftArithmeticRight_of_lt_256_nonnegative`;
- `Word.shiftArithmeticRight_of_lt_256_negative`;
- `Word.shiftArithmeticRight_of_ge_256_nonnegative`; and
- `Word.shiftArithmeticRight_of_ge_256_negative`.

The remaining six are `BinaryOp.apply_wordSar`, general store-threaded
`Evaluates.wordSar`, and four evaluation cases named `wordSar_lt_256_nonnegative`,
`wordSar_lt_256_negative`, `wordSar_ge_256_nonnegative`, and
`wordSar_ge_256_negative`.

The general evaluation exposes the intermediate store after value and final
store after shift.

## Required tests

Focused regressions cover:

- positive `4 >> 1`;
- the high bit shifted by 0, 1, 255, and 256;
- maximum shifted by 1 and by the maximum shift;
- two's-complement `-2 >> 1` and `-3 >> 1`;
- Word result typing, wrong declared result, and wrong value/shift types;
- raw invalid operands, a value fault that skips shift, and a shift fault that
  observes value effects;
- two allocating and writing operands evaluated value then shift exactly once,
  with the final store retained;
- exact literal 4/5 and effectful 28/29 fuel boundaries; and
- rejection by frozen Wire v1/v2 expression projection and by the Wire v2
  `BinaryOp` conversion itself.

Compile-time examples exercise all eleven theorem names.

## Publication and exclusions

`wordSar` is internal-only. No Wire tag, Core/JSON round trip, public Oracle or
schema change, source/standard-library API, ABI rule, opcode lowering, or gas
rule is introduced. Existing operation values, types, faults, effects, fuel,
and publication boundaries remain unchanged.

## Consequences

Internal Core gains total arithmetic right shift with explicit sign, range,
operand-order, and effect semantics. Further primitives require separate ADRs.
