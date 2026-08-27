# ADR-0042: Add internal modular word exponentiation

- Status: Accepted
- Decision date: 2026-08-27
- Scope: twenty-fourth internal Semantic Core vNext slice
- Implementation: In progress

## Context

Core words support modular addition and multiplication but not exponentiation.
Direct host exponentiation is unsuitable for a 256-bit exponent, while binary
square-and-multiply gives a total bounded implementation and a compact proof
surface.

## Decision

Add internal `BinaryOp.wordPow` and `Word.pow(base, exponent)`. Raw Core operand
order is left base, right exponent. Core evaluates base first, then exponent,
each exactly once, retaining the exponent operand's final store.

Implement `Word.pow` with
`Word.modularPowLoop(base, accumulator, exponent)`. Each iteration uses the low
exponent bit, squares the base modulo `2^256`, and halves the exponent. The
recursive measure is `exponent.val`; halving bounds the loop to at most 256
iterations.

The result is exactly:

```text
Word.ofNatModulo (base.val ^ exponent.val)
```

equivalently `base.val ^ exponent.val % 2^256`. Exponent zero returns one, so
`0^0 = 1`.

The helper loop is an internal computation inside one primitive application.
Its iterations are not separate CEK transitions or separately charged fuel.
A successful raw binary primitive still costs the existing single primitive
step after its two operands.

Add the tag only to internal Core and extend existing typing, inference,
renaming, weakening, evaluation, machine, Safety, and proof cases. Do not add
an `Expr` alias or duplicate generic theorem surfaces.

## Required proof interface

Publish exactly fourteen focused theorems. Eight Word results are:

- `Word.modularPowLoop_correct` and `Word.pow_correct`;
- `Word.pow_zero`, `Word.pow_one`, and `Word.one_pow`;
- `Word.zero_pow_of_positive`;
- `Word.two_pow_256`; and
- `Word.maximum_pow_two`.

The remaining six are `BinaryOp.apply_wordPow`, general store-threaded
`Evaluates.wordPow`, and `Evaluates.wordPow_exponent_zero`,
`Evaluates.wordPow_exponent_one`, `Evaluates.wordPow_one_base`, and
`Evaluates.wordPow_zero_base_of_positive`.

## Required tests

Focused regressions cover:

- `0^0`, `37^0`, `0^1`, `1^maximum`, and `37^1`;
- `2^8`, `2^256`, and `(2^255)^2`;
- `maximum^2`, `maximum^maximum`, and `2^maximum`;
- Word result typing, wrong declared result, and wrong base/exponent types;
- raw invalid operands, a base fault that skips exponent, and an exponent fault
  that observes base effects;
- two allocating and writing operands evaluated base then exponent exactly once,
  with the final store retained;
- exact literal 4/5 and effectful 28/29 CEK fuel boundaries; and
- rejection by frozen Wire v1/v2 expression projection and by the Wire v2
  `BinaryOp` conversion itself.

Compile-time examples exercise all fourteen names. Large exponent regressions
also ensure the internal logarithmic loop terminates without changing CEK fuel.

## Publication and exclusions

`wordPow` is internal-only. No Wire tag, Core/JSON round trip, public Oracle or
schema change, source/standard-library API, ABI rule, opcode lowering, or gas
rule is introduced. Existing operation values, types, faults, effects, fuel,
and publication boundaries remain unchanged.

## Consequences

Internal Core gains total, proved modular exponentiation with bounded host
computation and unchanged observable evaluation structure. Further primitives
require separate ADRs.
