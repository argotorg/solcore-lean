# ADR-0042: Add internal modular word exponentiation

- Status: Accepted
- Decision date: 2026-08-27
- Scope: twenty-fourth internal Semantic Core vNext slice
- Implementation: Complete

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
natural-number helper terminates by the `exponent` argument. `Word.pow` seeds it
with `exponent.val < 2^256`, so that call takes at most 256 iterations.

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
- exact literal 4/5 and effectful 28/29 CEK fuel boundaries.

Compile-time examples exercise all fourteen names. Large exponent regressions
also ensure the internal logarithmic loop terminates without changing CEK fuel.

## Exclusions

No source/standard-library API, ABI rule, opcode lowering, or gas rule is
introduced. Existing operation values, types, faults, effects, and fuel remain
unchanged.

## Consequences

Internal Core gains total, proved modular exponentiation with bounded host
computation and unchanged observable evaluation structure. Further primitives
require separate ADRs.

## Implementation result

Internal Core now has `BinaryOp.wordPow`, `Word.pow`, and the terminating
square-and-multiply helper `Word.modularPowLoop`. The loop-correctness theorem
connects the executable helper to natural-number exponentiation modulo `2^256`.
All fourteen focused theorems are complete: eight Word results, one exact
application equation, and five store-threaded evaluations.

Runtime tests cover zero, one, ordinary, boundary, high-bit, maximum, and
maximum-exponent cases without constructing giant expected natural powers.
They also cover result and operand types, raw invalid operands, ordered faults,
and two allocating, writing operands evaluated base then exponent exactly once
with the final store. Literal expressions stop at fuel 4 and complete at 5;
effectful expressions stop at 28 and complete at 29. Maximum exponents still
complete at fuel 5 because the internal loop remains one CEK primitive step.

The implementation and focused proof/semantic validation are complete.
After correcting the helper-bound wording above, the independent audit found no
remaining P0-P3 issue. The next primitive or conversion requires its own ADR.
