# ADR-0048: Add internal signed word division and remainder

- Status: Accepted
- Decision date: 2026-08-27
- Scope: thirtieth internal Semantic Core vNext slice
- Implementation: In progress

## Context

Core words are unsigned 256-bit containers, but several existing operations
interpret their top bit as a two's-complement sign. Core still lacks signed
division and remainder with explicit behavior for division by zero and the
one quotient that cannot be represented as a signed 256-bit integer.

## Decision

Add internal `BinaryOp.wordSdiv` and `BinaryOp.wordSmod`. The left operand is
the dividend and the right operand is the divisor. Core evaluates both
operands, left then right and exactly once, before applying either operation.

Let `H = 2^255` and `M = 2^256`. A word is negative when its natural value is
at least `H`. Its unsigned magnitude is its value when nonnegative and
`M - value` when negative. Encoding a nonnegative magnitude returns it modulo
`M`; encoding a negative nonzero magnitude returns `M - magnitude` modulo
`M`. Zero always has the single encoding zero.

```text
negative(v) = H <= v
magnitude(v) = if negative(v) then M - v else v
encode(isNegative, n) =
  if n = 0 then 0 else if isNegative then (M - n) mod M else n mod M
```

If the divisor is zero, both operations return zero after both operands have
been evaluated. Otherwise, `wordSdiv` divides the natural magnitudes and gives
the quotient a negative sign exactly when the operand signs differ. Natural
division therefore implements rounding toward zero. `wordSmod` takes the
natural remainder of the magnitudes and gives a nonzero remainder the sign of
the dividend, independent of the divisor's sign.

The minimum signed word divided by negative one wraps to the minimum word;
its remainder is zero. This follows the fixed-width encoding instead of
introducing overflow or exceptional behavior.

## Required proof interface

Publish exactly fourteen focused theorems:

- `Word.sdiv_zero` and `Word.sdiv_nonzero`;
- `Word.smod_zero` and `Word.smod_nonzero`;
- `Word.sdiv_minimum_negative_one` and
  `Word.smod_minimum_negative_one`;
- `BinaryOp.apply_wordSdiv` and `BinaryOp.apply_wordSmod`;
- general `Evaluates.wordSdiv`, plus `wordSdiv_zero` and
  `wordSdiv_nonzero`; and
- general `Evaluates.wordSmod`, plus `wordSmod_zero` and
  `wordSmod_nonzero`.

The general evaluation theorems expose the intermediate store after the
dividend and the final store after the divisor. Generic typing, inference,
machine, Safety, and renaming theorems should absorb the new binary cases;
focused duplicates are excluded.

## Required tests

Focused regressions cover:

- `7 / 3`, `7 / -3`, `-7 / 3`, and `-7 / -3`, with corresponding remainders,
  including quotients rounded toward zero and remainders carrying the
  dividend's sign;
- zero dividends and zero divisors, including confirmation that a zero
  divisor does not skip right-operand evaluation;
- minimum signed word divided by negative one, and its zero remainder;
- word result typing, wrong operand types, and a wrong declared result type;
- unchecked operands exposing the exact invalid left or right payload;
- a dividend fault that skips the divisor and a divisor fault that observes
  completed dividend effects;
- two allocating and writing operands evaluated left then right exactly once,
  retaining the divisor's final store;
- exact literal 4/5 and effectful 28/29 CEK fuel boundaries; and
- rejection by frozen Wire v1/v2 expression projection and the Wire v2
  `BinaryOp` conversion.

## Publication and exclusions

Both operations are internal-only. Do not add them to frozen Wire v1 or v2,
their JSON enums, any public Oracle, schema, profile, version, or golden byte
stream. This slice adds no source syntax, standard-library API, ABI rule,
opcode lowering, gas rule, or exceptional division behavior.

## Consequences

Core gains total, deterministic signed division and remainder whose sign,
rounding, zero-divisor, overflow-wrap, operand-order, and store behavior are
explicit. Existing public formats and behavior remain unchanged.
