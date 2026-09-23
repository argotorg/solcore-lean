# ADR-0050: Add dedicated ternary modular arithmetic

- Status: Accepted
- Decision date: 2026-08-27
- Scope: thirty-second internal Semantic Core vNext slice
- Implementation: Complete

## Context

Core has fixed-width binary addition and multiplication, but Solidity-style
modular arithmetic needs three operands and must reduce a full-precision sum or
product by an independently evaluated modulus. Composing the existing binary
word operations would wrap at 256 bits too early and give the wrong result.

## Decision

Add internal `TernaryOp.wordAddMod`, `TernaryOp.wordMulMod`, and
`Expr.ternary`. Each operation has type `word × word × word → word`. The first
value, second value, and modulus evaluate in source order, each exactly once;
the result retains the modulus evaluation's final store.

For natural representatives `a`, `b`, and `m`, define:

```text
wordAddMod(a, b, m) = if m = 0 then 0 else (a + b) % m
wordMulMod(a, b, m) = if m = 0 then 0 else (a * b) % m
```

All three operands evaluate even when the modulus is zero. For a nonzero
modulus, addition and multiplication use unbounded natural-number precision
before taking the remainder. They must not apply 256-bit wrapping to the sum
or product first.

Untyped execution reports a dedicated `invalidTernaryOperands` fault containing
the three raw values when an operand combination is invalid. Faults raised
while evaluating operand expressions still follow source order: an earlier
fault skips later operands, while a later fault observes all earlier effects.

## Required proof interface

Publish exactly fourteen focused theorems:

- `Word.addMod_zero`, `Word.addMod_nonzero`, `Word.mulMod_zero`, and
  `Word.mulMod_nonzero`;
- `Word.addMod_no_prewrap` and `Word.mulMod_no_prewrap`;
- `TernaryOp.apply_wordAddMod` and `TernaryOp.apply_wordMulMod`;
- general `Evaluates.wordAddMod`, plus `wordAddMod_zero` and
  `wordAddMod_nonzero`; and
- general `Evaluates.wordMulMod`, plus `wordMulMod_zero` and
  `wordMulMod_nonzero`.

The general evaluation theorems expose the stores after the first and second
operands and the final store after the modulus. Generic infrastructure must
cover typing, executable checking, Safety, declarative/executable
correspondence, and renaming; do not publish focused duplicates of those
generic laws.

## Required tests

Focused regressions cover:

- ordinary addition and multiplication modulo nonzero words;
- zero modulus after three effectful operands, confirming every operand runs
  exactly once and the final store is retained;
- sums and products whose mathematical intermediate exceeds `2^256`, proving
  reduction happens before any word encoding;
- word result typing, wrong declared result type, and wrong first, second, or
  modulus operand types;
- unchecked execution returning the exact three-value
  `invalidTernaryOperands` payload;
- ordered faults at each operand and left-to-right allocating/writing effects;
- exact literal 6/7 and effectful 42/43 CEK fuel boundaries; and
- rejection by frozen Wire v1/v2 expression projection, with no public
  ternary-operation enum added.

## Staged implementation plan

Keep every commit below 300 changed lines and leave the tree green:

1. add the Word values and total `TernaryOp.apply` layer;
2. add a dormant CEK ternary continuation tail without exposing expressions;
3. add `Expr.ternary` and activate untyped evaluation semantics;
4. activate typing, checking, Safety, correspondence, and renaming support;
5. add the exact fourteen focused proofs;
6. add focused semantic and machine tests;
7. add frozen Wire rejection tests; and
8. update completion documentation after all checks pass.

## Publication and exclusions

The ternary form and both operations are internal-only. Frozen Wire v1/v2,
their JSON forms, schemas, profiles, and versions remain unchanged and reject
the new form. This slice adds no source syntax,
standard-library API, ABI rule, opcode lowering, or gas rule.

## Consequences

Core gains explicit three-operand modular arithmetic with correct
full-precision intermediates, deterministic zero-modulus behavior, dedicated
raw faults, and observable source-order effects. Public behavior is unchanged.
