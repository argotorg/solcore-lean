# ADR-0043: Add internal signed word greater-than

- Status: Accepted
- Decision date: 2026-08-27
- Scope: twenty-fifth internal Semantic Core vNext slice
- Implementation: In progress

## Context

Core has unsigned word comparison and two's-complement arithmetic shift, but no
direct signed comparison. External compiler witnesses expose word-valued EVM
comparison helpers. Internal Core instead uses boolean comparison results and
derives word flags separately.

## Decision

Add internal `BinaryOp.wordSgt : word × word → bool` and
`Word.signedGt(left, right)`. A word is negative exactly when its value is at
least `2^255`.

Signed greater-than follows four total cases:

- two nonnegative words use their ordinary unsigned order;
- two negative words also use their ordinary unsigned order;
- every nonnegative word is greater than every negative word; and
- no negative word is greater than a nonnegative word.

Raw Core evaluates left and then right, each exactly once. The right operand
starts from the store produced by the left, and its final store is retained.

This slice adds only the boolean signed-greater basis. Signed less-than must not
swap arbitrary expressions; a future slice may derive it with bindings that
preserve evaluation order. Word-valued signed flags are also deferred.

## Required proof interface

Publish exactly eleven focused theorems. Five Word laws are:

- `Word.signedGt_self`;
- `Word.signedGt_both_nonnegative`;
- `Word.signedGt_both_negative`;
- `Word.signedGt_nonnegative_negative`; and
- `Word.signedGt_negative_nonnegative`.

The remaining six are `BinaryOp.apply_wordSgt`, general store-threaded
`Evaluates.wordSgt`, and four evaluations named `wordSgt_both_nonnegative`,
`wordSgt_both_negative`, `wordSgt_nonnegative_negative`, and
`wordSgt_negative_nonnegative`.

Generic binary typing, inference, renaming, weakening, correspondence, and
Safety APIs remain authoritative; this slice does not duplicate them.

## Required tests

Focused regressions cover:

- zero, one, `2^255 - 1`, `2^255`, and maximum;
- both same-sign orders, both cross-sign orders, and equal operands;
- boolean result typing, a wrong declared result, and wrong left/right types;
- raw invalid operands, a left fault that skips the right, and a right fault
  that observes completed left effects;
- two allocating and writing operands evaluated left then right exactly once,
  with their final store retained;
- exact literal 4/5 and effectful 28/29 CEK fuel boundaries; and
- rejection by frozen Wire v1/v2 expression projection and by the Wire v2
  `BinaryOp` conversion itself.

Compile-time examples exercise all eleven theorem names.

## Publication and exclusions

`wordSgt` is internal-only. Do not add it to frozen Wire v1 or v2, their JSON
enums, any public Oracle, schema, profile, or version. No source spelling,
standard-library API, ABI rule, opcode lowering, or gas rule is introduced.
Existing public behavior and bytes remain unchanged.

## Consequences

Internal Core gains one total boolean basis for signed comparison. Derived
signed less-than and word-valued flags remain explicit future decisions.
