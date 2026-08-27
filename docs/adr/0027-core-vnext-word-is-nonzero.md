# ADR-0027: Semantic Core vNext word nonzero test

- Status: Accepted
- Decision date: 2026-08-27
- Scope: ninth internal Semantic Core vNext vertical slice
- Implementation: Complete

## Context

ADR-0024 provides total word truthiness and canonical boolean-to-word
conversion. Their composition expresses the EVM/Yul-style word-valued nonzero
predicate without a new primitive or semantic rule.

## Decision

The internal Core library provides this derived builder:

```text
wordIsNonzero(x) = boolToWord(wordToBool(x))
```

It has type `word -> word`: word zero maps to word zero, and every nonzero word
maps to word one. The operand occurs exactly once. Its final store is preserved
through both conversions, which add no allocation, write, or other effect.

This result differs from `wordToBool`, whose result type is `bool`, and is the
word-valued inverse predicate of `wordIsZero`. None of these operations performs
strict ABI decoding: no zero-or-one input restriction or encoding rule is
introduced.

This is a derived form. It adds no type, value, expression, operation, frame,
transition, fault, diagnostic, schema, capability, Core, CEK, wire, or Oracle
tag. Existing typing, evaluation, safety, and fuel behavior come from the exact
expansion.

## Alternatives

`wordIsZero(wordIsZero(x))` has the same value table, but repeats a larger
derived conversion pipeline and therefore consumes more fuel. It is not the
normative expansion.

`boolToWord(wordGt(x, word(0)))` is value-equivalent for unsigned words, but its
unchecked raw fault and exact fuel differ. It may be proved equivalent or used
by a future optimizer, but cannot replace the normative expansion silently.

## Wire boundary

Wire v1 rejects the primitive forms required by the expansion. Wire v2 projects
exactly the ordinary `boolToWord(wordToBool(x))` expression. Frozen schemas,
capabilities, and golden bytes do not change.

## Required implementation, proof, and tests

- define the builder solely by the normative expansion and prove that equality;
- prove declarative typing and the executable `infer?` result;
- prove general store-threaded evaluation, zero, and arbitrary nonzero results;
- prove the operand occurs and evaluates exactly once and its final store is
  the result store;
- prove commutation with `Expr.weakenAt`;
- test zero, one, maximum word, representative nonzero values, and bad types;
- test effectful operands, allocation/write preservation, and unchecked faults;
- test exact sufficient and insufficient fuel boundaries; and
- test wire v1 rejection and exact wire v2 projection with no new tag.

## Consequences

The Core gains a canonical word-valued nonzero predicate while reusing the
already accepted truthiness conversion and preserving all existing semantic
boundaries.

The implementation provides the named canonical expansion, typing and
inference, general and zero/nonzero store-preserving evaluation, and weakening
theorems. Tests cover zero, one, two, and maximum word values; operand types and
the raw unchecked fault; exact insufficient/sufficient fuel at 9/10 steps;
allocation and write effects exactly once with final-store preservation; the
distinctions from `wordToBool`, `wordIsZero`, and ABI decoding; and exact wire
v1 rejection and v2 projection. Warning, trust, axiom, and whitespace audits
pass.
