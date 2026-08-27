# ADR-0025: Semantic Core vNext word zero test

- Status: Accepted
- Decision date: 2026-08-27
- Scope: seventh internal Semantic Core vNext vertical slice
- Implementation: In progress

## Context

The Core can already compare words and convert a boolean to canonical word zero
or one. It can therefore express the EVM/Yul `iszero` operation without a new
primitive or semantic rule.

The local Haskell evaluator returns one exactly when its input is zero, and zero
otherwise. The Rust-bundled Solidity/EVM implementation gives `ISZERO` the same
meaning. This agreement provides a stable target without settling any deferred
signed, byte, arithmetic-shift, or encoding questions.

## Decision

The internal Core library provides this derived expression builder:

```text
wordIsZero(value) =
  boolToWord(wordEq(value, word(0)))
```

Its signature and result table are:

```text
word -> word
```

| Input | Result |
| --- | --- |
| word zero | word one |
| any nonzero word | word zero |

The typing rule is:

```text
Gamma |- value : word
-------------------------
Gamma |- wordIsZero(value) : word
```

This is a derived form, not a new Core tag. Type inference, checking, big-step
evaluation, CEK execution, safety, and fuel behavior are inherited from the
expanded existing expressions.

## Evaluation order and effects

The operand occurs exactly once, as the left operand of `wordEq`. It is
evaluated before the constant zero. The equality result is converted to word
zero or one without evaluating the original operand again.

The expansion preserves the store produced by evaluating the operand. It
allocates no cell, performs no write, and adds no effect of its own. Effectful
operands must therefore execute exactly once.

## Difference from `wordToBool` and ABI rules

`wordToBool` has type `word -> bool` and implements truthiness: zero becomes
`false`, while every nonzero word becomes `true`. `wordIsZero` has type
`word -> word` and implements the opposite predicate encoded canonically as a
word: zero becomes one, while every nonzero word becomes zero.

Neither operation is an ABI decoder. This ADR defines no canonical-input
validation, byte width, padding, byte order, calldata layout, storage layout,
or other encoding rule. The word result zero or one is a semantic value only.

## Core and wire boundary

This slice adds no type, value, expression, operation, frame, transition,
machine-fault, diagnostic, schema, or capability tag. It also adds no new
big-step rule or CEK transition.

Wire v1 lacks the existing primitive form needed by the expansion and therefore
continues to reject it. Wire v2 projects it using only its existing `if`, word,
binary `wordEq`, and related ordinary expression forms. No frozen wire schema,
Oracle profile, capability, or golden byte changes.

## Required implementation, proof, and tests

- define `Expr.wordIsZero` solely by the expansion in this ADR;
- prove its declarative typing rule and executable `infer?` result;
- prove evaluation for zero and for an arbitrary nonzero word;
- prove the general evaluation result and that the operand's final store is
  also the conversion's final store;
- prove the builder expands to the stated existing expression and that the
  operand subtree occurs exactly once;
- prove or expose commutation with `Expr.weakenAt`;
- test zero, one, the maximum word, and representative nonzero values;
- test rejection of a non-word operand and the unchecked expansion's fault;
- test an effectful operand to detect skipped or duplicate evaluation;
- test exact sufficient and insufficient fuel boundaries; and
- test that wire v1 rejects while wire v2 projects exactly the handwritten
  expansion, with no new tag or public capability.

## Consequences

The Core gains the established Haskell, Rust, Yul, and EVM zero-test meaning as
a small reusable builder. Because the operation remains an expansion, existing
syntax-indexed proofs and serializers require no new cases.
