# ADR-0030: Complete the derived word-comparison proof interface

- Status: Accepted
- Decision date: 2026-08-27
- Scope: twelfth internal Semantic Core vNext slice
- Implementation: In progress

## Context

ADR-0011 already defines four boolean-valued word comparisons as derived Core
expressions: `wordNe`, `wordLt`, `wordLe`, and `wordGe`. Their runtime meaning is
therefore fixed by existing unary, binary, let, variable, and weakening rules.
What remains is a uniform public proof interface for arbitrary operand
expressions, including expressions that change the local store or fault.

This slice completes that proof surface. It introduces no expression form,
operation, evaluation rule, fault, source syntax, wire tag, or public behavior.

## Decision

The existing ADR-0011 expansions remain normative:

```text
wordNe(left, right) = boolNot(wordEq(left, right))
wordLt(left, right) =
  let leftValue = left
  let rightValue = weakenAt(right, 0)
  wordGt(rightValue, leftValue)
wordLe(left, right) = boolNot(wordGt(left, right))
wordGe(left, right) = boolNot(wordLt(left, right))
```

`wordLt` and `wordGe` must keep the nested-let expansion. The first operand is
evaluated exactly once, then the second operand is evaluated exactly once in
the extended environment. The second expression is weakened so its original
free variables continue to refer to the same captured values. The final
`wordGt` receives the computed values in swapped positions.

Replacing this expansion by a syntax-level operand swap is forbidden. A swap
would evaluate the right expression first and would change fault order, store
effects, and exact fuel for arbitrary expressions.

## Proof interface

Each builder receives:

- a named expansion theorem;
- declarative `HasType` and executable `infer?` theorems;
- general `Expr.rename` and `Expr.weakenAt` laws;
- a general store-threaded big-step evaluation theorem; and
- truth-case corollaries for equal/unequal or ordered/not-ordered word values,
  as appropriate.

The `wordLt` and `wordGe` proofs reuse ADR-0029's head-insertion theorem to
justify evaluation of the weakened right operand without assuming that it is
closed. The general theorems must expose the intermediate stores so callers can
see left-to-right effect and fault order.

## Tests

Focused tests cover:

- true and false value cases, including zero and maximum-word boundaries;
- arbitrary left and right expressions that allocate and write, proving
  exactly-once left-to-right effects;
- wrong operand types and raw fault order;
- exact insufficient and sufficient fuel boundaries;
- Wire v1 rejection of the required primitive forms; and
- exact Wire v2 projection against each handwritten normative expansion.

Tests exercise both the executable behavior and the named proof interface.

## Boundaries

No frozen schema, capability report, golden byte sequence, or Oracle behavior
changes. These are ordinary existing Core expressions, and each wire projection
continues to treat them exactly like its handwritten expansion. This decision
does not define signed comparison, ABI decoding, opcode mapping, or gas cost.

## Consequences

The four comparisons gain a consistent arbitrary-expression proof API while
preserving their established meaning, evaluation order, faults, stores, and
fuel behavior.
