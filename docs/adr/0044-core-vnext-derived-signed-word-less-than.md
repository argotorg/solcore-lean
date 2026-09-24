# ADR-0044: Derive effect-safe signed word less-than

- Status: Accepted
- Decision date: 2026-08-27
- Scope: twenty-sixth internal Semantic Core vNext slice
- Implementation: Complete

## Context

ADR-0043 adds boolean signed greater-than. Signed less-than has the value-level
equation `left < right` exactly when `right > left`, but swapping arbitrary
operand expressions would reverse faults and store effects.

## Decision

Add the derived builder `Expr.wordSlt(left, right) : bool` with this exact
expansion:

```text
let leftValue = left
let rightValue = weakenAt(right, 0)
wordSgt(rightValue, leftValue)
```

In de Bruijn form the final expression is
`.binary .wordSgt (.var 0) (.var 1)`: variable zero is the computed right value
and variable one is the computed left value.

Core evaluates the source left operand exactly once, then the source right
operand exactly once from the left operand's final store. Weakening preserves
the right expression's original free-variable references under the new binding.
The result retains the right operand's final store.

Implementing `wordSlt` by syntactically swapping `left` and `right` is
forbidden. It would change observable fault order, effects, stores, and fuel.

## Implemented proof interface

The implementation publishes exactly ten focused theorems: five static laws
and five evaluation laws.

- `Expr.wordSlt_expansion`;
- `HasType.wordSlt`;
- `infer_wordSlt`;
- `Expr.rename_wordSlt`;
- `Expr.weakenAt_wordSlt`;
- general store-threaded `Evaluates.wordSlt`; and
- `Evaluates.wordSlt_both_nonnegative`, `wordSlt_both_negative`,
  `wordSlt_nonnegative_negative`, and `wordSlt_negative_nonnegative`.

The evaluation proof reuses ADR-0029's typed head-insertion result to justify
the weakened right expression. It exposes the source intermediate and final
stores. Do not add `Word.signedLt`, a new operation tag, a primitive application
theorem, or duplicate generic typing and Safety APIs.

## Implemented tests

Focused regressions cover:

- zero, one, `2^255 - 1`, `2^255`, and maximum;
- both same-sign orders, both cross-sign orders, and equality;
- result and operand typing plus compile-time use of all ten theorem names;
- unchecked non-word operands exposing the exact underlying `wordSgt` fault;
- a source-left fault that skips the right and a source-right fault that
  observes the completed left store;
- allocating and writing operands evaluated source-left then source-right
  exactly once, retaining the final store;
- exact literal 10/11 and effectful 34/35 CEK fuel boundaries.

## Publication and exclusions

This slice adds a derived builder, not a Core form or primitive tag. It adds no
source spelling, ABI rule, opcode lowering, or gas rule. Word-valued signed
flags remain a separate future decision.

## Consequences

Internal Core gains signed less-than for arbitrary effectful expressions while
preserving source order. The signed comparison basis stays minimal.

The nested bindings leave variable zero naming the computed right value and
variable one naming the computed left value. Value and type boundaries,
underlying invalid-operand faults, ordered faults, effects, final stores, and
exact literal 10/11 and effectful 34/35 fuel boundaries are executable
regressions. The independent audit found no P0-P3 issue.
