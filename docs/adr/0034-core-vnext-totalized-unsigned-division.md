# ADR-0034: Complete totalized unsigned division and modulo interfaces

- Status: Accepted
- Decision date: 2026-08-27
- Scope: sixteenth internal Semantic Core vNext slice
- Implementation: In progress

## Context

Core already has direct unsigned word division and modulo operators:

```text
binary(wordDiv, numerator, divisor)
binary(wordMod, numerator, divisor)
```

Both are totalized. A zero divisor returns word zero rather than faulting. The
generic binary typing, inference, renaming, weakening, evaluation, safety,
machine, and Wire v2 layers already support these operators. What is missing is
a focused value and store-threaded proof interface plus regressions for their
strict evaluation behavior.

## Decision

Keep the existing raw `.binary .wordDiv` and `.binary .wordMod` expressions.
Do not add Expr aliases or specialized `HasType`, `infer?`, `Expr.rename`, or
`Expr.weakenAt` theorems. The generic binary API already states those facts
without loss of information.

The left operand is always the numerator and the right operand is always the
divisor. This order is part of the semantic interface.

## Required proof interface

Add named value lemmas for both `Word.udiv` and `Word.umod`:

- a zero-divisor result equal to `Word.zero`; and
- a nonzero-divisor unfolding to the existing unsigned quotient or remainder.

Add exact `BinaryOp.apply` lemmas showing that applying `.wordDiv` or
`.wordMod` to two word values returns the corresponding `Word.udiv` or
`Word.umod` value.

Add store-threaded `Evaluates` theorems for each operator:

- a general result from left and right operand evaluations;
- a zero-divisor case returning word zero; and
- a nonzero-divisor case returning the unsigned quotient or remainder.

The general theorems expose the intermediate and final stores. They preserve
the left-to-right, exactly-once evaluation already defined by `Evaluates.binary`.

## Zero-divisor behavior

Zero division is a result policy, not short-circuit control flow. Even when the
right operand eventually produces zero, Core evaluates the numerator once and
then the divisor once. Their effects and faults occur in that order, and the
successful result retains the divisor evaluation's final store.

The unchecked machine still faults for non-word operand values. Well-typed
programs reuse the existing generic Safety proof that makes those operand faults
unreachable.

## Required tests

Focused semantic regressions cover:

- representative quotient and remainder values;
- numerator and divisor zero, one, and maximum-word boundaries;
- word result types and wrong left and right operands;
- a left fault that prevents divisor evaluation;
- a right fault that observes completed numerator effects;
- zero-divisor executions where both operands allocate and write exactly once;
- the exact literal boundary of four transitions insufficient and five
  sufficient;
- measured insufficient and sufficient fuel for effectful operands;
- frozen Wire v1 rejection; and
- exact Wire v2 projection and round trips through the existing `wordDiv` and
  `wordMod` tags.

Compile-time examples exercise every new named theorem. Effectful tests assert
the final store, not merely the returned zero.

## Existing generic proofs

Do not duplicate generic binary typing, inference, arbitrary renaming,
weakening, totality, Safety, progress, preservation, machine correspondence, or
Wire codec proofs. The focused results specialize the already accepted raw
operators.

## Boundaries

No expression form, operation, fault, evaluation rule, machine frame, Wire tag,
schema, version, byte encoding, Oracle behavior, source syntax, ABI rule,
opcode, or gas rule changes. Division and modulo remain unsigned and totalized;
signed arithmetic remains a separate decision.

## Consequences

Callers can reason directly about normal, zero-divisor, and effectful unsigned
division and modulo without unpacking the generic binary rule. The next feature
is selected by a separate ADR; this decision does not choose it.
