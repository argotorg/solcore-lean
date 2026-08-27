# ADR-0033: Complete the direct unary primitive interface

- Status: Accepted
- Decision date: 2026-08-27
- Scope: fifteenth internal Semantic Core vNext slice
- Implementation: In progress

## Context

Core already represents boolean negation and 256-bit word complement directly:

```text
unary(boolNot, operand)
unary(wordNot, operand)
```

The generic typing, evaluation, safety, machine, and Wire v2 layers support both
operators. Existing tests cover part of `boolNot` and the value-level fact that
the complement of word zero is the maximum word. The two direct primitives do
not yet have the focused named proof interface and symmetric regressions used by
newer Core work.

## Decision

Keep the existing raw `.unary` expressions. Do not add `Expr.boolNot` or
`Expr.wordNot` aliases, a derived expansion, or a new operation tag. An alias
would duplicate the existing direct syntax without adding meaning.

Publish named theorems stated directly over the raw expressions:

- `HasType.boolNot` and `HasType.wordNot`;
- `infer_boolNot` and `infer_wordNot`;
- general store-threaded `Evaluates.boolNot` and `Evaluates.wordNot` results;
- boolean true and false evaluation cases;
- word zero and maximum evaluation cases;
- arbitrary `Expr.rename` laws; and
- `Expr.weakenAt` laws.

The general evaluation theorems consume one operand evaluation, return the
operator's existing result, and preserve its final store. They do not introduce
new evaluation rules.

## Word complement facts

Prove `Word.bitNot_zero` and `Word.bitNot_maximum`. These facts state the two
important 256-bit boundaries without changing the existing definition
`maximum - value`.

A universal `Word.bitNot_involutive` theorem is desirable but is not required
for this slice if the proof needs disproportionate new modular-arithmetic
infrastructure for `Fin (2^256)`. The implementation must attempt the compact
proof and record the result. Executable regressions must still check double
complement at zero, one, and maximum, so involution behavior remains protected
even if the universal lemma is deferred.

## Required tests

Focused semantic tests cover:

- both boolean inputs;
- word zero, one, and maximum, including double complement;
- word and boolean result types and wrong operand rejection;
- raw invalid-operand faults for both operators;
- an effectful operand evaluated exactly once with its final store retained;
- exact insufficient and sufficient fuel for literals and effectful operands;
- frozen Wire v1 rejection of both raw unary expressions; and
- exact Wire v2 projection and round trips through the existing `boolNot` and
  `wordNot` tags.

Compile-time examples exercise every named theorem. Literal unary expressions
retain their existing three-transition completion boundary. The effectful fuel
boundary is measured from the unchanged operand expression and unary machine
frames rather than introduced as a new cost rule.

## Existing generic proofs

Do not duplicate `UnaryOp.apply_total_of_type`, result typing, generic Core
safety, progress, preservation, totality, machine correspondence, or renaming
simulation. The named interface is a specialization of those existing results.

## Boundaries

No expression form, operator, evaluator rule, machine frame, fault, type, Wire
tag, version, byte encoding, Oracle behavior, source syntax, ABI rule, opcode,
or gas rule changes. Existing weakening, evaluation, fault, effect, fuel, and
Wire behavior remain normative.

## Consequences

The two direct unary primitives gain a small symmetric proof and regression
surface while remaining raw Core operations. The next feature is selected by a
separate ADR; this decision does not choose it.
