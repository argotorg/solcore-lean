# ADR-0038: Complete direct word comparison interfaces

- Status: Accepted
- Decision date: 2026-08-27
- Scope: twentieth internal Semantic Core vNext slice
- Implementation: Complete

## Context

Core already has two direct word comparisons:

```text
binary(wordEq, left, right)
binary(wordGt, left, right)
```

Both return booleans. `wordGt` is strict unsigned greater-than. Generic typing,
inference, renaming, weakening, evaluation, Safety, machine, and Wire support
already exist, but the raw operations lack a small named proof interface and
focused boundary regressions.

## Decision

Retain the existing raw expressions and their semantics. Each evaluates the
left operand exactly once, then the right operand exactly once, and retains the
right evaluation's final store. Do not add an `Expr` alias, Word-level duplicate,
operation tag, evaluation rule, or duplicate generic typing, inference,
renaming, weakening, or Safety theorem.

Publish exactly eight named theorems:

- `BinaryOp.apply_wordEq` and `BinaryOp.apply_wordGt`;
- `Evaluates.wordEq`, `Evaluates.wordEq_eq`, and `Evaluates.wordEq_ne`; and
- `Evaluates.wordGt`, `Evaluates.wordGt_gt`, and
  `Evaluates.wordGt_not_gt`.

The general evaluation theorems expose intermediate and final stores. Case
theorems state boolean results for equality/inequality and strict unsigned
greater-than/not-greater-than.

Existing raw `.binary` construction in `ComparisonFlags` and
`DerivedComparisonEval` may use the new helper interface when that is a small
refactor. Such use must preserve the exact expression and semantics.

## Required tests

Focused regressions cover:

- zero, one, maximum, equal, unequal, greater, and not-greater values;
- boolean results, wrong declared result types, and wrong operand types;
- raw invalid-operand faults for both operations;
- a left fault that skips the right and a right fault after visible left effects;
- two allocating and writing operands, their left-to-right exactly-once order,
  and the final store;
- exact literal 4/5 and effectful 28/29 fuel boundaries.

## Boundaries

This slice does not define signed comparison, source or standard-library APIs,
opcode lowering, or gas. It changes no type, value, fault, evaluator, frame,
tag, schema, version, byte encoding, or published boundary. Derived comparison
builders and flags retain their meaning.

## Consequences

The existing boolean word comparisons gain concise reusable application and
store-threaded evaluation results without expanding Core. Further conversions
and primitives remain separate ADR decisions.

## Implementation result

All eight named theorems are implemented: two exact `BinaryOp.apply` equations
and six store-threaded general/case evaluation theorems. `ComparisonFlags` and
`DerivedComparisonEval` now reuse the direct evaluation helpers without
changing their expressions or semantics.

Tests cover zero, one, maximum, equality, inequality, strict greater-than, and
not-greater-than results; boolean result typing and invalid result/operand
types; raw invalid operands and ordered left/right faults; and two allocating,
writing operands with the exact final store. Literal evaluation has the exact
4/5 fuel boundary and effectful evaluation the exact 28/29 boundary.

The implementation, focused Wire suite, semantic suite, and independent audit
are complete. The audit found no P0-P3 issue, no source trust escape hatch, and
only the repository-approved Lean foundational dependencies. No alias,
duplicate Word or generic theorem, tag, or schema changed. The next feature
requires a separate ADR.
