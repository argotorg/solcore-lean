# ADR-0031: Derive word-valued flags for the remaining comparisons

- Status: Accepted
- Decision date: 2026-08-27
- Scope: thirteenth internal Semantic Core vNext slice
- Implementation: Complete

## Context

Core already has the boolean-valued derived builders `wordNe`, `wordLt`,
`wordLe`, and `wordGe`. ADR-0024 also provides `boolToWord`, which maps false
to word zero and true to word one. ADR-0028 uses that conversion for equality
and unsigned greater-than flags.

The remaining comparisons need the same word-valued interface for internal
semantic composition. They do not need new primitive operations or evaluation
rules.

## Decision

Add four derived expression builders with these canonical expansions:

```text
wordNeFlag(left, right) = boolToWord(wordNe(left, right))
wordLtFlag(left, right) = boolToWord(wordLt(left, right))
wordLeFlag(left, right) = boolToWord(wordLe(left, right))
wordGeFlag(left, right) = boolToWord(wordGe(left, right))
```

Each builder returns word one when its boolean comparison is true and word zero
when it is false. The names distinguish these word-valued flags from the
existing boolean-valued builders.

These definitions are ordinary compositions of existing Core expressions.
They add no Core form, primitive tag, evaluation rule, fault, wire version, or
wire behavior.

## Evaluation order

The underlying comparison determines operand evaluation. The left expression
is evaluated exactly once, followed by the right expression exactly once.
`wordLtFlag` and `wordGeFlag` retain the nested-let and right-operand weakening
from `wordLt` and `wordGe`; replacing those forms with a syntax-level operand
swap is forbidden.

The `boolToWord` wrapper evaluates the comparison once and selects only its
canonical result branch. It must preserve the comparison's fault order,
intermediate effects, final store, and existing CEK fuel accounting.

## Implemented interface

Each builder provides:

- a named canonical expansion theorem;
- `HasType` and executable `infer?` results with word output;
- `Expr.rename` and `Expr.weakenAt` laws;
- a store-threaded big-step evaluation theorem; and
- true and false case corollaries returning canonical word one or zero.

The typed assumptions required by the existing `wordLt` and `wordGe`
evaluation theorems remain explicit in their flag counterparts. The other two
builders do not gain unnecessary typing assumptions.

The implementation provides four builders, four named expansions, four
`HasType` results, four `infer?` results, and renaming and weakening laws for
each builder. Four general store-threaded evaluations and eight true/false case
corollaries return canonical word one or zero.

## Implemented tests

Focused regressions cover:

- true and false results for all four builders, including zero and maximum;
- checker acceptance, word result types, and wrong-operand rejection;
- left-first raw faults and exactly-once left-to-right effects;
- final-store preservation with allocating and writing operands;
- exact insufficient and sufficient fuel for every derived form; and
- rejection by frozen Wire v1 plus exact Wire v2 projection and round trips
  against the handwritten canonical expansions.

Compile-time examples exercise the public typing, inference, and evaluation
theorems.

The fault regressions also cover the binder boundary in `wordLtFlag` and
`wordGeFlag`: weakening the right expression lifts an unbound variable index
under the internal left-value binding. The reported index is therefore shifted,
while the fault still occurs after the completed left store and before any
right-side effect.

## Boundaries

This is an internal Core vNext proof-and-builder slice. It adds no source
spelling, standard-library declaration, ABI conversion, opcode, gas rule,
schema field, or published behavior. Further primitives and conversions remain
separate decisions.

## Consequences

All existing unsigned word comparisons have both boolean-valued and canonical
word-valued derived interfaces. Their underlying meaning, evaluation order,
faults, effects, stores, and wire encoding remain unchanged.

Further primitives and conversions are selected by separate ADRs; this slice
does not choose the next feature.
