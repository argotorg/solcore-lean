# ADR-0028: Semantic Core vNext word-valued comparison flags

- Status: Accepted
- Decision date: 2026-08-27
- Scope: tenth internal Semantic Core vNext vertical slice
- Implementation: Complete

## Context

The Core already has boolean-valued word equality and unsigned greater-than,
plus canonical boolean-to-word conversion. Some internal consumers need the
same predicates encoded as word one or zero. The pinned Haskell and Rust Yul
evaluators provide comparison evidence by returning numeric one or zero for
`eq` and `gt`.

This evidence does not change the existing Core operations. `wordEq` and
`wordGt` remain boolean-valued and authoritative for their existing semantics.

## Decision

The internal Core library provides two derived expression builders:

```text
wordEqFlag(left, right) =
  boolToWord(binary wordEq left right)

wordGtFlag(left, right) =
  boolToWord(binary wordGt left right)
```

Both have type `word × word -> word`. A true comparison returns canonical word
one and a false comparison returns word zero. `wordGtFlag` uses the existing
unsigned word ordering.

The left operand is evaluated exactly once before the right operand, which is
also evaluated exactly once. The right operand starts from the left operand's
final store. Conversion preserves the comparison's final store and introduces
no allocation or write. Unchecked faults and their order are exactly those of
the handwritten expansion: a left fault prevents right evaluation, and an
invalid comparison is observed before conversion.

These are derived forms. They add no type, value, expression, primitive,
frame, transition, fault, diagnostic, schema field, Core, CEK, or wire tag.

## Naming and alternatives

The `Flag` suffix distinguishes canonical word encoding from existing
boolean-valued `wordEq` and `wordGt`. Overloading or changing those names would
obscure result types and break an established semantic boundary.

New word-returning primitive tags are rejected because the exact behavior is
already expressible. Names such as `eqWord` or opcode-shaped aliases are not
chosen: this ADR defines an internal typed Core convenience, not a source API,
standard-library function, or instruction mapping.

## Required implementation, proof, and tests

- define both builders solely by the normative expansions and prove them;
- prove declarative typing and executable `infer?` results;
- prove general left-to-right, exactly-once, store-threaded evaluation;
- prove equal/unequal and greater/not-greater canonical one/zero results;
- prove commutation with `Expr.weakenAt`;
- test equality, unsigned boundaries, operand types, and raw unchecked faults;
- test left/right allocation and writes, order, and final-store preservation;
- test exact sufficient and insufficient fuel boundaries.

## Exclusions

This ADR defines no source spelling, public API, standard-library commitment,
ABI encoding or decoding, opcode identity, gas schedule, signed comparison, or
optimizer rule.

## Consequences

Internal consumers gain explicit word-valued comparison flags while the Core's
existing boolean comparisons and all published boundaries remain unchanged.

The implementation provides named expansions, typing and inference, general
store-threaded evaluation and equality, inequality, greater, and not-greater
case theorems, plus weakening. Tests cover values and unsigned boundaries,
types and raw fault order, two allocating and writing operands with the exact
final store, literal 7/8 and effectful 31/32 fuel boundaries, preservation of
the existing boolean comparisons, and the canonical expansions. Warning,
trust, axiom, test, and whitespace audits pass.
