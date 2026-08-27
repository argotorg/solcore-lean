# ADR-0019: Semantic Core vNext binary products

- Status: Accepted
- Decision date: 2026-08-27
- Scope: first internal Semantic Core vNext vertical slice

## Context

The published Core supports only unit, boolean, and word values. A richer Core
needs structured values before functions, algebraic data, ABI values, and
contract observations can be represented cleanly.

Binary products are a bounded first extension. They exercise syntax, typing,
checking, evaluation, the CEK machine, correspondence, and safety without
introducing recursion or weakening the existing sufficient-fuel theorem.

## Decision

The internal Core adds:

- a binary product type with left and right component types;
- a pair expression and pair value;
- first and second projection expressions.

Pair components evaluate exactly once, left first and right second. A
projection evaluates its operand exactly once before selecting the requested
component.

Declarative typing is:

- a pair of values with types A and B has type product A B;
- first applied to product A B has type A;
- second applied to product A B has type B.

The unchecked machine has a structured fault when a projection receives a
non-pair value. Well-typed programs cannot reach that fault.

Unit remains the nullary product representation. This ADR does not choose how
a future Surface tuple with more than two elements nests into binary products;
that belongs to an elaboration decision.

## Boundary

This feature is internal. It adds no tag to Semantic Core v1 or v2 and changes
no Oracle v2 or v3 profile.

The frozen wire projections return no representation for:

- product types;
- pair expressions;
- projection expressions;
- pair values; and
- programs containing those forms.

Product equality, ordering, hashing, ABI encoding, storage layout, Surface
syntax, and source diagnostics are outside this decision.

## Required implementation

- recursive product types and pair values;
- declarative and executable typing;
- detailed checker paths and a non-product projection diagnostic;
- big-step pair and projection evaluation;
- CEK frames and transitions preserving left-to-right order;
- evaluator/machine correspondence and determinism;
- value, environment, frame, and state typing;
- progress, preservation, typed results, sufficient fuel, and fault exclusion;
- focused execution, diagnostic, nesting, order, and wire-isolation tests.

## Consequences

Core type and value equality become recursive. Frozen wire languages remain
closed because conversion from the internal Core is a rejecting projection.

The feature provides a useful template for later sum and algebraic-data
extensions while retaining all termination properties of the current language.
