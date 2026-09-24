# ADR-0021: Semantic Core vNext binary sums

- Status: Accepted
- Decision date: 2026-08-27
- Scope: third internal Semantic Core vNext vertical slice

## Context

Products represent values that contain both components. The Core also needs a
typed way to represent a value that is one of two alternatives and to branch
on that choice. This is the smallest useful foundation for optional results,
error values, and later algebraic data.

Source-level constructor names and pattern syntax are likely to evolve. Their
design is not required to define binary alternatives after elaboration.

## Decision

The internal Core adds:

- a binary sum type with left and right payload types;
- a left injection carrying the right alternative's type;
- a right injection carrying the left alternative's type; and
- exhaustive case elimination with one branch for each alternative.

The absent alternative annotation lets an injection have a complete type
without inspecting source syntax. Runtime injection values retain that
annotation so their internal type remains available to diagnostics and tests.

Case elimination evaluates its scrutinee exactly once. If the result is a left
injection, only the left branch runs; if it is a right injection, only the
right branch runs. The selected payload is de Bruijn index zero in that branch,
followed by the surrounding lexical environment in its existing order.

Both branches must produce the same result type. The unchecked machine reports
a structured fault when a case scrutinee produces neither injection.
Well-typed programs cannot reach that fault.

## Boundary

This decision does not add named data types, constructor identities, nested
pattern syntax, guards, non-exhaustive matching, catch-all ordering, or a
source-elaboration rule. Later named algebraic data may elaborate to sums and
products or receive a separate Core representation; this ADR does not decide
that question.

No equality, ordering, hashing, ABI encoding, or storage layout operation is
added for sum values.

## Required implementation

- nestable sum types and left/right injected values;
- declarative and executable typing;
- detailed paths for payloads, scrutinees, and both branches;
- diagnostics for a non-sum scrutinee and mismatched branch results;
- big-step injection and selected-branch evaluation;
- CEK frames and transitions preserving scrutinee-first execution;
- evaluator/machine correspondence and determinism;
- value, frame, state, and logical-reducibility coverage;
- progress, preservation, total evaluation, sufficient fuel, and fault
  exclusion;
- weakening beneath both branch binders; and
- focused nesting, selection, order, diagnostic, exact-fuel, and interaction
  tests.

## Consequences

The logical relation gains a sum case: a reducible sum value contains either a
reducible left payload or a reducible right payload. This is structurally
recursive in the sum type, so the non-recursive language retains total
evaluation and sufficient-fuel results.

The Core can express typed alternatives without committing the future source
language to a particular pattern or constructor syntax.
