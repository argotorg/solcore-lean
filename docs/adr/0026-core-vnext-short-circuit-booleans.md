# ADR-0026: Semantic Core vNext short-circuit boolean operators

- Status: Accepted
- Decision date: 2026-08-27
- Scope: eighth internal Semantic Core vNext vertical slice
- Implementation: Complete

## Context and authority

Accepted ADR-0011 already fixes boolean conjunction and disjunction as deferred
derived operations with selected-branch-only behavior. The Core has conditionals
and boolean literals, so that decision can now be implemented without extending
the expression algebra.

Some reference evaluators reach ordinary `and` or `or` functions only after
evaluating both call arguments. Those eager calls are not the semantics of the
operators decided here. Versioned Lean rules and Accepted ADRs are authoritative;
reference Haskell, Rust, compiler, and backend behavior is comparison evidence.
An eager reference call therefore cannot override ADR-0011's explicit
short-circuit equations.

## Decision

The internal Core library provides two derived expression builders:

```text
boolAnd(x, y) = ifE x y false
boolOr(x, y)  = ifE x true y
```

Both have signature:

```text
bool × bool -> bool
```

Their value behavior is ordinary boolean conjunction and disjunction, but the
branching behavior is part of the decision: `boolAnd` evaluates `y` only when
`x` is true, and `boolOr` evaluates `y` only when `x` is false.

The typing rules are:

```text
Gamma |- x : bool    Gamma |- y : bool
---------------------------------------
Gamma |- boolAnd(x, y) : bool

Gamma |- x : bool    Gamma |- y : bool
---------------------------------------
Gamma |- boolOr(x, y) : bool
```

These are derived forms, not new Core tags. Inference, checking, big-step
evaluation, CEK execution, safety, and fuel behavior are inherited from the
expanded conditionals.

## Evaluation order, stores, faults, and fuel

The left operand occurs exactly once and is evaluated first. Its resulting
store becomes the branch store. The right operand also occurs exactly once in
the syntax, but it is evaluated only in the selected branch. A skipped right
operand cannot allocate, write, fault, or consume evaluation transitions.

When the right operand is selected, it starts from the left operand's resulting
store, and its resulting store is the final store. When it is skipped, the left
operand's resulting store is the final store. Existing unchecked-machine faults
remain exactly those of the handwritten expansion: a left-condition fault
prevents branch evaluation, and a fault in `y` is observable only when `y` is
selected. Fuel use likewise follows the selected conditional path rather than
an eager two-operand cost.

## Core and wire boundary

This slice adds no type, value, expression, primitive operation, frame,
transition, machine fault, diagnostic, schema, profile, capability, or Oracle
tag. It adds no big-step rule or CEK transition.

Wire v1 and wire v2 both project each builder exactly as the corresponding
handwritten `ifE` expression using their existing conditional and boolean forms.
No new encoding exists, and decoding that expansion reconstructs only the
ordinary conditional tree. Frozen schemas and golden bytes do not change.

## Required implementation, proof, and tests

- define both builders solely by the equations in this ADR;
- prove named expansion equalities and commutation with `Expr.weakenAt`;
- prove declarative typing and executable `infer?` results;
- prove all four left-boolean cases and general store-threaded evaluation;
- prove that the left operand is evaluated once and the right operand only in
  the selected branch, including preservation of the correct final store;
- show existing correspondence, safety, typed-result, and sufficient-fuel
  theorems apply without new syntax-indexed cases;
- test all boolean value pairs and rejection of non-boolean operands;
- test effectful left and right operands, including skipped allocation/write;
- test that skipped faults are unobservable and selected faults are preserved;
- test exact fuel boundaries for selected and skipped paths; and
- test wire v1 and v2 projection equality with handwritten expansions and the
  absence of new tags or capabilities.

## Deferred

This ADR does not add eager boolean primitives, source spelling or overload
resolution, implicit truthiness, word-level bitwise aliases, optimizer
replacement, ABI decoding, or a new public Core or Oracle version.

## Consequences

Short-circuit boolean behavior becomes an explicit reusable Core target while
remaining ordinary conditional semantics. Future elaborators must select these
builders, not eager ordinary calls, when implementing boolean operators.

The implementation provides the named expansions, typing and inference
theorems, and all four store-threaded branch evaluations. Tests cover truth
tables, operand types, skipped and selected faults, allocation and writes,
left-to-right store threading into the selected right operand, exact fuel,
weakening, and exact wire v1 and v2 projection of the handwritten expansions.
