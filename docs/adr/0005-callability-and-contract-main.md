# ADR-0005: Callability and the Contract Runtime Entry

- Status: Accepted
- Decision date: 2026-07-23
- Scope: static semantics and contract entry

## Context

The Haskell compiler sometimes accepts examples that call a value annotated as
`word`. This is a false acceptance in which the value's type does not agree
with its callability.

A contract-local `main` suppresses generated dispatch, while the Haskell
compiler also accepts a parameterized `main`. The runtime convention invokes
the entry without arguments, so the execution meaning of such a program is
undefined.

A value with valid invokable evidence must remain callable even when its
source-level form is not an ordinary function name, as with an explicit
closure representation.

## Decision

- Only values with a function type, or values carrying
  specification-defined invokable evidence, may be the callee of a call
  expression.
- Calling a non-callable value, including a `word`, `bool`, or ADT value,
  produces `rejected` in the static phase.
- An explicit closure representation with the correct type and evidence is
  accepted.
- When source code defines `main` as the contract runtime entry, `main` must
  have zero parameters.
- The arity of `main` is checked during contract validation, before dispatch or
  lowering.
- The same arity rule applies when a local `main` suppresses generated
  dispatch.

This ADR does not decide the return type of `main`, payability, fallback
behavior, or constructor semantics. Subsequent ADRs on contract semantics will
decide those matters.

## Consequences

- Types and evidence determine callability, not the syntactic form of a
  callee.
- Static semantics cannot be bypassed merely because a backend can transform a
  value in function position.
- A parameterized contract `main` is rejected consistently, independently of a
  compiler-specific runtime convention.
- The source checker does not incorrectly reject a valid explicit
  representation produced by closure conversion.

## Conformance Requirements

- A positive test must cover an ordinary function call.
- A positive test must cover an explicit closure carrying invokable evidence.
- A minimal negative test must use a `word` as the callee.
- A negative test must cover a non-callable ADT value.
- A positive test must cover a zero-argument contract `main`.
- A contract `main` with one or more parameters must be rejected before
  dispatch.
