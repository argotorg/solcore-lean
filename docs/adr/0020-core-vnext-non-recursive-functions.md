# ADR-0020: Semantic Core vNext non-recursive functions

- Status: Accepted
- Decision date: 2026-08-27
- Scope: second internal Semantic Core vNext vertical slice

## Context

Binary products established structured values without changing the Core's
termination guarantees. The next useful capability is reusable computation:
functions that can capture surrounding immutable bindings and later receive an
argument.

Recursion is deliberately later in the roadmap. Combining it with the first
function implementation would also combine two separate questions: how calls
work, and how potentially diverging programs change the current totality and
sufficient-fuel claims.

## Decision

The internal Core adds:

- a function type with one parameter type and one result type;
- a lambda expression carrying both type annotations and a body;
- an application expression with a callee and one argument; and
- a closure value carrying the lambda body, its annotations, and the lexical
  environment present when the lambda was evaluated.

The parameter is de Bruijn index zero in the lambda body. Existing captured
bindings follow it in their original order.

A lambda evaluates immediately to a closure. Application then:

1. evaluates the callee exactly once;
2. evaluates the argument exactly once in the caller's environment; and
3. evaluates the body in the captured environment extended with the argument.

The callee therefore runs before the argument, and the argument runs before
the body. The body continues with the caller's existing continuation; no
separate source-level return construct is introduced.

Declarative typing checks the body under the parameter type followed by the
surrounding context. The inferred body type must equal the lambda's declared
result type. Application requires the callee's parameter type to equal the
argument type.

The unchecked machine reports a structured fault when application receives a
non-closure callee. Well-typed programs cannot reach that fault.

## Boundary

This feature contains no recursion, self-reference, named function binding,
multiple-argument convention, polymorphism, effects, or explicit return.
Multiple arguments can be represented by nesting unary functions, but no
Surface-language elaboration rule is fixed here.

The feature is internal. It adds no tag to Semantic Core v1 or v2 and changes
no Oracle v2 or v3 profile. Frozen wire projections reject function types,
lambda and application expressions, closure values, and programs containing
them.

Closure equality is structural only because the internal Lean data types need
decidable equality for tests and machine results. This ADR does not make
closure equality available as a Core primitive or observable language
operation.

## Required implementation

- nestable function types, lambdas, applications, and lexical closures;
- declarative and executable typing;
- detailed paths for lambda bodies, callees, and arguments;
- distinct diagnostics for a non-function callee, an argument mismatch, and
  a lambda result mismatch;
- big-step closure and application evaluation;
- CEK frames and transitions preserving callee-before-argument order;
- evaluator/machine correspondence and determinism;
- value, environment, frame, and state typing for captured environments;
- progress, preservation, typed results, sufficient fuel, and fault exclusion;
- weakening beneath a lambda binder; and
- focused capture, shadowing, order, diagnostic, exact-fuel, fault, and frozen
  wire tests.

## Consequences

Runtime value typing can no longer be reconstructed from a value's displayed
type annotation alone: a closure is well typed only when its body and captured
environment agree. Safety proofs must therefore carry that evidence explicitly
and prove primitive results directly instead of relying on a generic
type-annotation converse.

Because calls remain non-recursive, every well-typed expression still has a
big-step result and enough CEK fuel can still be exhibited. Recursion will be a
separate decision that revisits those claims explicitly.
