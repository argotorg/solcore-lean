# ADR-0179: Exact compiled-function execution factorization

- Status: Accepted
- Decision date: 2026-09-08
- Scope: full runtime correspondence for the existing restricted compiler

## Decision

Complete the semantic bridge from value-free restricted function compilation
to the existing runtime endpoint. Prove an unconditional Option equality:
compile the declaration, test the ordered supplied argument types against the
reverse compiled parameter context, and run the actual compiled Core with the
supplied argument values in reverse source order. This is exactly the result of
`runRuntimeFunction?`, at every fuel and from every initial store.

Do not add a second runner, new evaluator, source-call semantics, or a new
evaluation relation. The factorization is a public proof interface over the
existing endpoints. It justifies reuse of compiled output and supplies the
missing generic contract previously checked only in concrete parsed regressions.

## Contracts

An independent `RuntimeFunctionCompiles` derivation plus the exact ordered
argument-type equality determines the complete Core initial state. Retain
actual argument values, including repeated types with distinct values; arity
and type order are both part of the guard. Parameter binding's exact value-row
layout supplies the environment equality. Do not invent inhabitants or infer
argument availability from static parameter declaration.

The unconditional factorization covers failed compilation and guard rejection
as `none`. On success it preserves the result type and the full stateful result,
not only terminal values: zero-fuel states, suspended continuations, values,
stores, and any result constructor of the unchanged Core machine.

Publish an independent existential characterization of successful runtime
results using compilation evidence, the argument guard, and exact Core execution.
Also connect independently costed function evaluations to this actual compiled
initial state, deriving exact completion/exhaustion thresholds. Typing and
no-fault claims must retain independent compilation or actual compilation
success and matching typed arguments. A hand-built compiled record is data,
not a proof that its Core is well typed or elaborates any declaration.

Use existing preparation, layout, cost, and safety theorems. Keep source
expressions, function profile, static/runtime argument distinction, declaration
identity, and Core semantics unchanged. Equal argument type lists alone do not
make runtime values, costs, or suspended states equal.

## Validation

Add independent consumers with arbitrary supplied typed values, same-type
distinct values in different source positions, exact zero/intermediate states,
and unequal-cost short-circuit paths. Distinguish matching compilation from
wrong arity/type order and from forged compiled data. Fully parse complete
function declarations and compare actual compiled Core with the unchanged
runtime endpoint across argument lists and fuel boundaries, including function
and reference values supplied with their existing typing evidence.

Register and audit all new public declarations. Keep new files below 300 lines,
run focused and aggregate builds, full tests, standard-axiom, kernel,
forbidden-token and whitespace checks, and commit small exact-path units.
Diagnostic proofs remain outside this work.
