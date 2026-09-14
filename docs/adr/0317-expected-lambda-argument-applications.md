# ADR-0317: Expected unary lambdas in application arguments

## Status

Accepted; an additive opt-in frontend adapter for one singleton application
whose locally inferable callee supplies the expected type of a direct unary
lambda argument. Existing expression checkers, source evaluators, parsers and
diagnostics remain unchanged.

## Context

ADR-0281 through ADR-0283 check an original unary lambda when an explicit
function type is already available. ADR-0284 and ADR-0285 propagate an explicit
typed-let annotation to direct lambda initializers. No application checker yet
passes its callee's parameter type to a lambda argument: the existing recursive
local checker tries to infer the argument independently and therefore rejects a
direct source lambda.

The singleton application path already infers a callee as
`Core.Ty.function parameterType resultType`. That exact `parameterType` is the
required expected-type input. Requiring callers to split the application and
manually combine two unrelated successful checks would leave the original
source shape and literal Core application outside one exact frontend contract.

Global function resolution is not a smaller substitute. The current frontend
has no global function lookup table, local-versus-global shadowing policy,
declaration-owner assignment rule, or recursive closure environment. Those
choices precede any honest global-call theorem.

## Decision

Add `ExpectedLambdaArgumentApplication` as a narrow opt-in adapter. Its
independent elaboration judgment has one constructor retaining:

- the exact original singleton call, callee, direct lambda argument and spans;
- an existing `RecursiveLocalComputationElaborates` derivation of the callee at
  `parameterType -> resultType`;
- an existing `ExpectedComputationLambdaElaborates` derivation of the argument
  at that literal `parameterType`; and
- the literal Core result `Core.Expr.apply functionCore argumentCore` at
  `resultType`.

Expose `elaborateExpectedLambdaArgumentApplication?`. It first runs the
unchanged recursive local checker on the original callee. Only a function
result continues. It then invokes the unchanged expected computation-lambda
checker on the original argument using the recovered parameter type. There is
no fallback after a recognized singleton call fails, no fabricated annotation,
and no rewriting or grouping of the original argument.

Prove exact optional-checker correspondence, exact absence, Core typing from
the two independent component typings, and one-layer provenance. Checker
exactness must reuse the existing recursive-expression and expected-lambda
correspondence laws; it must not infer source semantics from `Core.infer?` or
from a successful final application alone.

## Independent consumers

A symbolic consumer constructs the callee and original lambda elaborations
before using the new checker law. It retains sparse and foreign-owner rows,
duplicate names, exact source spans and a higher-order callee whose parameter
is `Word -> Word`. It demonstrates that the old recursive checker rejects the
whole call while the new adapter produces the literal typed Core application.

A parsed consumer checks the complete original source, lexer/parser diagnostics,
file span and EOF. It independently recovers the callee lookup, lambda header,
body elaboration and Core execution before consuming the new iff theorem.
Negative controls cover a non-function callee, wrong lambda body result,
zero/multiple arguments, a non-lambda argument and a top-level lambda.

## Preserved boundaries

This slice admits only a direct unary lambda as the sole argument of a
singleton application. The callee must already elaborate through the unchanged
local recursive checker. It does not propagate expected types into grouped
lambdas, nested application arguments, tuples, conditional branches, return
expressions or inferred lets, and it does not add ordinary-argument fallback.

No global/source-function resolution, multi-parameter packing, currying policy,
recursive closure construction, raw source evaluation, source/Core closure
identity, runtime-world safety, cost/fuel relation, backend execution guarantee,
principal inference, coercion, overload resolution or whole-language
compilation follows. A successful static adapter neither creates a source
closure nor supplies runtime inhabitants.

Keep each proof or consumer file below 300 lines and every commit within 300
changed lines. Verify focused and aggregate builds, full tests, exact public
axioms, declaration ownership, source-policy scans and independent consumers.
