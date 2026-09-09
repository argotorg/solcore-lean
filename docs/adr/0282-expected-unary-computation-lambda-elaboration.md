# ADR-0282: expected unary computation lambda elaboration

## Status

Accepted; additive standalone frontend elaboration with an explicit expected
function type. Canonical Rust remains fixed at
`18fd9f75d290df0070e21ee56e0a5691f232596f`. Existing recursive-child, body and
function entry points, source admission and literal insertion contracts remain
unchanged.

## Evidence and preceding boundary

ADR-0281 prepares a type-only inner scope and retains the original unchecked
lambda body. Its success is not evidence that the body returns the expected
codomain. At the fixed pin, `crates/hir-ty/src/infer/expr.rs:938–1080` checks the
original body with the lambda return type on its return stack, after assigning
expected parameter types and adding parameters to a new inner scope. An omitted
return annotation inherits the expected codomain, not the named-function Unit
policy. Inference without an expected function type follows a different nominal
closure path and is not the profile chosen here.

`crates/hir/src/nameres/body_resolver.rs:166–184` resolves annotations in the
outer scope before parameters and the original body in the inner scope.
`crates/specialize/src/specialize/body.rs:744–824` retains outer locals, inserts
parameters and specializes the original statements in a nested body context.
These support the explicit inner-input/body boundary, not a claim that Lean's
positional Core representation equals canonical local identifiers.

`crates/hull/src/emit/emitter.rs:702–720` rejects surviving Mono lambdas on that
emission path; 763–770 has a separate known-function callee path. Producing a
Lean Core lambda must not be reported as general canonical backend closure
execution, or as a language-wide impossibility of executing every lambda.

Core lambda typing additionally requires both component types to be well formed.
The wider ADR-0281 header accepts arbitrary supplied types, and a variable body
can be typed at a named-data type absent from the empty data environment. Header
success plus body typing therefore cannot alone justify Core lambda typing.

## Decision

Add a generic opt-in `ExpectedComputationLambda` module. Take an unchanged
original source expression, outer type-name table, owner, type-only inputs, and
an explicit expected type. Reuse the independent expected-header judgment to
recover the original body and the exact fresh parameter row. Add an independent
`ExpectedComputationLambdaElaborates` judgment whose constructor requires:

- the original header declaration at the supplied function type;
- independent well-formedness of its domain and codomain in the empty Core data
  environment used by the existing shared body typing interface;
- an independent `ComputationReturnTreeElaborates` derivation of the original
  body, under exactly those inner inputs, at exactly the expected codomain.

Its result is the literal Core lambda with those component types and that body
Core. The child elaboration relation is a parameter, not a checker graph.
Do not require child determinism, runtime arguments, a store, a world, captured
values or an inhabitant of either component type to state this judgment.

Expose `elaborateExpectedComputationLambda?`, parameterized by the existing
child checker. Check the original header, both component well-formedness guards,
and the original body using the unchanged shared computation return-tree
checker. Require the computed body type to equal the expected codomain. Return
only the resulting Core expression; the expected type is already an input.
There is no fabricated source annotation, rewritten body or default return type.

Prove exact checker/independent-elaboration correspondence and exact absence
using only the fixed child's own exact checker correspondence. Separately prove
Core typing from independent elaboration and the child's own Core-typing law;
that theorem does not require the executable checker or its correctness. Expose
original-header/body provenance and fresh inner scope by retaining, not
reconstructing, the header evidence. Private helpers should not enlarge the API.
Keep implementation and proof files below 300 lines each.

Well-formedness guards are an explicit limitation of this fixed Core profile,
not a claim that canonical named-data types are invalid. The outer scope need
not acquire a new blanket well-formedness assumption. Generic children remain
responsible for their own typing: exact checker correspondence alone must not
be mistaken for child or lambda Core safety.

## Consumers and validation

Use independent symbolic and parsed original-body derivations before exercising
the checker laws. Cover inferred and typed parameters, explicit and omitted
return annotations, same-name shadowing, preserved outer rows, owner-filtered
fresh IDs, captured-variable positions, structural products/functions, and
existing effectful shared bodies. Contrast header-only success with body type
mismatch, unsupported/error bodies and component well-formedness failure.
Demonstrate that a dishonest generic child does not acquire Core typing merely
from exact checker correspondence. Preserve old source-lambda rejection tests.

Any test of the produced Core lambda's existing machine transition is explicitly
a Core consumer: it retains the complete supplied environment and delays body
effects until application. It is not a new source evaluation judgment or a
source-to-Core operational correspondence theorem.

Run focused and aggregate builds, full tests, public and consumer exact
standard-only axiom catalogs, independent reviews, old byte/header/import
checks, kernel/metadata/EOF/whitespace checks. Keep the decision, implementation
and proofs, consumers, and publication in small separately verified commits.

## Non-goals

No changes to recursive-child, shared body or named-function source admission;
no automatic expected-type propagation into nested lambdas, general inference,
unification, nominal resolution or nonempty data environments. No new raw source
lambda evaluator, capture conversion, operational correspondence, backend
execution guarantee, runtime safety theorem or literal-value insertion change.
Diagnostics and parser proofs remain paused.
