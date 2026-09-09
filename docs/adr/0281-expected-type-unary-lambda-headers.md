# ADR-0281: expected-type unary lambda headers

## Status

Accepted; a new opt-in frontend header foundation, not lambda execution or whole
lambda checking. Canonical Rust is fixed at
`18fd9f75d290df0070e21ee56e0a5691f232596f`. Old source adapters, judgments,
executable definitions and their contracts remain unchanged.

## Canonical evidence and limits

At the fixed pin, `crates/hir-ty/src/infer/expr.rs:938–1080` distinguishes a
lambda with an expected function type from inference without an expected type.
An unannotated parameter receives the corresponding expected domain. A typed
parameter is checked against that domain. An omitted lambda return annotation
uses the expected codomain; it is not implicitly Unit. An explicit return
annotation is checked against that codomain.

`crates/hir/src/nameres/body_resolver.rs:166–184` resolves annotations before
entering a fresh lambda scope. Its inner-first lookup and scope push/pop at
832–836 and 936–965 retain outer bindings while allowing a parameter to shadow
an outer spelling. The existing Lean type-only inputs and owner-filtered fresh
IDs provide the adapter's explicit representation of that inner scope.

The named-function parameter and return policies are different: they require
explicit parameter annotations, reject repeated spellings in their input scope,
and use Unit for an absent named-function return clause. Do not reuse those
policies for an expected-type lambda header.

The preliminary function-index candidate is not admitted. Its type-inference
fallback does not supply call semantics: specialization retains `Index`, and the
fixed emitter rejects surviving index access. Numeric field projections likewise
cannot be inferred from an internal representation without source-parser support.

## Decision

Add `ExpectedUnaryLambdaHeader` with independent parameter, return-annotation
and original-header judgments. Restrict the expected type to an explicitly
supplied `Core.Ty.function parameterType returnType` and the original source to
a lambda with exactly one runtime parameter.

The parameter may be inferred or carry a non-comptime structural annotation.
For an inferred parameter use the expected domain directly, without a runtime
inhabitant or an extra well-formedness assumption. For an annotation require its
independent structural meaning to equal that domain. Resolve meanings using the
unchanged outer type-name table before binding the parameter.

An omitted return annotation agrees with any supplied expected codomain. A
present annotation must independently denote that codomain. This is a concrete
structural fragment, not general unification, alias normalization, inference
variables, type-class solving or inference of a nominal closure type.

Produce a `DeclaredUnaryLambdaHeader` containing the type-only inner inputs,
original body, expected domain and expected codomain. Bind exactly one fresh
parameter row on the front of the untouched outer rows, using the original
spelling and existing owner-filtered fresh-ID construction. Do not require that
the spelling be absent from the outer scope. Preserve original syntax and spans;
there is no annotation or body rewriting and no runtime argument construction.

Expose only one executable entry point, `declareExpectedUnaryLambdaHeader?`.
Keep parameter and return checkers private. Prove its exact iff with the
independent header judgment, exact absence, result uniqueness and original
header provenance with the fresh-row layout. Explicit error parameter nodes,
comptime parameters, non-unary headers, non-function expected types and
unsupported or mismatched annotations remain outside this opt-in profile.
Parser recovery diagnostics are not inputs to this semantic API: a recovered
inferred/typed node is judged by its actual AST, not a diagnostic-free premise
or a forbidden-spelling test.

## Body boundary and consumers

Header success deliberately does not inspect or type-check the original body.
The output has no Core expression, closure or runtime value. An unresolved,
ill-typed or recovered body can still have a valid header. A later body checker
must independently establish the declared return type using these inner inputs.
Existing recursive-child and shared-function checkers still reject source
lambdas; none of their admission branches change here.

Use independent symbolic and parsed consumers. Cover arbitrary supplied expected
types without inhabitants, inferred/explicit annotation agreement, first-match
type names, outer same-name shadowing, sparse same-owner and foreign-owner IDs,
exact original body/spans, wrong arity, annotation absence and mismatch, and
header success followed by separate body success or failure. Do not evaluate a
source lambda by inserting elaboration evidence into a raw evaluation judgment.

Verify focused and aggregate builds, full tests, exact standard-only public and
consumer axiom catalogs, independent reviews, old bytes/signatures/imports,
kernel/metadata/EOF/whitespace checks. Keep new proof/consumer files below 300
lines and decision, implementation/proofs, consumers and publication in small
separate commits.

## Non-goals

No source closure construction or capture conversion, raw lambda semantics,
expected-type propagation through the recursive checker, multi-parameter or
comptime lambdas, general inference or name/type resolution, return-body typing,
lambda admission in the shared engine, parser/diagnostic work or runtime safety.
Literal-value insertion contracts are not weakened to make closures fit.
