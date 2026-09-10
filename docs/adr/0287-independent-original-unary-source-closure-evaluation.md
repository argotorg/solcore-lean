# ADR-0287: independent original unary source closure evaluation

## Status

Accepted; an opt-in raw source profile over the mixed values of ADR-0286.
Canonical Rust remains fixed at
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
Existing Core, Resolved, raw frontend, checker and executable entry APIs stay unchanged.

## Purpose and boundaries

Define original source closure creation and original unary call sequencing without
using an elaborated Core body, expected type or typing/checker evidence as a premise.
Use independent supplied expression and original-block evaluation relations over
RuntimeValue and ordered raw stores. This is a parametric operational layer, not a
closed recursive evaluator or an executable implementation of arbitrary source.

The fixed resolver keeps lambda parameters in a distinct lexical scope and
resolves a let initializer before adding its new binder
(body_resolver.rs:40–55, 166–184). Fixed closure dispatch evaluates the callee,
then original arguments, before dispatching (evaluate/core.rs:1029–1036).
This is evidence about specialization order, not a proof of general runtime
effect equivalence or a canonical runtime closure object.

Fixed lambda specialization derives parameter mode from the explicit marker OR
the normalized parameter type (specialize/body.rs:780–785). Consequently an
unmarked syntax parameter is not a proven canonical runtime-stage parameter.
Our raw profile ignores parameter/return annotation meaning, just as old raw
typed-let rules ignore annotation meaning. Unknown or comptime type annotations
do not become accepted typed/staged programs because raw evaluation exists.
Canonical staging, annotation typing and their later correctness bridges remain separate.

## Original unary shape

Introduce independent SourceUnaryLambdaShape from the whole original Syntax.Expr
to its original parameter Identifier and original Block. Exactly one parameter
must be present: either inferred or explicitly typed with no comptime marker.
Retain all expression, keyword, list, parameter, annotation and body spans.
Do not normalize a grouped lambda, insert a Unit return annotation, rewrite the
body or resolve type names. The return annotation is unrestricted original data.

Zero/multiple parameters, marked parameters, recovered error parameters and
nonlambda outer shapes have no shape witness. Parser diagnostics are not an input;
an actually recovered inferred/typed name is judged by its actual syntax.
The body may itself be unsupported, ill-typed or unevaluable: creation does not
inspect or run it. A sourceClosure value with arbitrary inert syntax from ADR-0286
is callable here only if its saved original expression has this shape.

Provide sourceUnaryLambdaShape? returning Option (Identifier × Block), with an
exact independent-judgment iff. Keep parameter helpers and shape uniqueness private.

## Raw creation and original call rules

Introduce SourceLambdaEvaluates with two constructors and fixed independent
ChildEval and BodyEval parameters. Both callbacks explicitly take declaration
owner, ordered name/ID rows, ordered ID/RuntimeValue rows, actual initial store,
original syntax, actual result and actual final store. ChildEval receives Expr;
BodyEval receives Block. Stores are List RuntimeValue with no typed-cell guard.

Creation requires only the original unary shape. It returns sourceClosure carrying
the identical original expression, current owner, complete names and captures,
and leaves the actual store unchanged. No body evaluation or capture pruning occurs.

An original .call with exactly one argument evaluates the original callee first,
using the caller owner/names/captures and initial store. Its actual result must be
a sourceClosure. The original argument is evaluated next in the same caller scope
and the actual store left by the callee. Finally, BodyEval evaluates the saved
original body in the captured lexical scope, starting from the argument's final
store. Thread all three evaluations' actual intermediate/final stores explicitly.

Choose the parameter LocalId with freshLocalId savedOwner (savedNames.map Prod.snd).
Prepend the original parameter spelling with that ID to the saved name rows and
prepend the same ID with the actual argument value to the saved capture rows.
Use the saved owner, never the caller owner, for both freshness and body evaluation.
Preserve every old row, duplicate/foreign ID and actual payload. Environment-only
ID collisions are retained, not repaired; freshness is only relative to names.

No store snapshot is taken or restored. Captured references observe invocation-time
stores through the supplied body relation. Actual argument/results may themselves
be source closures, Core closures or arbitrary data; no projection into Core is needed.
Core-closure/host calls are not part of this source-closure-only dispatch layer.

## Proofs and public surface

Target seven public declarations across SourceLambdaEvaluation and
SourceLambdaEvaluationProperties: shape relation, shape decoder, raw evaluation
relation, decoder iff, creation iff under the supplied original shape, exact
original-call decomposition iff, and result/store determinism.

The creation law retains the exact whole source/captures and unchanged store.
The call law exposes the actual saved source/owner/rows, original name/body,
actual argument value and callee/argument/body store sequence.
Determinism requires separate determinism premises for both fixed callbacks;
raw existence does not imply those premises. No typing, alignment, checker,
world, elaboration or Core-evaluation premise may enter these laws.
Every new Lean module remains below 300 lines; do not add a prepared record or
a redundant value-level invocation API.

## Consumers and verification

Use independent raw body/child witnesses before consuming decomposition laws.
Cover actual captured returns, parameter shadowing, different caller/callee owners,
duplicate/misaligned/foreign rows, name-only freshness and environment-only ID
collisions, higher-order actual values and invocation-time reference effects.
Prove creation remains possible with an empty body relation and an unchanged
store, while application needs actual body evidence. Distinguish callee and
argument effects and demonstrate why callback determinism cannot be inferred.

Parse original accepted/unaccepted shapes, including annotated/inferred and
recovered syntax. Unknown/comptime annotation meaning is explicitly outside this
raw profile; do not relabel a raw witness as typing or staging admission.
Keep old whole-entry rejection and Core-only execution claims separate.
Run focused/aggregate/full tests, exact standard-only catalogs, independent
reviews and unchanged old bytes/headers/imports, kernel, metadata and formatting checks.

## Non-goals

No recursive callback closing, mixed Core-body evaluator, global/host resolution,
Core-closure interoperability, fuel/cost/error classifier, source typing or staging,
elaboration correctness, termination, runtime safety or parser/diagnostic proofs.
