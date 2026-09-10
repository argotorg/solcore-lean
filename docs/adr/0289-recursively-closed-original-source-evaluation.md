# ADR-0289: recursively closed original source closure evaluation

## Status

Accepted; callback-free evaluation for a bounded source-syntax fragment.
Canonical Rust remains fixed at
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
Existing Core, Resolved, source lambda/body, checker and entry-point APIs stay unchanged.

## Motivation and representation

ADR-0287 sequences original unary source calls through open expression/body callbacks.
ADR-0288 provides actual original body rules but still takes a child callback.
Close this recursive evaluation explicitly without inserting elaboration, Core
projection, an opaque callback law or an assumed global determinism theorem.

Directly nesting SourceLambdaEvaluates E (SourceComputationBodyEvaluates E) in E
is rejected by Lean's nested-inductive restrictions: existing relation parameters
contain local lexical inputs. Do not change those published parameter contracts.
Instead use an explicit mutually inductive original expression/body pair, with
owner and all lexical inputs as indices. Relate the new body/call forms back to
the independent existing relations through proved iff laws.

Here "closed" refers to recursion between evaluation judgments, not closed source
terms or a ban on free identifiers. Ordered input name/value rows remain explicit.

## Exact syntax fragment

Introduce ClosedSourceExpressionEvaluates and ClosedSourceBodyEvaluates.
Use eight expression constructors: first-match local reference, original empty
tuple Unit, original Word literal, grouping, two-element tuple, right-associated
tuple with at least three elements, supported original source-lambda creation,
and original unary source-closure call. Reuse independent name/ID lookup, Word
literal meaning and SourceUnaryLambdaShape; do not decode annotations as typing.

Preserve original Expr/Block values, spans, delimiters, parameter/return annotation
syntax, and original tuple suffix construction exactly as in existing raw rules.
A singleton tuple AST has no new rule; grouping and tuple syntax are not normalized.
Bool data may be read from captures, but unbound Bool-looking identifiers do not
become new literals. Operators, projections, array/index/constructor/proxy syntax
and multiargument or zero-argument calls are outside this fragment.

Creation stores the entire original source, owner, ordered names and captured
actual mixed values without running its body. A call evaluates callee then
argument in the caller scope, then the saved original body in the saved scope.
Compute the one prepended parameter ID from saved-owner name IDs alone.
Keep arbitrary duplicates, foreign IDs, environment-only collisions, recursively
mixed captures and even manually supplied source-closure data literal.

The mutual body side mirrors all nine ADR-0288 raw forms: bare/expression return,
terminal explicit block, typed/inferred let, semicolon discard, both terminal
Bool branches and terminal single-scrutinee ordered Word match. Initializers
precede binding; original tails use the same block span. Preserve selected-branch
behavior and the independent RuntimeWordMatchChooses judgment without a scope,
coverage, alignment or type guard.

## Laws and proof dependencies

Prove exact equivalence between the new closed body judgment and
SourceComputationBodyEvaluates ClosedSourceExpressionEvaluates, over every
original input/body and actual mixed result/final store. Each direction uses
original body-constructor induction; no Core-value image premise is involved.

For an original unary call, prove exact equivalence between the new expression
judgment and SourceLambdaEvaluates ClosedSourceExpressionEvaluates
(SourceComputationBodyEvaluates ClosedSourceExpressionEvaluates). Use the body
iff to transport saved-body evidence; retain both original child expressions,
saved owner/rows and all actual intermediate stores. This compatibility law
does not claim that non-call reference/literal expressions are lambda steps.

Prove closed expression value/store determinism with one joint induction whose
body motive gives local body hypotheses. Align callee, argument, original source
shape and saved body using those local hypotheses. Do not invoke an unproved
global child law recursively through the old parametric determinism theorem.
Then derive closed body determinism using the body iff and ADR-0288 determinism
with the now-proved closed expression law.

Target six public declarations across three modules: ClosedSourceEvaluation
(the mutual pair), ClosedSourceEvaluationCompatibility (body/call iff), and
ClosedSourceEvaluationProperties (expression/body determinism). Keep each below
300 lines and proof bookkeeping private. No wrapper store or public helper family.

## Boundaries and consumers

This syntax-bounded fragment has no store-mutating primitives or Core/host closure
dispatch. Its successful computations preserve the input store; that boundary
is not a claim of termination, bounded execution depth or an executable interpreter.
Source closures may flow through actual environments, tuples, returns and nested
calls. Arbitrary Core/host closures are inert values here, not new call targets.

The old raw selected-if scope policy remains unchanged. Canonical resolution
visits then/else in one scope, so unrestricted canonical name correspondence
requires separate static/alignment evidence. Unknown/comptime annotations and
unmarked unary syntax do not establish typing or canonical runtime staging.
No old-entry admission, source/Core operational correspondence, fuel, fault,
divergence classification, evaluation costs or runtime safety theorem is added.

Construct independent closed derivations for parsed nested applications,
higher-order arguments/results, captured shadowing, arbitrary tuple nesting and
body wrappers, original if/match selection and excluded syntax boundaries.
Exercise both compatibility directions and unconditional closed determinism.
Preserve actual mixed values and original lexical data without projection gates.
Run direct/focused/aggregate/full tests, exact standard-only public/consumer
catalogs, old-byte/header/import audits, independent reviews and small commits.
