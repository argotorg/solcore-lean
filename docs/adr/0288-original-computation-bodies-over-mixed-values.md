# ADR-0288: original computation bodies over mixed frontend values

## Status

Accepted; a separate raw body family for the mixed value universe.
Canonical Rust remains fixed at
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
All old Core, Resolved, body, lambda, checker and entry-point files stay unchanged.

## Motivation and scope

ADR-0287 makes source closure creation and original unary call sequencing
independent of elaboration, but its original-body callback is supplied externally.
The old ComputationReturnTreeEvaluates still fixes Core.Value and Core.Store.
Provide a separate body relation over RuntimeValue with an explicit-owner mixed
child callback. It can be supplied directly to SourceLambdaEvaluates without
projecting closures or stores into Core or adding a typing premise.

This unit supplies actual original body rules, not recursive closing of expression
and body callbacks. A mixed Core evaluator, whole-source interpreter, staging,
source/Core operational correctness, executable fuel and safety remain separate.

## Ordered mixed Word matching

Introduce RuntimeWordMatchChooses with the same four independent original-choice
constructors as WordMatchChooses, now indexed by RuntimeValue.
Reuse WordMatchPatternClassifies and the original pattern/body data unchanged.
Wildcard and empty-case default accept any actual value, including a source closure.
Literal hit/miss require an actual Word. A non-Word cannot skip an earlier literal
case to reach a later wildcard or default; it has no successful choice there.
Unsupported patterns likewise do not gain a skip rule.

Retain original first-match order, selected original block and literal comparison
count. Do not normalize patterns or inspect unvisited later cases.
No source closure or whole store is projected into Core to decide a match.
Prove choice/count determinism and an exact iff with old WordMatchChooses on
ofCore inputs, including arbitrary non-Word old values and malformed tags/captures.
This is a selector law, not a source execution-cost or fault theorem.

## Original body relation

Introduce SourceComputationBodyEvaluates with a fixed ChildEval taking owner,
ordered name/ID rows, ordered ID/RuntimeValue rows, actual initial store, original
Expr, actual result and actual final store. The body relation takes the same
lexical inputs with an original Block. Stores remain unrestricted List RuntimeValue.

Mirror the nine existing raw body constructors and only those constructors:
bare return, expression return, terminal explicit block, explicitly typed let,
inferred let, semicolon discard followed by a tail, terminal if-true/if-false,
and terminal ordered Word match with one original scrutinee.
There is no empty-body implicit return, uninitialized let, nonterminal if/match,
new binder pattern, annotation interpretation or source normalization.

Typed and inferred let initializers use the old lexical inputs before the new
binder exists. The original tail receives exactly the prepended spelling/ID and
ID/actual-value rows. Compute freshLocalId owner from the current name-row IDs
only, preserving all old rows, duplicate/foreign IDs and environment-only collisions.
Discard consumes its complete child evaluation and actual final store but keeps
the lexical rows unchanged. Returns and explicit blocks preserve original syntax.

If evaluates the actual Bool condition then only the selected original branch.
Word match evaluates its actual original scrutinee, independently chooses the
original branch with RuntimeWordMatchChooses, then evaluates that branch.
Unselected branches and annotation meanings are not checked by raw rules.
No new scope/name-protection guard is added: any later canonical resolved-name
correspondence needs its own static scope evidence, just as for the old raw family.
In particular, fixed resolver if branches are resolved sequentially in one scope;
that does not justify silently changing the existing selected-branch raw contract.

Prove value/store determinism from the fixed child's own value/store determinism.
Do not assume or conclude child completeness, store-length monotonicity, typing,
row alignment, termination, arbitrary-source admission or execution costs.

## Conditional old-body bridges

Preserve old body evidence with a one-way bridge: assuming each old child
evaluation embeds as the mixed child on identical original syntax/name rows,
map all actual Core capture payloads and store slots through RuntimeValue.ofCore.
The mixed body keeps the original block, owner, names and literal result/store.
This premise permits a mixed child to support additional new source behavior.

Separately prove an exact successful-image iff under the stronger child contract:
for every old input environment/store and every actual mixed result/final store,
mixed child success iff there exist old result/store with literal embedding
equalities and old child evidence. The body iff quantifies over all actual mixed
outputs too, not just outputs the caller has already assumed to be embedded.

An iff restricted to old output images is insufficient for reflection, even with
child determinism. A child can return a source closure for an otherwise unsupported
discard expression, then the body discards it and returns old-image Unit.
The old body may have no derivation despite an old-image mixed final result/store.

The stronger image-exact contract is conditional and generally fails for a real
child that creates source lambdas from an embedded environment. Do not label it
full conservativity of the source-lambda extension. The one-way bridge remains
useful when reflection is unavailable. No source/Core closure-value relation or
generated Core execution theorem is hidden in either bridge.

## Public surface and dependencies

Target seven public declarations: RuntimeWordMatchChooses, its ofCore iff and
determinism; SourceComputationBodyEvaluates and its conditional determinism;
old-to-mixed body embedding; and the conditional body exact-image iff.
Use separate RuntimeWordMatch, SourceComputationBodyEvaluation,
SourceComputationBodyEvaluationProperties and
SourceComputationBodyEmbeddingProperties modules, each below 300 lines.
Keep list mapping/reflection helpers private and avoid a new public store wrapper.
Only the compatibility bridge module needs the old raw body import and its old
Core-evaluation dependency; new raw definitions do not inspect old evaluations.

## Consumers and verification

Construct independent child/body evidence before consuming new laws.
Cover all nine body constructors, arbitrary shadowing chains and actual source/
Core closure values, first-match captures, delayed body effects and saved-owner
lambda integration via the existing parametric SourceLambdaEvaluates interface.
Use non-Word wildcard/default successes and literal-first failure boundaries,
unvisited unsupported cases and preserved original selected branches/counts.
Test forward embedding with extra mixed behavior and refute weak reflection
using a deterministic child with a discarded source-closure result.
Cover a genuinely image-exact child instance for both directions of the stronger law.

Keep callback models explicit and bounded, without a closed-evaluator claim.
Run focused/aggregate/full tests, exact standard-only public and consumer catalogs,
independent reviews, unchanged old bytes/headers/imports, kernel, metadata,
EOF, whitespace and small-commit checks.
