# ADR-0337: Six-level-grouped-conditional-first local applications

## Status

Accepted; add one nonrecursive source-only wrapper that selects the complete
ADR-0336 result before the complete unchanged ADR-0335 result.

## Context

ADR-0336 is the standalone exact-singleton adapter for an immediate conditional
beneath exactly six transparent whole-expression groups when at least one
immediate branch is an ungrouped direct computation lambda. ADR-0335 is the
current complete local-application entry: its true branch is the exact ADR-0334
five-group conditional result, and its false branch is the complete unchanged
ADR-0333 result with all older conditional and finite direct-lambda-group
precedence.

Every ADR-0336 candidate is false for ADR-0335's ADR-0334 classifier because the
fifth group immediately contains a sixth group rather than a conditional.
ADR-0335 therefore returns the complete ADR-0333 `Option`; on all three new
ADR-0336 success partitions this is literally `none`. On classifier-selected
ADR-0336 semantic failure, that predecessor value is irrelevant and must not be
inspected. Dispatch after a failed checker would make precedence depend on
semantic success instead of the frozen source partition.

Editing ADR-0335, copying its nested dispatch, or introducing recursive group
traversal would reopen frozen behavior. The smallest additive integration is a
two-child wrapper around the complete ADR-0336 and ADR-0335 results. It adds no
new expression, type, Core or runtime semantics.

The reviewed baseline is final ADR-0336 HEAD
`5c0e6450e565cb5060447d9c4e1311495c7bdd9d`. Frozen ADR-0336 decision,
production, symbolic-consumer and parsed-consumer SHA-256 values are
`aa3ed396e47c3af282d33892a3a1f28addf0489cbeeb3108b78fc3ce8039c660`,
`518355410f3b34a533a25580ce35922b44e7b92bc7c51816f31b881b1df843f1`,
`b13369aae8716498d09b767b7ab1e86c627d860104559727c6e560211bf018e3` and
`38a7ecd2ffc4af0d6d445efed2b5905b0d02c33bf05863cbbca71b795499c41c`.
The final independent ADR-0336 completion freeze is GREEN with zero issues at
`.lake/trace-audits/ADR0336CompletionIndependent.json`, SHA-256
`045b258b9583885afa8c9347fc28155c8061b0d2b55d800579630a022f762463`.

The production-shaped ADR-0337 wrapper prototype is frozen at
`.lake/trace-audits/ADR0337LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaPrototypeIndependent.lean`,
151 lines and SHA-256
`c41aaad59b6e13e3483520bcf34905160c5478fb6facf735f6c4164c62957aeb`.
Its GREEN zero-issue audit has SHA-256
`9fcf55e8d2ddbb0c1a30c2274cc34e31e3fb1f374f7601766d0ddcd364fa1e78`.

## Decision

Add `LocalApplicationWithSixLevelGroupedConditionalExpectedLambda` as a
separate additive wrapper. Evaluate the unchanged
`isSixLevelGroupedConditionalExpectedLambdaArgumentApplication` classifier once
on the unchanged original `Syntax.Expr`:

```text
if ADR0336-classifier(source)
then exact ADR0336 Option(source)
else exact ADR0335 Option(source)
```

The true branch returns
`elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?`
literally. The false branch returns
`elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?`
literally. Classification stays source-only: it does not read owner, tables,
resolution, inferred types, diagnostics, checker results or runtime observations.

A classifier-true `none` is final. Do not invoke ADR-0335 after selected failure,
use `Option.orElse`, retry until a checker succeeds, remove or add groups, rebuild
or normalize the source, rewrite spans, or change either child. Conversely, every
classifier-false input preserves the complete ADR-0335 `Option`, both `some` and
`none`, including ADR-0335's ADR-0334-before-ADR-0333 nested precedence.

Add no classifier, combined classifier, path enum, group extractor, recursion,
fuel, termination argument, source reconstruction, source union, runtime node,
generic failure theorem or change to ADR-0335/ADR-0336.

## Declarative and executable interface

Define `LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates`
with exactly two constructors:

1. `sixLevelGroupedConditional` retains
   `isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = true`
   and a complete
   `SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates` child;
2. `existing` retains the same classifier equal to `false` and a complete
   `LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates`
   child.

Expose exactly these eight authored public roots, mechanically isomorphic to the
measured ADR-0335 wrapper API of 8 roots, 15 owned declarations, 15 public and
zero private:

1. `LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates`;
2. `elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?`;
3. `elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_of_sixLevelGroupedConditional`;
4. `elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_of_existing`;
5. `elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_iff`;
6. `elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_eq_none_iff`;
7. `LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates.core_hasType`;
8. `LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates.provenance`.

Both branch theorems are universal literal complete-`Option` equations. The
success theorem is exact executable/declarative correspondence, and the failure
theorem equates checker `none` with absence of every Core/type relation witness.
Typing delegates directly to the selected complete child. Provenance is the exact
disjunction of the classifier equation plus complete ADR-0336 child provenance,
or the false equation plus complete ADR-0335 wrapper and nested-child provenance.
Do not add a wrapper classifier or `classified` theorem; the unchanged ADR-0336
Boolean and its negation are already the complete partition.

Production imports only the exact ADR-0336 leaf and complete ADR-0335 wrapper and
must be the mechanical ADR-0335 wrapper extension, expected at 151 lines and
strictly below 300. Advance only the selected classifier/child and wrapper names
by one level.

## Independent symbolic consumer

Create
`Solcore/Test/FrontendLocalApplicationWithSixLevelGroupedConditionalExpectedLambdaProperties.lean`
strictly below 300 lines with exactly three authored public roots. Keep every
fixture and helper private. Reuse the established sparse table: first-match
`apply` is Core variable 0 with `(Word -> Word) -> Word`, a later duplicate has
`Unit`, foreign-owner `flag` is variable 3 with `Bool`, `ordinary` is variable 4
with `Word -> Word`, and unrelated opaque, wrong and unresolved rows remain.
Port ADR-0336's already frozen planned-dispatch obligations to the real public
wrapper and remove the private `planned` dispatcher; a duplicate local selector
is not an acceptable substitute for exercising ADR-0337.

The true route covers all three ADR-0336 exact-depth-six branch partitions:
lambda/ordinary, ordinary/lambda and lambda/lambda. For each, independently
construct the complete ADR-0336 relation before the wrapper relation. Freeze the
classifier equation, exact true-branch equation, literal complete checker
result/Core/type, Core typing, and both wrapper and complete six-group child
provenance. Also freeze that current ADR-0335 returns exactly `none` for all three.

Use exactly these ten classifier-true selected-failure categories:

- non-Bool condition and unresolved condition;
- malformed immediate-lambda header and malformed body;
- wrong-typed ordinary branch and unresolved ordinary branch;
- non-function callee and unresolved callee; and
- a direct lambda opposite a grouped direct lambda, and a direct lambda opposite
  a nested-call lambda.

Every selected-failure row proves exact ADR-0336 `none`, wrapper equality to that
same `none`, and no ADR-0335 inspection or fallback.

The classifier-false complete-Option matrix has exactly twenty-two shapes:

- immediate and one- through five-group conditionals, plus a seven-group
  conditional;
- exact-depth-six all-ordinary, grouped-only and nested-only branch shapes;
- direct lambdas at group depths zero through seven; and
- an ordinary singleton, zero arguments, multiple arguments and a top-level
  non-call.

For every false row prove the whole wrapper result equals the complete ADR-0335
`Option`, not only equality of successful Core terms. The exact outcomes are
sixteen `some` and six `none`: six shallower conditionals, exact-six all-ordinary,
eight direct-lambda depths and ordinary singleton are `some`; the seven-group
conditional, grouped-only, nested-only, zero, multiple and top-level rows are
`none`. Construct the complete ADR-0335 relation and retain its wrapper and
nested-child provenance wherever evidence exists. Expose the universal false
branch equation for an arbitrary source.

Also preserve actual `none` for exactly fourteen inherited or boundary examples:
representative selected failures from ADR-0334, ADR-0332, ADR-0330, ADR-0328,
ADR-0326, ADR-0324, ADR-0323, ADR-0322, ADR-0320 and ADR-0317, followed by tuple,
nested-call, returned-lambda and inferred-let-lambda boundaries. Do not claim
ADR-0336 accepts a neighboring shape or that ADR-0335 changes on any false source.

The exact runtime-selection list has seventeen sources: the three new successes,
six conditional controls at depths zero through five, and eight direct-lambda
controls at depths zero through seven. Aggregate complete true/false dispatch
with nested provenance, exact runtime controls, and selected/inherited failures
plus universal complete ADR-0335 preservation into exactly three public roots.
Those roots are exactly
`all_three_six_level_grouped_conditional_partitions_have_exact_semantics`,
`all_selected_and_control_cores_have_exact_fuel_and_store` and
`selected_failures_and_complete_adr0335_options_are_exact` in the isolated
ADR-0337 consumer namespace.

## Independent parsed consumer

Create
`Solcore/Test/FrontendParsedLocalApplicationWithSixLevelGroupedConditionalExpectedLambda.lean`
strictly below 300 lines with exactly three authored public roots, including one
IO runner registered exactly once in `Tests.Main`. Require clean lexer/parser
diagnostics, EOF, full-file span and proof-producing structural equality to each
hand-built AST; never derive propositional equality from `BEq`.
The roots are exactly `parsed_six_group_wrapper_static_contract`,
`independently_executed_six_group_wrapper_core` and
`Tests.adr0337ParsedLocalApplicationWithSixLevelGroupedConditionalExpectedLambdaTests`.
Replace every ADR-0336 planned selector observation with the actual wrapper and
retain no parsed-consumer shadow dispatcher.

Reuse the ADR-0336 primary true-route text:

```text
apply(((((((flag ? lam(x){return x;} : ordinary)))))))
```

Its exact half-open spans are call/full file `0..54`, callee/name `0..5`,
arguments `5..54`, group spans `6..53`, `7..52`, `8..51`, `9..50`, `10..49`,
`11..48`, conditional `12..47`, condition/name `12..16`, question `17..18`,
lambda `19..36`, colon `37..38`, and ordinary identifier/name `39..47`. Lambda
keyword, parameters, parameter/name, body, return statement and returned
identifier/name spans remain `19..22`, `22..25`, `23..24`, `25..36`, `26..35`
and `33..34`.

Cover the other two true partitions with the exact ADR-0336 texts:

```text
apply(((((((flag ? ordinary : lam(x){return x;})))))))
apply(((((((flag ? lam(x){return x;} : lam(y){return y;})))))))
```

For all three sources prove the exact AST, complete ADR-0336 child, wrapper
relation, classifier and branch equation, literal checker/Core/type, Core typing,
and nested wrapper/child provenance. The primary Core is exactly
`apply (var 0) (ifE (var 3) (lambda Word Word (var 0)) (var 4))`.

Mirror all ten symbolic selected failures and the complete false and inherited
matrices. Use exactly thirty-six complete ADR-0335 preservation rows: the
twenty-two false shapes above plus the fourteen actual inherited or boundary
failures. Their exact outcomes are sixteen `some` and twenty `none`. Every false
row proves literal whole-`Option` equality to ADR-0335; every true failure proves
the selected ADR-0336 `none` is final. Retain proof routes rather than only
runtime equality.

Freeze proof-producing exact ADR-0336 ASTs and spans for the five-group
predecessor, seven-group conditional boundary and six-group direct-lambda
control. Their exact source texts and call/full spans are respectively
`apply((((((flag ? lam(x){return x;} : ordinary))))))` at `0..52`,
`apply((((((((flag ? lam(x){return x;} : ordinary))))))))` at `0..56`, and
`apply(((((((lam(x){return x;})))))))` at `0..36`. The predecessor group spans
are `6..51`, `7..50`, `8..49`, `9..48`, `10..47`, with conditional `11..46`.
The boundary group spans are `6..55`, `7..54`, `8..53`, `9..52`, `10..51`,
`11..50`, `12..49`, with conditional `13..48`. The lambda control group spans
are `6..35`, `7..34`, `8..33`, `9..32`, `10..31`, `11..30`, with lambda
`12..29`.

## Runtime contract

The wrapper returns the selected child Core verbatim and adds no runtime step.
With the exact nonempty opaque/cell/host environment and store, retain
`Core.Evaluates`, `runStateful_evaluation_sound`, determinism and identical store.
Fuel 13 is exactly `outOfFuel`; fuel 14 is `done (Word 7)`. Conditional controls
at depths zero through five retain 13/14; direct-lambda controls at depths zero
through seven retain 10/11. No runtime cost, result or store changes.

## Preserved, deferred and delivery boundaries

ADR-0317 through ADR-0336, every existing classifier, relation, checker and
theorem, ADR-0335's complete nested precedence, `RecursiveLocalComputation`, the
ADR-0324 branch checker, canonical source unions, runtime entries and wire
versions remain textually and semantically unchanged. This adds one opt-in
wrapper only.

ADR-0338 is the next standalone step for the exact seven-group conditional.
Eight or more groups, a generic/deeper grouped-conditional spine, grouped branch
lambdas, broader expected propagation, source-union integration, source closures,
runtime-world safety, costs and backend guarantees remain deferred.
Parser/diagnostic proof work remains paused, including the existing eight files.
Do not stage, edit or remove any of those eight untracked pause files.

Deliver exactly six commits over exactly nine unique tracked paths:

1. this decision at
   `docs/adr/0337-six-level-grouped-conditional-first-local-applications.md`;
2. `Solcore/Frontend/LocalApplicationWithSixLevelGroupedConditionalExpectedLambda.lean`;
3. the symbolic consumer path above;
4. the parsed consumer path above;
5. additive registration in `Solcore/Frontend.lean` and `Tests/Main.lean`; and
6. updates to `docs/CURRENT_STATUS.md`, `docs/FEATURE_MATRIX.md` and
   `docs/M2_PLAN.md`.

Keep the decision, production and both consumers strictly below 300 lines, and
every commit at no more than 300 changed lines. Use `set_option autoImplicit false`.
Stage only the exact paths for each commit; create no seventh completion commit.
Forbid `sorry`, `admit`, authored `axiom`, `unsafe`, `native_decide`, `partial`,
`noncomputable`, `extern`, `implemented_by`, `bv_decide` and `termination_by`.
Before closure verify exact production 8/15/15/0 and consumer 3/3 roots,
safe/total flags, public simp/proof leaks, axiom closure limited to `propext`,
`Classical.choice` and `Quot.sound`, masked source, selected-failure finality,
universal complete ADR-0335 preservation and exact 16/6 and 16/20 partitions,
normal/trust-zero/warnings/direct/full
builds and tests, runner, registration, exact six-commit/nine-path scope,
dependency and source/olean parity, kernel/metadata and unchanged paused files.
Do not record a final ADR-0337 implementation commit hash in this decision.
