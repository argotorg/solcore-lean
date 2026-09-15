# ADR-0331: Three-level-grouped-conditional-first local applications

## Status

Accepted; add one nonrecursive source-only wrapper that selects the complete
ADR-0330 result before the complete unchanged ADR-0329 result.

## Context

ADR-0330 is the standalone exact-singleton adapter for an immediate conditional
beneath exactly three transparent whole-expression groups when at least one
immediate branch is an ungrouped direct computation lambda. ADR-0329 is the
current complete local-application entry: its true branch is the exact ADR-0328
two-group conditional result, and its false branch is the complete ADR-0327
result with all older conditional and finite direct-lambda-group precedence.

Every ADR-0330 candidate is false for ADR-0329's ADR-0328 classifier because the
second group immediately contains a third group rather than a conditional.
ADR-0329 therefore returns the complete ADR-0327 `Option`; on all three new
ADR-0330 success partitions this is literally `none`. On classifier-selected
ADR-0330 semantic failure, the predecessor value is irrelevant and must not be
inspected. Dispatch after a failed checker would make precedence depend on
semantic success instead of the frozen source partition.

Editing ADR-0329, copying its nested dispatch, or introducing recursive group
traversal would reopen frozen behavior. The smallest additive integration is a
two-child wrapper around the complete ADR-0330 and ADR-0329 results. It adds no
new expression, type, Core or runtime semantics.

The reviewed baseline is HEAD
`4df01d49cfabb15a35f345d12efc471071d4e01e`. Frozen ADR-0329 decision and
production SHA-256 values are
`66db228670af823b7a8952e5037540055ed4c87d87127610fbf43326fe68dc16` and
`4367b3582e81e743eceb6b80b2044bc05532e2805d2240d93a7c71e878749b5d`.
Frozen ADR-0330 decision and production SHA-256 values are
`56722882d91754beab547ca3d357542b6dfba1129644395645d824185eef24ca` and
`d4a6ad3f3f52980817e263aa591b9c09a0436d70b729a9e03dc4bb02fe9ce705`.
Its final independent semantic audit is GREEN with zero issues at SHA-256
`71fab2d633c00ea4a9bce7dd4a88f6c5222a0d44d56f940ab617d20be9916616`.

## Decision

Add `LocalApplicationWithThreeLevelGroupedConditionalExpectedLambda` as a
separate additive wrapper. Evaluate the unchanged
`isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication` classifier
once on the unchanged original `Syntax.Expr`:

```text
if ADR0330-classifier(source)
then exact ADR0330 Option(source)
else exact ADR0329 Option(source)
```

The true branch returns
`elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?`
literally. The false branch returns
`elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?`
literally. Classification stays source-only: it does not read owner, tables,
resolution, inferred types, diagnostics, checker results or runtime observations.

A classifier-true `none` is final. Do not invoke ADR-0329 after selected failure,
use `Option.orElse`, retry until a checker succeeds, remove or add groups, rebuild
or normalize the source, rewrite spans, or change either child. Conversely, every
classifier-false input preserves the complete ADR-0329 `Option`, both `some` and
`none`, including ADR-0329's nested ADR-0328-before-ADR-0327 precedence.

Add no classifier, combined classifier, path enum, group extractor, recursion,
fuel, termination argument, source reconstruction, source union, runtime node,
generic failure theorem or change to ADR-0329/ADR-0330.

## Declarative and executable interface

Define `LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates`
with exactly two constructors:

1. `threeLevelGroupedConditional` retains
   `isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = true`
   and a complete
   `ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates`
   child;
2. `existing` retains the same classifier equal to `false` and a complete
   `LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates`
   child.

Expose exactly these eight authored public roots:

1. `LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates`;
2. `elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?`;
3. `elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_threeLevelGroupedConditional`;
4. `elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing`;
5. `elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_iff`;
6. `elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_eq_none_iff`;
7. `LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates.core_hasType`;
8. `LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates.provenance`.

Both branch theorems are universal literal complete-`Option` equations. The
success theorem is exact executable/declarative correspondence, and the failure
theorem equates checker `none` with absence of every Core/type relation witness.
Typing delegates directly to the selected complete child. Provenance is the exact
disjunction of the classifier equation plus complete ADR-0330 child provenance,
or the false equation plus complete ADR-0329 wrapper and nested-child provenance.
Do not add a wrapper classifier or `classified` theorem; the unchanged ADR-0330
Boolean and its negation are already the complete partition.

## Independent symbolic consumer

Create
`Solcore/Test/FrontendLocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaProperties.lean`
strictly below 300 lines with exactly three authored public roots. Keep every
fixture and helper private. Reuse the established sparse table: first-match
`apply` is Core variable 0 with `(Word -> Word) -> Word`, a later duplicate has
`Unit`, foreign-owner `flag` is variable 3 with `Bool`, `ordinary` is variable 4
with `Word -> Word`, and unrelated foreign opaque and wrong rows remain present.

The true route covers all three ADR-0330 exact-depth-three branch partitions:
lambda/ordinary, ordinary/lambda and lambda/lambda. For each, independently
construct the complete ADR-0330 relation before the wrapper relation. Freeze the
classifier equation, exact true-branch equation, literal complete checker
result/Core/type, Core typing, and both wrapper and complete three-group child
provenance.

Use exactly these ten classifier-true selected-failure categories:

- non-Bool condition and unresolved condition;
- malformed immediate-lambda header and malformed body;
- wrong-typed ordinary branch and unresolved ordinary branch;
- non-function callee and unresolved callee; and
- a direct lambda opposite a grouped direct lambda, and a direct lambda opposite
  a nested-call lambda.

Every selected-failure row proves exact ADR-0330 `none`, wrapper equality to that
same `none`, and no ADR-0329 inspection or fallback.

The classifier-false complete-Option matrix has exactly sixteen shapes:

- immediate, one-group, two-group and four-group conditionals;
- exact-depth-three all-ordinary, grouped-only and nested-only branch shapes;
- direct lambdas at group depths zero, one, two, three and four;
- an ordinary singleton, zero arguments, multiple arguments and a top-level
  non-call.

For every false row prove the whole wrapper result equals the complete ADR-0329
`Option`, not only equality of successful Core terms. Construct the complete
ADR-0329 relation and retain its wrapper/child provenance wherever evidence
exists. Expose the universal false-branch equation for an arbitrary source.

Also preserve actual `none` for exactly eleven inherited or boundary examples:
representative selected failures from ADR-0328, ADR-0326, ADR-0324, ADR-0323,
ADR-0322, ADR-0320 and ADR-0317, followed by tuple, nested-call, returned-lambda
and inferred-let-lambda boundaries. Do not claim ADR-0330 accepts a neighboring
shape or that ADR-0329 changes on any false source.

Aggregate exactly three public roots: complete true/false dispatch with nested
provenance; exact runtime controls; and selected/inherited failures plus universal
complete ADR-0329 preservation.

## Independent parsed consumer

Create
`Solcore/Test/FrontendParsedLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda.lean`
strictly below 300 lines with exactly three authored public roots, including one
IO runner registered exactly once in `Tests.Main`. Require clean lexer/parser
diagnostics, EOF, full-file span and proof-producing structural equality to each
hand-built AST; never derive propositional equality from `BEq`.

Freeze the primary true-route text:

```text
apply((((flag ? lam(x){return x;} : ordinary))))
```

Its exact half-open spans are call/full file `0..48`, callee/name `0..5`, arguments
`5..48`, outer group `6..47`, middle group `7..46`, inner group `8..45`,
conditional `9..44`, condition/name `9..13`, question `14..15`, then lambda
`16..33`, colon `34..35`, and ordinary identifier/name `36..44`. Lambda keyword,
parameters, parameter/name, body, return statement and returned identifier/name
spans are `16..19`, `19..22`, `20..21`, `22..33`, `23..32` and `30..31`.

Cover the other two true partitions with:

```text
apply((((flag ? ordinary : lam(x){return x;}))))
apply((((flag ? lam(x){return x;} : lam(y){return y;}))))
```

For all three sources prove the exact AST, complete ADR-0330 child, wrapper
relation, classifier and branch equation, literal checker/Core/type, Core typing,
and nested wrapper/child provenance. The primary Core is exactly
`apply (var 0) (ifE (var 3) (lambda Word Word (var 0)) (var 4))`.

Mirror all ten symbolic selected failures and the complete false and inherited
matrices with parsed source. Use exactly twenty-seven complete ADR-0329
preservation rows: the sixteen false shapes above plus the eleven actual inherited
or boundary failures. Every false row proves literal whole-`Option` equality to
ADR-0329; every true failure proves the selected ADR-0330 `none` is final.

Freeze proof-producing exact ASTs and spans for the two-group predecessor,
four-group conditional boundary and three-group direct-lambda predecessor. The
four-group text `apply(((((flag ? lam(x){return x;} : ordinary)))))` has call/full
span `0..50`, arguments `5..50`, group spans `6..49`, `7..48`, `8..47`, `9..46`,
and conditional `10..45`. The three-group direct-lambda source
`apply((((lam(x){return x;}))))` has call `0..30`, arguments `5..30`, group spans
`6..29`, `7..28`, `8..27`, and lambda `9..26`.

## Runtime contract

The wrapper returns the selected child Core verbatim and adds no runtime step.
Use the exact nonempty environment and store containing an opaque closure, cell
reference and host function. For each of the three ADR-0330 Cores and both Boolean
choices, independently retain `Core.Evaluates`, `runStateful_evaluation_sound`
and determinism. Fuel 13 is exactly `outOfFuel`; fuel 14 is exactly
`done (Word 7)` with the identical store.

Immediate, one-group and two-group conditional controls retain 13/14. Direct and
finite-group expected-lambda controls retain 10/11. Neither wrapper branch changes
Core, environment, store, evaluation cost or result.

## Preserved and deferred boundaries

ADR-0317 through ADR-0330, every existing classifier, relation, checker and theorem,
ADR-0329's complete nested precedence, `RecursiveLocalComputation`, the shared
ADR-0324 branch checker, canonical source unions, runtime entries and public wire
versions remain textually and semantically unchanged. ADR-0331 adds only
reachability and fixed precedence.

The next smallest standalone semantic leaf is exactly four whole-expression groups
around the same immediate conditional. Do not add that leaf or its later selecting
wrapper here. Five or more groups and any generic/deeper grouped-conditional spine,
grouped conditional branch lambdas, nested conditional/call, tuple, return,
inferred-let and typed-body expected propagation, multiple arguments, global
resolution, source-union integration, source closures, runtime-world safety, costs
and backend guarantees remain deferred. Parser and diagnostic proof work remains
paused.

Preserve exactly the existing eight untracked pause files under `Solcore/Syntax`
and `Solcore/Syntax/Parser`; do not stage, edit or remove them.

## Prototype, verification and delivery contract

Before production, freeze a production-shaped scratch prototype and audit its
source hash, direct and trust-zero compiled artifact hashes, exact owned/generated
declarations, public/private split, safe/total flags, public simp/proof leaks and
complete axiom closure. Permit only `propext`, `Classical.choice` and `Quot.sound`;
forbid `sorry`, `admit`, authored `axiom`, `unsafe`, `native_decide`, `partial`,
`noncomputable`, `extern`, `implemented_by`, `bv_decide` and `termination_by`.
Port the audited theorem bodies unchanged.

Deliver exactly six commits over exactly these nine unique tracked paths:

1. decision: `docs/adr/0331-three-level-grouped-conditional-first-local-applications.md`;
2. production: `Solcore/Frontend/LocalApplicationWithThreeLevelGroupedConditionalExpectedLambda.lean`;
3. symbolic consumer: `Solcore/Test/FrontendLocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaProperties.lean`;
4. parsed consumer: `Solcore/Test/FrontendParsedLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda.lean`;
5. registration: `Solcore/Frontend.lean` and `Tests/Main.lean`;
6. documentation: `docs/CURRENT_STATUS.md`, `docs/FEATURE_MATRIX.md` and
   `docs/M2_PLAN.md`.

Keep the decision, production and both consumers strictly below 300 lines. Keep
every commit at no more than 300 changed lines. Stage only the exact paths for its
commit; do not create a seventh completion commit or include scratch/paused files.

Before closure verify exact ownership/generated names, safe/total flags, root and
all-owned axiom closure, masked forbidden-source and line-limit scans, both literal
branch equations, selected-failure finality, and universal complete ADR-0329
preservation; direct/focused/umbrella/aggregate builds, direct parsed runner and
full tests; registration counts; exact six-commit/nine-path range; preservation of
ADR-0317 through ADR-0330 and all paused files; source/olean drift and dependency
closure. Do not record a final ADR-0331 implementation commit hash in this decision.
