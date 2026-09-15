# ADR-0335: Five-level-grouped-conditional-first local applications

## Status

Accepted; add one nonrecursive source-only wrapper that selects the complete
ADR-0334 result before the complete unchanged ADR-0333 result.

## Context

ADR-0334 is the standalone exact-singleton adapter for an immediate conditional
beneath exactly five transparent whole-expression groups when at least one
immediate branch is an ungrouped direct computation lambda. ADR-0333 is the
current complete local-application entry: its true branch is the exact ADR-0332
four-group conditional result, and its false branch is the complete unchanged
ADR-0331 result with all older conditional and finite direct-lambda-group
precedence.

Every ADR-0334 candidate is false for ADR-0333's ADR-0332 classifier because the
fourth group immediately contains a fifth group rather than a conditional.
ADR-0333 therefore returns the complete ADR-0331 `Option`; on all three new
ADR-0334 success partitions this is literally `none`. On classifier-selected
ADR-0334 semantic failure, that predecessor value is irrelevant and must not be
inspected. Dispatch after a failed checker would make precedence depend on
semantic success instead of the frozen source partition.

Editing ADR-0333, copying its nested dispatch, or introducing recursive group
traversal would reopen frozen behavior. The smallest additive integration is a
two-child wrapper around the complete ADR-0334 and ADR-0333 results. It adds no
new expression, type, Core or runtime semantics.

The reviewed baseline is final ADR-0334 HEAD
`4c8b5ca4e20060ddd48df2f459e6641ec188990b`. Frozen ADR-0333 decision and
production SHA-256 values are
`e66c74b90938cb5f920fe98523b30d827b335503f5e47609ea6fa3ada9662b12` and
`2e96652168c86923b8e5dca2452c7c1bd2a7e2b622ef1c3d303f5f485a65e5b9`.
Frozen ADR-0334 decision, production, symbolic-consumer and parsed-consumer
SHA-256 values are
`2d293c68b3e4a4ed6be6b261b999a30a978058d0d265da51d0d10e2ca37d82ea`,
`252cfdc97273443138a696a5fe9aaa0355d003e3f4eebcde2f00e8ff65e67c98`,
`0ae8c6cb1f12bda63c2ebb0566382cfbcf201a30dfcb228141deca6758231900` and
`774adfa393f60f315ced76608e9cae0294dd9fef1005a421aee00b8be81d59de`.
The final independent ADR-0334 completion freeze is GREEN with zero issues at
`.lake/trace-audits/ADR0334CompletionIndependent.json`, SHA-256
`cb2bbffbce95de29cff976daf2bd6c289800f61780e464befc9c74f1580ff465`.

## Decision

Add `LocalApplicationWithFiveLevelGroupedConditionalExpectedLambda` as a
separate additive wrapper. Evaluate the unchanged
`isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication` classifier once
on the unchanged original `Syntax.Expr`:

```text
if ADR0334-classifier(source)
then exact ADR0334 Option(source)
else exact ADR0333 Option(source)
```

The true branch returns
`elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?`
literally. The false branch returns
`elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?`
literally. Classification stays source-only: it does not read owner, tables,
resolution, inferred types, diagnostics, checker results or runtime observations.

A classifier-true `none` is final. Do not invoke ADR-0333 after selected failure,
use `Option.orElse`, retry until a checker succeeds, remove or add groups, rebuild
or normalize the source, rewrite spans, or change either child. Conversely, every
classifier-false input preserves the complete ADR-0333 `Option`, both `some` and
`none`, including ADR-0333's ADR-0332-before-ADR-0331 precedence.

Add no classifier, combined classifier, path enum, group extractor, recursion,
fuel, termination argument, source reconstruction, source union, runtime node,
generic failure theorem or change to ADR-0333/ADR-0334.

## Declarative and executable interface

Define `LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates`
with exactly two constructors:

1. `fiveLevelGroupedConditional` retains
   `isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = true`
   and a complete
   `FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates`
   child;
2. `existing` retains the same classifier equal to `false` and a complete
   `LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates`
   child.

Expose exactly these eight authored public roots, mechanically isomorphic to the
measured eight-root ADR-0333 wrapper API:

1. `LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates`;
2. `elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?`;
3. `elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_fiveLevelGroupedConditional`;
4. `elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_existing`;
5. `elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff`;
6. `elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_eq_none_iff`;
7. `LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates.core_hasType`;
8. `LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates.provenance`.

Both branch theorems are universal literal complete-`Option` equations. The
success theorem is exact executable/declarative correspondence, and the failure
theorem equates checker `none` with absence of every Core/type relation witness.
Typing delegates directly to the selected complete child. Provenance is the exact
disjunction of the classifier equation plus complete ADR-0334 child provenance,
or the false equation plus complete ADR-0333 wrapper and nested-child provenance.
Do not add a wrapper classifier or `classified` theorem; the unchanged ADR-0334
Boolean and its negation are already the complete partition.

The production implementation must be the mechanical ADR-0333 wrapper extension,
expected at approximately 151 lines and strictly below 300. Advance only the
selected classifier/child and wrapper names by one level.

## Independent symbolic consumer

Create
`Solcore/Test/FrontendLocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaProperties.lean`
strictly below 300 lines with exactly three authored public roots. Keep every
fixture and helper private. Reuse the established sparse table: first-match
`apply` is Core variable 0 with `(Word -> Word) -> Word`, a later duplicate has
`Unit`, foreign-owner `flag` is variable 3 with `Bool`, `ordinary` is variable 4
with `Word -> Word`, and unrelated foreign opaque and wrong rows remain present.

The true route covers all three ADR-0334 exact-depth-five branch partitions:
lambda/ordinary, ordinary/lambda and lambda/lambda. For each, independently
construct the complete ADR-0334 relation before the wrapper relation. Freeze the
classifier equation, exact true-branch equation, literal complete checker
result/Core/type, Core typing, and both wrapper and complete five-group child
provenance. Also freeze that current ADR-0333 returns exactly `none` for all three.

Use exactly these ten classifier-true selected-failure categories:

- non-Bool condition and unresolved condition;
- malformed immediate-lambda header and malformed body;
- wrong-typed ordinary branch and unresolved ordinary branch;
- non-function callee and unresolved callee; and
- a direct lambda opposite a grouped direct lambda, and a direct lambda opposite
  a nested-call lambda.

Every selected-failure row proves exact ADR-0334 `none`, wrapper equality to that
same `none`, and no ADR-0333 inspection or fallback.

The classifier-false complete-Option matrix has exactly twenty shapes:

- immediate, one-group, two-group, three-group, four-group and six-group
  conditionals;
- exact-depth-five all-ordinary, grouped-only and nested-only branch shapes;
- direct lambdas at group depths zero through six; and
- an ordinary singleton, zero arguments, multiple arguments and a top-level
  non-call.

For every false row prove the whole wrapper result equals the complete ADR-0333
`Option`, not only equality of successful Core terms. The exact outcomes are
fourteen `some` and six `none`: five shallower conditionals, exact-five
all-ordinary, seven direct-lambda depths and ordinary singleton are `some`; the
six-group conditional, grouped-only, nested-only, zero, multiple and top-level
rows are `none`. Construct the complete ADR-0333 relation and retain its wrapper
and nested-child provenance wherever evidence exists. Expose the universal
false-branch equation for an arbitrary source.

Also preserve actual `none` for exactly thirteen inherited or boundary examples:
representative selected failures from ADR-0332, ADR-0330, ADR-0328, ADR-0326,
ADR-0324, ADR-0323, ADR-0322, ADR-0320 and ADR-0317, followed by tuple,
nested-call, returned-lambda and inferred-let-lambda boundaries. Do not claim
ADR-0334 accepts a neighboring shape or that ADR-0333 changes on any false source.

The exact runtime-selection list has fifteen sources: the three new successes,
five conditional controls at depths zero through four, and seven direct-lambda
controls at depths zero through six. Aggregate complete true/false dispatch with
nested provenance, exact runtime controls, and selected/inherited failures plus
universal complete ADR-0333 preservation into exactly three public roots.

## Independent parsed consumer

Create
`Solcore/Test/FrontendParsedLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda.lean`
strictly below 300 lines with exactly three authored public roots, including one
IO runner registered exactly once in `Tests.Main`. Require clean lexer/parser
diagnostics, EOF, full-file span and proof-producing structural equality to each
hand-built AST; never derive propositional equality from `BEq`.

Reuse the ADR-0334 primary true-route text:

```text
apply((((((flag ? lam(x){return x;} : ordinary))))))
```

Its exact half-open spans are call/full file `0..52`, callee/name `0..5`,
arguments `5..52`, group spans `6..51`, `7..50`, `8..49`, `9..48`, `10..47`,
conditional `11..46`, condition/name `11..15`, question `16..17`, lambda
`18..35`, colon `36..37`, and ordinary identifier/name `38..46`. Lambda keyword,
parameters, parameter/name, body, return statement and returned identifier/name
spans remain `18..21`, `21..24`, `22..23`, `24..35`, `25..34` and `32..33`.

Cover the other two true partitions with the exact ADR-0334 texts:

```text
apply((((((flag ? ordinary : lam(x){return x;}))))))
apply((((((flag ? lam(x){return x;} : lam(y){return y;}))))))
```

For all three sources prove the exact AST, complete ADR-0334 child, wrapper
relation, classifier and branch equation, literal checker/Core/type, Core typing,
and nested wrapper/child provenance. The primary Core is exactly
`apply (var 0) (ifE (var 3) (lambda Word Word (var 0)) (var 4))`.

Mirror all ten symbolic selected failures and the complete false and inherited
matrices. Use exactly thirty-three complete ADR-0333 preservation rows: the
twenty false shapes above plus the thirteen actual inherited or boundary
failures. Their exact outcomes are fourteen `some` and nineteen `none`. Every
false row proves literal whole-`Option` equality to ADR-0333; every true failure
proves the selected ADR-0334 `none` is final. Retain proof routes rather than only
runtime equality.

Freeze proof-producing exact ADR-0334 ASTs and spans for the four-group
predecessor, six-group conditional boundary and five-group direct-lambda control.
Their exact source texts and call/full spans are respectively
`apply(((((flag ? lam(x){return x;} : ordinary)))))` at `0..50`,
`apply(((((((flag ? lam(x){return x;} : ordinary)))))))` at `0..54`, and
`apply((((((lam(x){return x;}))))))` at `0..34`. Retain group spans
`6..49`/`7..48`/`8..47`/`9..46`,
`6..53`/`7..52`/`8..51`/`9..50`/`10..49`/`11..48`, and
`6..33`/`7..32`/`8..31`/`9..30`/`10..29`, with terminal conditional or lambda
spans `10..45`, `12..47` and `11..28`.

## Runtime contract

The wrapper returns the selected child Core verbatim and adds no runtime step.
Use the exact nonempty environment and store containing an opaque closure, cell
reference and host function. For each of the three ADR-0334 Cores and both Boolean
choices, independently retain `Core.Evaluates`, `runStateful_evaluation_sound`
and determinism. Fuel 13 is exactly `outOfFuel`; fuel 14 is exactly
`done (Word 7)` with the identical store.

Immediate through four-group conditional controls retain 13/14. Direct and
finite-group expected-lambda controls at depths zero through six retain 10/11.
Neither wrapper branch changes Core, environment, store, evaluation cost or result.

## Preserved and deferred boundaries

ADR-0317 through ADR-0334, every existing classifier, relation, checker and
theorem, ADR-0333's complete nested precedence, `RecursiveLocalComputation`, the
shared ADR-0324 branch checker, canonical source unions, runtime entries and
public wire versions remain textually and semantically unchanged. ADR-0335 adds
only reachability and fixed precedence.

ADR-0336 is the next smallest standalone semantic leaf: exactly six
whole-expression groups around the same immediate conditional. Do not add that
leaf or its later selecting wrapper here. Seven or more groups and any generic/
deeper grouped-conditional spine, grouped conditional branch lambdas, nested
conditional/call, tuple, return, inferred-let and typed-body expected propagation,
multiple arguments, global resolution, source-union integration, source closures,
runtime-world safety, costs and backend guarantees remain deferred. Parser and
diagnostic proof work remains paused.

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

1. decision: `docs/adr/0335-five-level-grouped-conditional-first-local-applications.md`;
2. production: `Solcore/Frontend/LocalApplicationWithFiveLevelGroupedConditionalExpectedLambda.lean`;
3. symbolic consumer: `Solcore/Test/FrontendLocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaProperties.lean`;
4. parsed consumer: `Solcore/Test/FrontendParsedLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda.lean`;
5. registration: `Solcore/Frontend.lean` and `Tests/Main.lean`;
6. documentation: `docs/CURRENT_STATUS.md`, `docs/FEATURE_MATRIX.md` and
   `docs/M2_PLAN.md`.

Keep the decision, production and both consumers strictly below 300 lines. Keep
every commit at no more than 300 changed lines. Stage only the exact paths for its
commit; do not create a seventh completion commit or include scratch/paused files.

Before closure verify exact ownership/generated names, safe/total flags, root and
all-owned axiom closure, masked forbidden-source and line-limit scans, both literal
branch equations, selected-failure finality, universal complete ADR-0333
preservation and exact 14/6 and 14/19 outcome partitions; direct/focused/umbrella/
aggregate builds, direct parsed runner and full tests; registration counts; exact
six-commit/nine-path range; preservation of ADR-0317 through ADR-0334 and all
paused files; source/olean drift, dependency closure, kernel and metadata. Do not
record a final ADR-0335 implementation commit hash in this decision.
