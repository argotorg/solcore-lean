# ADR-0333: Four-level-grouped-conditional-first local applications

## Status

Accepted; add one nonrecursive source-only wrapper that selects the complete
ADR-0332 result before the complete unchanged ADR-0331 result.

## Context

ADR-0332 is the standalone exact-singleton adapter for an immediate conditional
beneath exactly four transparent whole-expression groups when at least one
immediate branch is an ungrouped direct computation lambda. ADR-0331 is the
current complete local-application entry: its true branch is the exact ADR-0330
three-group conditional result, and its false branch is the complete unchanged
ADR-0329 result with all older conditional and finite direct-lambda-group
precedence.

Every ADR-0332 candidate is false for ADR-0331's ADR-0330 classifier because the
third group immediately contains a fourth group rather than a conditional.
ADR-0331 therefore returns the complete ADR-0329 `Option`; on all three new
ADR-0332 success partitions this is literally `none`. On classifier-selected
ADR-0332 semantic failure, the predecessor value is irrelevant and must not be
inspected. Dispatch after a failed checker would make precedence depend on
semantic success instead of the frozen source partition.

Editing ADR-0331, copying its nested dispatch, or introducing recursive group
traversal would reopen frozen behavior. The smallest additive integration is a
two-child wrapper around the complete ADR-0332 and ADR-0331 results. It adds no
new expression, type, Core or runtime semantics.

The reviewed baseline is HEAD
`a6b3e28065bdd53a08bd96e6625236dae8b94c79`. Frozen ADR-0331 decision and
production SHA-256 values are
`e139303451fe91a9c2bb9e3f1e257b42da607e8d306740733321fd51ab418c26` and
`7720fc27b26f31632a47d65ec626db990c4e78325cecb1032d5fd8fd70ef23d2`.
Frozen ADR-0332 decision and production SHA-256 values are
`43e0e40902efbc0c38cba3db7922cf1a16f8be7666d00cbb36605f65428538c4` and
`68896b1246d2bfbe60c3d93abfc61d7f0fbaa224a2a3e55b4c29b872d5a76382`.
Its final independent semantic audit is GREEN with zero issues at SHA-256
`9168011f28cd3e068e67b5e0415847add5c9a3520327193dbb6fce9dd152027b`.

## Decision

Add `LocalApplicationWithFourLevelGroupedConditionalExpectedLambda` as a
separate additive wrapper. Evaluate the unchanged
`isFourLevelGroupedConditionalExpectedLambdaArgumentApplication` classifier
once on the unchanged original `Syntax.Expr`:

```text
if ADR0332-classifier(source)
then exact ADR0332 Option(source)
else exact ADR0331 Option(source)
```

The true branch returns
`elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?`
literally. The false branch returns
`elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?`
literally. Classification stays source-only: it does not read owner, tables,
resolution, inferred types, diagnostics, checker results or runtime observations.

A classifier-true `none` is final. Do not invoke ADR-0331 after selected failure,
use `Option.orElse`, retry until a checker succeeds, remove or add groups, rebuild
or normalize the source, rewrite spans, or change either child. Conversely, every
classifier-false input preserves the complete ADR-0331 `Option`, both `some` and
`none`, including ADR-0331's ADR-0330-before-ADR-0329 precedence.

Add no classifier, combined classifier, path enum, group extractor, recursion,
fuel, termination argument, source reconstruction, source union, runtime node,
generic failure theorem or change to ADR-0331/ADR-0332.

## Declarative and executable interface

Define `LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates`
with exactly two constructors:

1. `fourLevelGroupedConditional` retains
   `isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = true`
   and a complete
   `FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates`
   child;
2. `existing` retains the same classifier equal to `false` and a complete
   `LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates`
   child.

Expose exactly these eight authored public roots:

1. `LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates`;
2. `elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?`;
3. `elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_fourLevelGroupedConditional`;
4. `elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing`;
5. `elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff`;
6. `elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_eq_none_iff`;
7. `LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates.core_hasType`;
8. `LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates.provenance`.

Both branch theorems are universal literal complete-`Option` equations. The
success theorem is exact executable/declarative correspondence, and the failure
theorem equates checker `none` with absence of every Core/type relation witness.
Typing delegates directly to the selected complete child. Provenance is the exact
disjunction of the classifier equation plus complete ADR-0332 child provenance,
or the false equation plus complete ADR-0331 wrapper and nested-child provenance.
Do not add a wrapper classifier or `classified` theorem; the unchanged ADR-0332
Boolean and its negation are already the complete partition.

## Independent symbolic consumer

Create
`Solcore/Test/FrontendLocalApplicationWithFourLevelGroupedConditionalExpectedLambdaProperties.lean`
strictly below 300 lines with exactly three authored public roots. Keep every
fixture and helper private. Reuse the established sparse table: first-match
`apply` is Core variable 0 with `(Word -> Word) -> Word`, a later duplicate has
`Unit`, foreign-owner `flag` is variable 3 with `Bool`, `ordinary` is variable 4
with `Word -> Word`, and unrelated foreign opaque and wrong rows remain present.

The true route covers all three ADR-0332 exact-depth-four branch partitions:
lambda/ordinary, ordinary/lambda and lambda/lambda. For each, independently
construct the complete ADR-0332 relation before the wrapper relation. Freeze the
classifier equation, exact true-branch equation, literal complete checker
result/Core/type, Core typing, and both wrapper and complete four-group child
provenance. Also freeze that current ADR-0331 returns exactly `none` for all three.

Use exactly these ten classifier-true selected-failure categories:

- non-Bool condition and unresolved condition;
- malformed immediate-lambda header and malformed body;
- wrong-typed ordinary branch and unresolved ordinary branch;
- non-function callee and unresolved callee; and
- a direct lambda opposite a grouped direct lambda, and a direct lambda opposite
  a nested-call lambda.

Every selected-failure row proves exact ADR-0332 `none`, wrapper equality to that
same `none`, and no ADR-0331 inspection or fallback.

The classifier-false complete-Option matrix has exactly eighteen shapes:

- immediate, one-group, two-group, three-group and five-group conditionals;
- exact-depth-four all-ordinary, grouped-only and nested-only branch shapes;
- direct lambdas at group depths zero through five; and
- an ordinary singleton, zero arguments, multiple arguments and a top-level
  non-call.

For every false row prove the whole wrapper result equals the complete ADR-0331
`Option`, not only equality of successful Core terms. Construct the complete
ADR-0331 relation and retain its wrapper/child provenance wherever evidence
exists. Expose the universal false-branch equation for an arbitrary source.

Also preserve actual `none` for exactly twelve inherited or boundary examples:
representative selected failures from ADR-0330, ADR-0328, ADR-0326, ADR-0324,
ADR-0323, ADR-0322, ADR-0320 and ADR-0317, followed by tuple, nested-call,
returned-lambda and inferred-let-lambda boundaries. Do not claim ADR-0332 accepts
a neighboring shape or that ADR-0331 changes on any false source.

The exact runtime-selection list has thirteen sources: the three new successes,
four conditional controls at depths zero through three, and six direct-lambda
controls at depths zero through five. Aggregate complete true/false dispatch with
nested provenance, exact runtime controls, and selected/inherited failures plus
universal complete ADR-0331 preservation into exactly three public roots.

## Independent parsed consumer

Create
`Solcore/Test/FrontendParsedLocalApplicationWithFourLevelGroupedConditionalExpectedLambda.lean`
strictly below 300 lines with exactly three authored public roots, including one
IO runner registered exactly once in `Tests.Main`. Require clean lexer/parser
diagnostics, EOF, full-file span and proof-producing structural equality to each
hand-built AST; never derive propositional equality from `BEq`.

Freeze the primary true-route text:

```text
apply(((((flag ? lam(x){return x;} : ordinary)))))
```

Its exact half-open spans are call/full file `0..50`, callee/name `0..5`,
arguments `5..50`, group spans `6..49`, `7..48`, `8..47`, `9..46`, conditional
`10..45`, condition/name `10..14`, question `15..16`, lambda `17..34`, colon
`35..36`, and ordinary identifier/name `37..45`. Lambda keyword, parameters,
parameter/name, body, return statement and returned identifier/name spans are
`17..20`, `20..23`, `21..22`, `23..34`, `24..33` and `31..32`.

Cover the other two true partitions with:

```text
apply(((((flag ? ordinary : lam(x){return x;})))))
apply(((((flag ? lam(x){return x;} : lam(y){return y;})))))
```

For all three sources prove the exact AST, complete ADR-0332 child, wrapper
relation, classifier and branch equation, literal checker/Core/type, Core typing,
and nested wrapper/child provenance. The primary Core is exactly
`apply (var 0) (ifE (var 3) (lambda Word Word (var 0)) (var 4))`.

Mirror all ten symbolic selected failures and the complete false and inherited
matrices with parsed source. Use exactly thirty complete ADR-0331 preservation
rows: the eighteen false shapes above plus the twelve actual inherited or boundary
failures. Every false row proves literal whole-`Option` equality to ADR-0331;
every true failure proves the selected ADR-0332 `none` is final.

Freeze proof-producing exact ASTs and spans for the three-group predecessor,
five-group conditional boundary and four-group direct-lambda control. The
three-group text `apply((((flag ? lam(x){return x;} : ordinary))))` has call/full
span `0..48`, arguments `5..48`, groups `6..47`, `7..46`, `8..45`, and
conditional `9..44`. The five-group text
`apply((((((flag ? lam(x){return x;} : ordinary))))))` has call/full `0..52`,
arguments `5..52`, groups `6..51`, `7..50`, `8..49`, `9..48`, `10..47`, and
conditional `11..46`. The four-group direct-lambda source
`apply(((((lam(x){return x;})))))` has call/full `0..32`, arguments `5..32`,
groups `6..31`, `7..30`, `8..29`, `9..28`, and lambda `10..27`.

## Runtime contract

The wrapper returns the selected child Core verbatim and adds no runtime step.
Use the exact nonempty environment and store containing an opaque closure, cell
reference and host function. For each of the three ADR-0332 Cores and both Boolean
choices, independently retain `Core.Evaluates`, `runStateful_evaluation_sound`
and determinism. Fuel 13 is exactly `outOfFuel`; fuel 14 is exactly
`done (Word 7)` with the identical store.

Immediate, one-group, two-group and three-group conditional controls retain
13/14. Direct and finite-group expected-lambda controls at depths zero through
five retain 10/11. Neither wrapper branch changes Core, environment, store,
evaluation cost or result.

## Preserved and deferred boundaries

ADR-0317 through ADR-0332, every existing classifier, relation, checker and theorem,
ADR-0331's complete nested precedence, `RecursiveLocalComputation`, the shared
ADR-0324 branch checker, canonical source unions, runtime entries and public wire
versions remain textually and semantically unchanged. ADR-0333 adds only
reachability and fixed precedence.

ADR-0334 is the next smallest standalone semantic leaf: exactly five
whole-expression groups around the same immediate conditional. Do not add that
leaf or its later selecting wrapper here. Six or more groups and any generic/deeper
grouped-conditional spine, grouped conditional branch lambdas, nested conditional/
call, tuple, return, inferred-let and typed-body expected propagation, multiple
arguments, global resolution, source-union integration, source closures,
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

1. decision: `docs/adr/0333-four-level-grouped-conditional-first-local-applications.md`;
2. production: `Solcore/Frontend/LocalApplicationWithFourLevelGroupedConditionalExpectedLambda.lean`;
3. symbolic consumer: `Solcore/Test/FrontendLocalApplicationWithFourLevelGroupedConditionalExpectedLambdaProperties.lean`;
4. parsed consumer: `Solcore/Test/FrontendParsedLocalApplicationWithFourLevelGroupedConditionalExpectedLambda.lean`;
5. registration: `Solcore/Frontend.lean` and `Tests/Main.lean`;
6. documentation: `docs/CURRENT_STATUS.md`, `docs/FEATURE_MATRIX.md` and
   `docs/M2_PLAN.md`.

Keep the decision, production and both consumers strictly below 300 lines. Keep
every commit at no more than 300 changed lines. Stage only the exact paths for its
commit; do not create a seventh completion commit or include scratch/paused files.

Before closure verify exact ownership/generated names, safe/total flags, root and
all-owned axiom closure, masked forbidden-source and line-limit scans, both literal
branch equations, selected-failure finality, and universal complete ADR-0331
preservation; direct/focused/umbrella/aggregate builds, direct parsed runner and
full tests; registration counts; exact six-commit/nine-path range; preservation of
ADR-0317 through ADR-0332 and all paused files; source/olean drift and dependency
closure. Do not record a final ADR-0333 implementation commit hash in this decision.
