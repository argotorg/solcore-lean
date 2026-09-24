# ADR-0329: Two-level-grouped-conditional-first local applications

## Status

Accepted; add one nonrecursive source-only wrapper that selects the complete
ADR-0328 result before the complete unchanged ADR-0327 result.

## Context

ADR-0328 is a standalone exact-singleton adapter for an immediate conditional
beneath exactly two transparent whole-expression groups when at least one
immediate branch is an ungrouped direct computation lambda. ADR-0327 is the
current complete local-application entry: its true branch is the exact ADR-0326
one-group conditional result, and its false branch is the complete ADR-0325
result with all older conditional and finite direct-lambda-group precedence.

Every ADR-0328 candidate is false for the ADR-0327 classifier because its outer
group immediately contains another group rather than a conditional. The exact
ADR-0327 result therefore remains its complete ADR-0325 result. On the three new
success shapes that result is `none`; on a selected ADR-0328 semantic failure its
value is deliberately irrelevant and must not be inspected. Dispatching after a
checker failure would make precedence depend on semantic success.

Editing ADR-0327, repeating its internal dispatch, or generalizing group traversal
would reopen frozen predecessors. The smallest additive reachability unit is a
two-child wrapper around the complete ADR-0328 and ADR-0327 results. It introduces
no new expression, type or runtime semantics.

The reviewed baseline is HEAD
`5231e47e49dab3ef025206682ae1c6fefcc01212`. The accepted ADR-0328 decision has
SHA-256 `77f688d38b60bbcbd8d63017c55579f43c8a2564eeaedba5e49ca0cb3ad12cf8`,
and the production ADR-0328 source has SHA-256
`3bf4aece7e3b01abfe9bd1b816f54476022c92233a292ca66862bbb753880674`.

## Decision

Add `LocalApplicationWithTwoLevelGroupedConditionalExpectedLambda` as a separate
additive wrapper. Evaluate the unchanged
`isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication` classifier once
on the unchanged original `Syntax.Expr`:

```text
if ADR0328-classifier(source)
then exact ADR0328 Option(source)
else exact ADR0327 Option(source)
```

The true branch returns
`elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?` literally.
The false branch returns
`elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?` literally.
Classification is source-only and does not read owner, tables, resolution, inferred
types, diagnostics, checker results or runtime observations.

A classifier-true `none` is final. Do not call ADR-0327 after a selected failure,
use `Option.orElse`, try checkers until one succeeds, rebuild or normalize the
source, erase either group before dispatch, or change any child. Conversely, every
classifier-false source preserves the complete ADR-0327 `Option`, both `some` and
`none`, including ADR-0327's nested one-group-first and ADR-0325 predecessor order.

Add no new classifier, combined classifier, path enumeration, generic group
extractor, recursion, fuel, termination argument, source rewrite, source union,
runtime node, generic failure theorem or modification to ADR-0327/ADR-0328.

## Declarative and executable interface

Define `LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates`
with exactly two constructors:

1. `twoLevelGroupedConditional` retains
   `isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = true`
   and a complete
   `TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates` child;
2. `existing` retains the same classifier equal to `false` and a complete
   `LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates` child.

Expose exactly these eight authored roots:

1. `LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates`;
2. `elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?`;
3. `elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_twoLevelGroupedConditional`;
4. `elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing`;
5. `elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_iff`;
6. `elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_eq_none_iff`;
7. `LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates.core_hasType`;
8. `LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates.provenance`.

The two branch theorems are universal literal complete-`Option` equations. The
success theorem is exact executable/declarative correspondence. The failure
theorem equates checker `none` with absence of every Core/type relation witness.
Typing delegates directly to the selected complete child. Provenance is the exact
disjunction of classifier equation plus complete ADR-0328 or ADR-0327 child.

Do not add a wrapper classifier or `classified` theorem: the unchanged ADR-0328
Boolean and its negation already are the complete partition.

## Independent symbolic consumer

Create
`Solcore/Test/FrontendLocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaProperties.lean`
strictly below 300 lines with exactly three authored public roots. All fixtures
and helpers remain private. Reuse the established sparse table: first-match
`apply` is Core variable 0 with `(Word -> Word) -> Word`; a later duplicate has
`Unit`; foreign-owner `flag` is variable 3 with `Bool`; `ordinary` is variable 4
with `Word -> Word`; and unrelated foreign opaque and wrong rows remain present.

The true route covers all three ADR-0328 branch partitions beneath exactly two
whole groups: lambda/ordinary, ordinary/lambda and lambda/lambda. For each,
independently construct the complete ADR-0328 child before the wrapper relation.
Freeze the classifier equation, exact true branch equation, literal complete
checker result/Core/type, Core typing and both wrapper and child provenance.

The false route preserves the complete ADR-0327 partition. Cover at least:

- a one-group conditional through ADR-0327's true child;
- an immediate conditional through ADR-0327's ADR-0325 child;
- three-or-more-, exact-two-, one- and zero-group direct lambdas;
- an all-ordinary depth-two grouped conditional; and
- an ordinary singleton application.

For every false fixture prove the entire wrapper `Option` equals the complete
ADR-0327 `Option`, not merely equality of successful Core terms. Where evidence
exists, construct the complete selected ADR-0327 relation independently and retain
it in wrapper provenance. Also expose the universal false-branch theorem for an
arbitrary source.

The classifier-true selected-failure table has exactly these ten categories:

- non-Bool condition and unresolved condition;
- malformed direct-lambda header and malformed body;
- wrong-typed ordinary branch and unresolved ordinary branch;
- non-function callee and unresolved callee; and
- direct lambda opposite a grouped direct lambda, and direct lambda opposite a
  nested-call lambda.

Every row proves classifier true, exact ADR-0328 result `none`, wrapper result
equal to that same `none`, and no ADR-0327 fallback. Inherited failures from the
one-group ADR-0326 path and representative ADR-0324, ADR-0323, ADR-0322, ADR-0320
and ADR-0317 paths are classifier-false and retain the complete ADR-0327 failure.

The false-boundary matrix also freezes a three-group conditional; depth-two
all-ordinary, grouped-only and nested-only branch shapes; zero/multiple arguments;
top-level non-calls; tuples; nested calls; returned and inferred-let lambdas. Add
no claim that ADR-0328 itself accepts any of these shapes.

Use exactly three public roots to aggregate: both complete dispatch routes and
provenance; exact runtime controls; and selected/inherited failures plus literal
ADR-0327 preservation.

## Independent parsed consumer

Create
`Solcore/Test/FrontendParsedLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda.lean`
strictly below 300 lines with exactly three authored public roots, including one
IO runner registered once in `Tests.Main`. Require clean lexer/parser diagnostics,
EOF, full-file span and proof-producing structural equality to each hand-built
AST; do not derive propositional equality from `BEq`.

Freeze the primary true-route text:

```text
apply(((flag ? lam(x){return x;} : ordinary)))
```

Its exact half-open spans are call/full file `0..46`, callee/name `0..5`, arguments
`5..46`, outer group `6..45`, inner group `7..44`, conditional `8..43`, condition/
name `8..12`, question `13..14`, then lambda `15..32`, colon `33..34`, and ordinary
identifier/name `35..43`. The lambda keyword, parameters, parameter/name, body,
return statement and returned identifier/name spans are `15..18`, `18..21`,
`19..20`, `21..32`, `22..31` and `29..30`.

The literal Core is `apply (var 0) (ifE (var 3)
(lambda Word Word (var 0)) (var 4))`. Cover the two other true partitions with:

```text
apply(((flag ? ordinary : lam(x){return x;})))
apply(((flag ? lam(x){return x;} : lam(y){return y;})))
```

For all three sources prove the exact AST, complete ADR-0328 child, wrapper
relation, classifier/branch equation, literal checker/Core/type, typing and nested
provenance. The wrapper must return exactly the child's `Option`.

Freeze exact false-route ASTs and spans for these predecessor representatives:

- `apply((flag ? lam(x){return x;} : ordinary))`: call `0..44`, arguments
  `5..44`, group `6..43`, conditional `7..42`;
- `apply(flag ? lam(x){return x;} : ordinary)`: call `0..42`, arguments
  `5..42`, conditional `6..41`;
- `apply(((lam(x){return x;})))`: call `0..28`, arguments `5..28`, groups
  `6..27` and `7..26`, lambda `8..25`; and
- `apply((((lam(x){return x;}))))`: call `0..30`, arguments `5..30`, groups
  `6..29`, `7..28`, `8..27`, lambda `9..26`.

Mirror the symbolic true-failure, inherited-failure and false-boundary matrices
with parsed sources. On every false row assert literal wrapper-versus-ADR-0327
complete `Option` equality, including both successful and rejected controls.

## Runtime contract

The wrapper returns an existing child Core verbatim and adds no runtime step. Use
the exact nonempty environment and store containing an opaque closure, cell
reference and host function. For each of the three two-group Cores and both
Boolean choices, independently retain `Core.Evaluates`, small-step soundness and
determinism. Fuel 13 is exactly `outOfFuel`; fuel 14 is exactly
`done (Word 7)` with the identical store.

The immediate and one-group conditional controls retain 13/14. Direct and finite
group expected-lambda controls retain 10/11. Neither wrapper branch changes Core,
environment, store, evaluation cost or result.

## Preserved and deferred boundaries

ADR-0317 through ADR-0328, every existing classifier, relation, checker and theorem,
ADR-0327's complete nested precedence, `RecursiveLocalComputation`, the ADR-0324
branch checker, canonical source unions, runtime entries, and Core Wire
remain textually and semantically unchanged. This unit adds reachability and fixed
precedence only.

The next smallest standalone semantic leaf is exactly three whole groups around
the same immediate conditional. A finite three-or-more grouped-conditional spine
remains later until exact depth three is frozen independently. Grouped conditional
branch lambdas remain deferred because admitting them would reopen the established
ADR-0324/0326/0328 selected-failure boundary. Also defer nested conditional/call,
tuple, return, inferred-let and typed-body expected propagation; multiple arguments
and global resolution; canonical source-union integration; source closures;
runtime-world safety, costs and backend guarantees. Parser and diagnostic proof
development remains paused.

Preserve exactly the existing eight untracked pause files under `Solcore/Syntax`
and `Solcore/Syntax/Parser`; do not stage, edit or remove them.

## Prototype freeze and delivery contract

The production-shaped prototype
`.lake/trace-audits/ADR0329LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaPrototypeIndependent.lean`
is fixed at 151 lines and 8,349 bytes with SHA-256
`4367b3582e81e743eceb6b80b2044bc05532e2805d2240d93a7c71e878749b5d`.
Its direct and trust-zero compiled artifact SHA-256 is
`e42505e87b3530b44c21e36e12941ae1238466eb863c9bf497d288912c1c3617`.
Port the source without theorem-body changes, allowing only the production module
comment/path context.

The prototype has exactly eight authored roots and 15 owned declarations, all
public. Every declaration is safe and total; there is no public simp/proof leak and
no axiom outside `propext`, `Classical.choice` and `Quot.sound`. The independent
prototype audit is GREEN with zero issues.

Deliver exactly six commits over exactly these nine unique tracked paths:

1. decision: `docs/adr/0329-two-level-grouped-conditional-first-local-applications.md`;
2. production: `Solcore/Frontend/LocalApplicationWithTwoLevelGroupedConditionalExpectedLambda.lean`;
3. symbolic consumer: `Solcore/Test/FrontendLocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaProperties.lean`;
4. parsed consumer: `Solcore/Test/FrontendParsedLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda.lean`;
5. registration: `Solcore/Frontend.lean` and `Tests/Main.lean`;
6. documentation: `docs/CURRENT_STATUS.md`, `docs/FEATURE_MATRIX.md` and
   `docs/M2_PLAN.md`.

Keep the decision, production and both consumers strictly below 300 lines. Keep
every commit at no more than 300 changed lines. Stage only the exact paths for each
commit; do not add a seventh completion commit or include scratch/paused files.

Before closure verify exact ownership/generated names, safe/total flags, root and
all-owned axiom closure, masked forbidden-source and line-limit scans, exact branch
equations, selected-failure finality and universal complete ADR-0327 preservation;
direct/focused/umbrella/aggregate builds, direct parsed runner and full tests;
registration counts; exact six-commit/nine-path range; preservation of ADR-0317
through ADR-0328 and paused files; and source/olean drift plus dependency closure.
Do not record a final ADR-0329 implementation commit hash in this decision.
