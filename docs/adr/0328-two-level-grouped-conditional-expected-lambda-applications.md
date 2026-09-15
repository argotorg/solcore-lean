# ADR-0328: Two-level grouped conditional expected-lambda applications

## Status

Accepted; add one standalone exact-singleton adapter
for an immediate conditional beneath exactly two transparent whole-expression
source groups.

## Context

ADR-0324 checks an immediate conditional argument at the inferred callee parameter
type when at least one branch is an immediate, ungrouped direct computation lambda.
ADR-0326 lifts that same branch contract through exactly one group around the whole
conditional. ADR-0327 makes ADR-0326 reachable before the complete unchanged
ADR-0325 local-application result.

The next unhandled source is two groups around that same conditional. The current
ADR-0327 wrapper sees its one-level classifier as false and therefore returns the
complete ADR-0325 `Option` literally. Both ADR-0325 classifiers are also false:
its immediate-conditional classifier sees a group, and its finite direct-lambda
group-spine classifier reaches a conditional rather than a direct lambda. Thus the
complete current route continues through ADR-0325 to the exact ADR-0322 result.

Changing grouped branch semantics is not this unit. A conditional with one direct
lambda and an opposite grouped lambda is already selected by ADR-0324 at depth zero;
reclassifying that branch would reopen a frozen recognized-failure boundary.
Generalizing to arbitrary group depth would introduce recursive traversal before
exact depth two has been independently frozen.

## Decision and exact source partition

Add `TwoLevelGroupedConditionalExpectedLambdaArgumentApplication` as a standalone
adapter. Its classifier is true exactly for:

```text
call callee [group (group
  (conditional condition ? thenBranch : elseBranch))]
```

The call has exactly one argument. That argument has exactly two outer groups, the
inner group's immediate child is a conditional, and at least one immediate branch
is an ungrouped direct computation lambda according to the unchanged
`isImmediateExpectedComputationLambda` classifier. Classification is syntax-only;
it ignores spans, owner, tables, name resolution, inferred types, header and body
validity, diagnostics, checker results and runtime observations.

The new true partition is structurally disjoint from the three relevant frozen
classifiers:

- ADR-0326 sees an outer group whose immediate child is a second group, not a
  conditional;
- ADR-0324 sees a group rather than an immediate conditional argument; and
- ADR-0323 cannot produce a direct-lambda group spine because the terminal after
  the two groups is a conditional.

Depths one and three are false. Branch-only grouping is false. At depth two, an
all-ordinary conditional and a conditional whose lambda-bearing branches are only
grouped or nested are false. A direct branch opposite a grouped or nested branch
is true because the direct branch establishes the boundary; the unchanged branch
checker treats the opposite branch as ordinary, and any failure remains selected.

This ADR does not modify ADR-0327. A later wrapper will dispatch on the ADR-0328
classifier, returning the complete ADR-0328 `Option` when true and the complete
ADR-0327 `Option` when false. A selected true-branch `none` will be final; dispatch
must not depend on semantic success.

## Static semantics

Inspect the unchanged original call/group/group/conditional source. Infer the
original callee with `elaborateRecursiveLocalComputation?` and require its exact
type to be `.function parameterType resultType`. Infer the original condition and
require its type to be exactly `.bool`. Check both original branch nodes at the
literal `parameterType` using the unchanged ADR-0324
`elaborateConditionalExpectedLambdaBranch?` contract:

- an immediate ungrouped direct lambda uses existing expected-lambda checking; and
- every other immediate branch uses unchanged recursive inference followed by
  exact type equality.

Return exactly:

```text
(.apply functionCore (.ifE conditionCore thenCore elseCore), resultType)
```

The two groups are transparent only in this Core result. Both group spans remain
available in declarative provenance. Pass the original callee, condition and
branch nodes directly to the existing child checkers. Do not unwrap into a rebuilt
AST, normalize or rewrite spans, invoke ADR-0324 on a replacement source, add
recursion or fuel, use `Option.orElse`, or try another checker after any recognized
semantic failure. The standalone checker returns its selected result directly.

## Declarative and executable interface

Define
`TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates` with one
`application` constructor. Retain the call and argument-list spans, outer and inner
group spans, conditional/question/colon spans, original callee, condition and both
branches, literal parameter and result types, and complete callee, Bool-condition
and two unchanged ADR-0324 branch derivations.

Expose exactly these eight authored roots:

1. `isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication`;
2. `TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates`;
3. `elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?`;
4. `elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff`;
5. `elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?_eq_none_iff`;
6. `TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.core_hasType`;
7. `TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.classified`;
8. `TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.provenance`.

The success iff theorem relates the literal complete checker result to the one
constructor. The none iff theorem states exact absence of all result evidence.
`core_hasType` composes only retained child typing. `classified` fixes the source
boundary. `provenance` exposes both group spans, every other original span and
child, the branch-boundary equation, complete child derivations and literal Core
equation.

Add no generic group extractor, recursive source checker, termination argument,
new branch relation or checker, combined path enum, source union, wrapper, generic
failure theorem, public helper theorem or redundant generated public surface.

## Independent symbolic consumer

Create a consumer strictly below 300 lines with exactly three authored public
roots. Use the established sparse local table: first-match `apply` at Core variable
0 has `(Word -> Word) -> Word`; a later duplicate `apply` has `Unit`; foreign-owner
`flag` at variable 3 has `Bool`; `ordinary` at variable 4 has `Word -> Word`; and
unrelated foreign opaque and wrong rows remain present.

Cover all three successes beneath exactly two whole-expression groups:

- direct lambda / ordinary;
- ordinary / direct lambda;
- direct lambda / direct lambda.

For each source, prove the new classifier true and the ADR-0326, ADR-0324 and
ADR-0323 classifiers false. Independently construct the complete callee,
condition, both ADR-0324 branch children and then the complete ADR-0328 relation
before using checker correspondence. Freeze the literal checker result, Core and
inferred result type, Core typing, classification, and complete two-group
provenance. Also prove that the untouched current ADR-0327 result is literally the
complete ADR-0325 result on each new source.

The selected failure matrix contains:

- non-Bool and unresolved conditions;
- malformed immediate-lambda header and malformed body;
- wrong-typed and unresolved ordinary branches;
- non-function and unresolved callees; and
- a direct lambda opposite a grouped direct lambda, and a direct lambda opposite
  a nested-call lambda.

For every failure, prove the ADR-0328 classifier remains true and the complete
ADR-0328 checker result is `none`; no predecessor result may rescue it.

Freeze neighboring complete results for: the same conditional at depths one and
three; depth-two all-ordinary, grouped-only and nested-only branch shapes; the
immediate conditional; direct-lambda applications at group depths zero through
three; the ordinary singleton; zero and multiple arguments; and top-level non-call
forms. Record the complete unchanged ADR-0327 `Option` for every neighbor. Whenever
the ADR-0327 one-level classifier is false, additionally prove its false equation
to the literal complete ADR-0325 `Option`; preserve the one-level conditional via
its true ADR-0327 route rather than incorrectly equating it with ADR-0325.

Use the literal established environment and nonempty store containing the opaque
closure, cell reference and host function. For each of the three new Cores and
both Boolean choices, independently prove evaluation to `Word 7` with the store
unchanged. Freeze all six runner boundaries: fuel 13 is `outOfFuel`, and fuel 14 is
exactly `done (Word 7)` with the identical initial store. Immediate and one-group
conditional controls remain 13/14; direct and finite-group lambda controls remain
10/11.

## Independent parsed consumer

Create a second consumer strictly below 300 lines with exactly three authored
public roots, including one IO runner registered exactly once in `Tests.Main`.
Require clean lexer and parser diagnostics, EOF, full-file span and
proof-producing equality to each complete hand-built AST; do not derive equality
from `BEq`.

Freeze the primary source:

```text
apply(((flag ? lam(x){return x;} : ordinary)))
```

Its exact half-open spans are:

| Node | Span |
| --- | --- |
| call / callee / arguments | `0..46` / `0..5` / `5..46` |
| outer group / inner group | `6..45` / `7..44` |
| conditional / condition | `8..43` / `8..12` |
| question / then lambda / colon / ordinary | `13..14` / `15..32` / `33..34` / `35..43` |
| lambda keyword / parameters / parameter | `15..18` / `18..21` / `19..20` |
| lambda body / return statement / returned identifier | `21..32` / `22..31` / `29..30` |

Identifier-name spans equal their containing identifier spans. Freeze the other
two success texts compactly:

```text
apply(((flag ? ordinary : lam(x){return x;})))
apply(((flag ? lam(x){return x;} : lam(y){return y;})))
```

For all three parsed sources, prove the same source partition and independently
constructed child relation, complete ADR-0328 relation, literal checker/Core/type,
typing, classification and provenance as the symbolic matrix. The primary literal
Core is `apply (var 0) (ifE (var 3) (lambda Word Word (var 0)) (var 4))`.

Cover the selected failure matrix with parsed sources and freeze parsed neighbors
for one- and three-group conditionals, depth-two false shapes, immediate
conditionals, direct-lambda group depths, ordinary/zero/multiple-argument calls and
top-level non-calls. For each applicable false route, compare the entire current
ADR-0327 `Option`, and then its exact ADR-0325 false-route `Option`, rather than only
comparing successful Core terms.

Run all three successful parsed Cores for both Boolean choices with the same exact
nonempty environment and store. Require fuel 13 to exhaust and fuel 14 to return
`Word 7` with the identical store. Keep the diagnostic checks local to this
consumer; general parser and diagnostic proof development remains paused.

## Preserved and deferred boundaries

ADR-0317 through ADR-0327 production, decisions and public semantics remain
textually and semantically unchanged. Preserve every existing classifier, checker,
relation and theorem; `RecursiveLocalComputation`; the shared ADR-0324 branch
contract; canonical source unions; runtime entries; public wire versions; and the
eight paused untracked parser/diagnostic proof files. This unit adds only an opt-in
static adapter and no new runtime expression semantics.

Defer the wrapper that selects ADR-0328 before the complete ADR-0327 result. Also
defer three or more whole groups around a conditional; grouped conditional branch
lambdas; nested conditional/call, tuple, return, inferred-let and typed-body
expected propagation; multiple arguments and global resolution; canonical
source-union integration; runtime-world safety, costs and backend guarantees; and
parser and diagnostic proofs.

## Prototype freeze and delivery contract

The production-shaped prototype is fixed at 225 lines with SHA-256
`836b8bdb62f87a3ef6869b709548e06402256f07689466d24785c56c0f7bb08e`.
Its canonical Lake build artifact SHA-256 is
`8e82e20c0cf233f1dbdac637d206c22f2af91c3e783415572dad046df76b1023`.
The prototype has exactly eight authored roots, 37 owned declarations, 31 public
and six private. All are safe and total, with no generated partial helper, public
simp leak, public proof leak or axiom outside `propext`, `Classical.choice` and
`Quot.sound`. Port theorem bodies unchanged, allowing only the production module
comment/path context, and re-audit production ownership independently.

Deliver exactly six commits over exactly these nine unique tracked paths:

1. decision: `docs/adr/0328-two-level-grouped-conditional-expected-lambda-applications.md`;
2. production: `Solcore/Frontend/TwoLevelGroupedConditionalExpectedLambdaArgumentApplication.lean`;
3. symbolic consumer: `Solcore/Test/FrontendTwoLevelGroupedConditionalExpectedLambdaArgumentApplicationProperties.lean`;
4. parsed consumer: `Solcore/Test/FrontendParsedTwoLevelGroupedConditionalExpectedLambdaArgumentApplication.lean`;
5. registration: `Solcore/Frontend.lean` and `Tests/Main.lean`;
6. documentation: `docs/CURRENT_STATUS.md`, `docs/FEATURE_MATRIX.md` and
   `docs/M2_PLAN.md`.

Keep every commit at no more than 300 changed lines. Keep production and both
consumers strictly below 300 lines. Stage only the exact paths for each commit and
do not include scratch evidence or the eight paused files.

Before closure, verify exact ownership and generated names; safe/total flags;
public-root and all-owned axiom closure; masked forbidden-source and line-limit
scans; exact source partitions, successes, selected failures and complete
ADR-0327/ADR-0325 preservation; direct, focused, umbrella and aggregate builds;
the direct parsed runner and full test suite; registration counts; exact six-commit
nine-path range; preservation of ADR-0317 through ADR-0327 and the paused files;
and source/olean drift plus dependency closure. Do not record a final implementation
commit hash in the production decision.
