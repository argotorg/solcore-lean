# ADR-0327: One-level-grouped-conditional-first local applications

## Status

Accepted; add one nonrecursive source-only wrapper that selects the complete
ADR-0326 result before the complete unchanged ADR-0325 result.

## Context

ADR-0326 is a standalone exact-singleton adapter for one transparent source group
around an immediate conditional with at least one immediate, ungrouped direct
computation-lambda branch. ADR-0325 remains the frozen unified entry for immediate
conditional arguments, finite direct-lambda group spines, shallow direct lambdas
and ordinary singleton applications.

Every ADR-0326 candidate currently reaches ADR-0325's exact ADR-0322 path because
it is structurally false for both ADR-0325 classifiers. Calling the new checker
only after ADR-0325 fails would make dispatch depend on semantic success. Editing
ADR-0325 or ADR-0326 would reopen a frozen predecessor. A single ordered wrapper
is therefore the smallest additive reachability step.

## Decision

Add `LocalApplicationWithOneLevelGroupedConditionalExpectedLambda` as a separate
entry. Dispatch once on the unchanged original `Syntax.Expr`:

| Source equation | Selected complete result |
| --- | --- |
| `isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source = true` | `elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication? ... source` |
| classifier `= false` | `elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? ... source` |

Return the selected `Option` literally. A recognized ADR-0326 failure is final;
do not use `Option.orElse`, try checkers until one succeeds, call ADR-0325 after a
selected semantic failure, rebuild or normalize the source, unwrap the group, or
change any child checker. The false equation preserves every ADR-0325 success and
failure, including its internal conditional-first then finite-group precedence.

Do not add a combined classifier or path enumeration. The unchanged ADR-0326
Boolean and its negation already form the exact source partition. Classification
reads no owner, table, name resolution, inferred type, diagnostics, checker result
or runtime observation.

## Declarative and executable interface

Define `LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates`
with two constructors retaining a complete selected child:

- `oneLevelGroupedConditional` retains the true classifier equation and a complete
  `OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates` child;
- `existing` retains the false equation and a complete
  `LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates` child.

Expose exactly these eight authored roots:

1. the two-way relation;
2. `elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?`;
3. the exact true-branch equation;
4. the exact false-branch equation;
5. checker `= some (core, type)` iff the relation;
6. checker `= none` iff no `core` and `type` inhabit the relation;
7. `core_hasType`, delegated literally to the selected child; and
8. provenance exposing the evaluated classifier equation and complete selected
   child.

The checker is the finite dispatch:

```text
if one-level-grouped-conditional source then ADR0326 source
else ADR0325 source
```

Add no new classifier, recursion, fuel, termination argument, source rewriting,
redundant `classified` theorem, child-field duplication, source union or generic
failure theorem to the minimum production module.

## Independent symbolic consumer

Create a consumer below 300 lines with exactly three authored public roots. Use
the established sparse table: first-match `apply` at Core variable 0 has
`(Word -> Word) -> Word`; a later duplicate `apply` has `Unit`; foreign-owner
`flag` at variable 3 has `Bool`; `ordinary` at variable 4 has `Word -> Word`;
and unrelated foreign opaque and wrong rows remain present. Runtime starts from
the literal nonempty opaque-closure/cell-reference/host-function store.

The true route covers the three ADR-0326 branch partitions beneath one whole
group: lambda/ordinary, ordinary/lambda and lambda/lambda. Construct each ADR-0326
child independently before the wrapper relation. Fix the true classifier, exact
true branch equation, literal checker result and Core, typing, and nested
provenance.

The false route represents the complete ADR-0325 partition with immediate
conditional, three-or-more-group lambda, exact-two-group lambda, one-group lambda,
direct lambda, ordinary singleton and all-ordinary conditional successes. For
each, prove equality of the entire wrapper `Option` to ADR-0325, not merely equal
successful Core terms, and retain the complete predecessor relation in provenance.

Recognized ADR-0326 failures include non-Bool or unresolved conditions, malformed
lambda headers or bodies, wrong or unresolved ordinary branches, non-function or
unresolved callees, and a direct lambda opposite a grouped or nested-call lambda.
They remain true-selected and final. Inherited recognized failures from ADR-0324,
ADR-0323 and the shallow expected-lambda adapters remain classifier-false and keep
their exact ADR-0325 result. Two outer conditional groups, grouped branch lambdas,
zero/multiple arguments, top-level conditionals, tuples, nested calls, returned
lambdas and inferred-let lambdas likewise preserve the complete false result.

All three new conditional Cores and the immediate ADR-0325 conditional execute for
both Boolean choices with fuel 13 exhausted and fuel 14 returning `Word 7` with the
exact initial store. Direct and finite-group lambda controls retain fuel 10/11.

## Independent parsed consumer

Create a consumer below 300 lines with exactly three authored public roots,
including one IO runner registered once in `Tests.Main`. Require clean lexer and
parser diagnostics, EOF, full-file span and proof-producing equality to hand-built
ASTs; do not derive equality from `BEq`.

Freeze the primary true-route source:

```text
apply((flag ? lam(x){return x;} : ordinary))
```

Its exact spans are call `0..44`, callee `0..5`, arguments `5..44`, outer group
`6..43`, conditional `7..42`, condition `7..11`, question `12..13`, lambda
`14..31`, colon `32..33`, and ordinary `34..42`. The lambda keyword, parameters,
parameter, body, return statement and returned identifier spans are `14..17`,
`17..20`, `18..19`, `20..31`, `21..30` and `28..29`. Its literal Core is
`apply (var 0) (ifE (var 3) (lambda Word Word (var 0)) (var 4))`.

Also freeze exact false-route ASTs and spans for:

- immediate conditional `apply(flag ? lam(x){return x;} : ordinary)` with call
  `0..42`, arguments `5..42` and conditional `6..41`;
- exact-two-group lambda `apply(((lam(x){return x;})))` with call `0..28`, groups
  `6..27` and `7..26`, and lambda `8..25`; and
- three-group lambda `apply((((lam(x){return x;}))))` with call `0..30`, groups
  `6..29`, `7..28` and `8..27`, and lambda `9..26`.

Cover the other true branch partitions plus compact recognized-failure and frozen
false-boundary loops. For every success, retain the complete selected child,
wrapper relation, exact checker result, Core typing and provenance. Exercise the
same fuel 13/14 and 10/11 boundaries with the exact nonempty store.

## Preserved and deferred boundaries

ADR-0317 through ADR-0326, every existing classifier, checker, relation and theorem,
`RecursiveLocalComputation`, canonical source unions, runtime entries and public wire
versions remain textually and semantically unchanged. The wrapper adds reachability
and fixed precedence only; it introduces no new expression or runtime semantics.

Remain deferred: two or more whole groups around a conditional; grouped conditional
branch lambdas; nested conditional/call, tuple, return, inferred-let and typed-body
expected propagation; multiple arguments and global resolution; canonical source
union integration; source closures, runtime-world safety, cost and backend
guarantees. Parser and diagnostic proof work remains paused, including the eight
existing untracked pause files.

## Prototype freeze and delivery contract

The production-shaped prototype is fixed at 153 lines with SHA-256
`5ef690bc3ffd950289dc83f7733288ca7bbea837540b2beac4bdd345a0f4a307`.
Its compiled artifact SHA-256 is
`b7ae807fb11e3395eb71524d92868124432981252b90b0169cba619bef9fcdc4`.
It has exactly eight authored roots and 15 owned declarations, all public. Every
declaration is safe and total, with no public simp or generated proof leak and no
axiom outside `propext`, `Classical.choice`, and `Quot.sound`. Port the source with
only namespace and module-comment adjustments, then freeze production ownership.

Use six commits: decision, production, symbolic consumer, parsed consumer,
umbrella/test registration, then `CURRENT_STATUS`/`FEATURE_MATRIX`/`M2_PLAN`
documentation. Keep production and both consumers strictly below 300 lines and
every commit at no more than 300 changed lines, over exactly nine tracked paths.

Before closure, verify exact ownership and generated names; safe/total flags;
public-root and all-owned axiom closure; masked forbidden-source and line-limit
scans; exact branch, recognized-failure and complete-predecessor probes; direct,
focused, umbrella and aggregate builds; direct parsed runner and full tests;
registration counts; git-range preservation of ADR-0317 through ADR-0326; the
eight paused files; and source/olean drift plus dependency closure. Do not record
a final implementation commit hash in this decision.
