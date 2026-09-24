# ADR-0334: Five-level grouped conditional expected-lambda applications

## Status

Accepted; add one standalone source-only exact-singleton adapter for an immediate
conditional beneath exactly five transparent whole-expression groups.

## Context

ADR-0324 checks an immediate conditional application argument at the inferred
callee parameter type when at least one immediate branch is an ungrouped direct
computation lambda. ADR-0326, ADR-0328, ADR-0330 and ADR-0332 lift that unchanged
branch contract through exactly one, two, three and four whole-expression groups.
ADR-0333 is the current complete local-application wrapper: its true branch is the
exact ADR-0332 `Option`, and its false branch is the complete unchanged ADR-0331
`Option`.

The next unhandled source has exactly five groups around the same immediate
conditional. ADR-0333 sees the exact-four ADR-0332 classifier as false because
the fourth group immediately contains a fifth group, not a conditional. It thus
returns the complete ADR-0331 `Option`. The older exact-depth conditional and
finite direct-lambda-spine classifiers also remain false. On all three new
success partitions the current ADR-0333 result is literally `none`.

A direct branch opposite a grouped or nested lambda remains inside the selected
source partition: the immediate direct branch establishes classification, while
the unchanged ordinary treatment of the opposite branch may reject it. Changing
branch semantics or introducing general conditional-group traversal is outside
this unit.

The reviewed baseline is HEAD
`a5525e8f03f6557097af04b7d2697658ebfbee88`. Frozen ADR-0332 decision and
production SHA-256 values are
`43e0e40902efbc0c38cba3db7922cf1a16f8be7666d00cbb36605f65428538c4` and
`68896b1246d2bfbe60c3d93abfc61d7f0fbaa224a2a3e55b4c29b872d5a76382`.
Frozen ADR-0333 decision and production SHA-256 values are
`e66c74b90938cb5f920fe98523b30d827b335503f5e47609ea6fa3ada9662b12`
and `2e96652168c86923b8e5dca2452c7c1bd2a7e2b622ef1c3d303f5f485a65e5b9`.
Its independent formal verification freeze is GREEN with zero issues at SHA-256
`3087de61cbe3440e396158d97273bba4b627a74212e04e81dcdc8cde0986c1e9`.

## Decision and exact source partition

Add `FiveLevelGroupedConditionalExpectedLambdaArgumentApplication` as a separate
standalone adapter. Its classifier is true exactly for:

```text
call callee [group (group (group (group (group
  (conditional condition ? thenBranch : elseBranch)))))]
```

The call has exactly one argument. Its argument has exactly five outer groups;
the fifth group's immediate child is a conditional; and at least one immediate
branch satisfies the unchanged `isImmediateExpectedComputationLambda` classifier.
Classification is total and source-only. It ignores spans, owner, tables,
resolution, inferred types, diagnostics, checker results and runtime observations.

Conditional depths zero through four and six or more are false. At exact depth
five, all-ordinary, grouped-only and nested-only branch shapes are false.
Branch-only grouping is false. Direct computation lambdas at every group depth
are false because the required terminal node is a conditional.

The partition is disjoint from the frozen predecessors: ADR-0332 requires its
fourth group to contain the conditional immediately; ADR-0330, ADR-0328 and
ADR-0326 stop after three, two and one groups; ADR-0324 requires an immediate
conditional; and the finite direct-lambda spine must terminate at a direct lambda.

Do not modify ADR-0333 or select this adapter in the current entry. ADR-0335 will
be a separate nonrecursive wrapper evaluating the new classifier once:

```text
if ADR0334-classifier(source)
then exact ADR0334 Option(source)
else exact ADR0333 Option(source)
```

A classifier-true `none` will be final. The future dispatch must not invoke
ADR-0333 after selected failure, use `Option.orElse`, retry based on checker
success, remove or add groups, rebuild the source, rewrite spans or recurse.

## Static semantics

Inspect the unchanged original call/group/group/group/group/group/conditional
nodes. Infer the original callee with `elaborateRecursiveLocalComputation?` and
require its type to be exactly `.function parameterType resultType`. Infer the
original condition with that same unchanged recursive checker and require exactly
`.bool`. At literal `parameterType`, check both original branch nodes with the
unchanged ADR-0324 `elaborateConditionalExpectedLambdaBranch?` contract:

- an immediate ungrouped direct computation lambda uses unchanged expected-lambda
  checking; and
- every other immediate branch uses unchanged recursive inference followed by
  exact type equality.

Return exactly:

```text
(.apply functionCore (.ifE conditionCore thenCore elseCore), resultType)
```

The five groups are transparent only in this Core. Retain all five group spans in
declarative provenance. Pass the original callee, condition and branch nodes to
the existing checkers. Selected semantic failure is final. Add no fallback,
normalization, source reconstruction, span rewriting, path enumeration, new
recursion or fuel.

## Declarative and executable interface

Define `FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates`
with one `application` constructor. It retains call and argument-list spans, all
five group spans, conditional/question/colon spans, every original source child,
literal parameter/result types, and complete callee, Bool-condition and two
unchanged ADR-0324 branch derivations.

Expose exactly these eight authored public roots:

1. `isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication`;
2. `FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates`;
3. `elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?`;
4. `elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff`;
5. `elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?_eq_none_iff`;
6. `FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.core_hasType`;
7. `FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.classified`;
8. `FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.provenance`.

The success theorem is literal complete-checker/declarative correspondence. The
failure theorem is exact absence of every Core/type witness. `core_hasType`
composes retained child typing only. `classified` fixes the exact source boundary.
`provenance` exposes five group spans, all other original spans and source nodes,
the branch-boundary equation, complete child derivations and literal Core equality.

Add no generic group extractor, recursive source checker, termination argument,
new branch relation/checker, wrapper, source union, public helper, generic failure
theorem or redundant generated public surface. A production-shaped implementation
must remain below 300 lines by mechanically extending ADR-0332 with one additional
group field and match.

## Independent symbolic consumer

Create
`Solcore/Test/FrontendFiveLevelGroupedConditionalExpectedLambdaArgumentApplicationProperties.lean`
strictly below 300 lines with exactly three authored public roots. Keep fixtures
and helpers private. Reuse the sparse table: first `apply` has
`(Word -> Word) -> Word`; a later duplicate has `Unit`; foreign-owner `flag` is
Bool variable 3; `ordinary` is `Word -> Word` variable 4; unrelated foreign
opaque and wrong rows remain.

Cover the three exact-depth-five successes: lambda/ordinary, ordinary/lambda and
lambda/lambda. Build complete callee, condition and two ADR-0324 branch children
before the new relation. Freeze the new classifier true, all predecessor
classifiers false, the literal checker/Core/type, Core typing, classification and
five-group provenance. For each success, prove the current ADR-0333 complete
`Option` equals its ADR-0331 false-branch result and is literally `none`.

Use exactly ten classifier-true selected failures:

- non-Bool and unresolved conditions;
- malformed immediate-lambda header and body;
- wrong-typed and unresolved ordinary branches;
- non-function and unresolved callees; and
- a direct lambda opposite a grouped direct lambda or a nested-call lambda.

Each row proves the new checker is exactly `none` and the literal planned ADR-0335
dispatch selects that `none` without inspecting or falling back to ADR-0333.

The classifier-false complete-Option matrix has exactly twenty shapes:

- conditional depths zero through four and depth six;
- exact-depth-five all-ordinary, grouped-only and nested-only branches;
- direct lambdas at depths zero through six; and
- an ordinary singleton, zero arguments, multiple arguments and a top-level
  non-call.

For every row prove the whole planned dispatch equals the complete ADR-0333
`Option` and retain its relation/nested provenance when evidence exists. The exact
tracked outcomes are fourteen `some` and six `none`: the five shallower
conditionals, all-ordinary row, seven direct lambdas and ordinary singleton are
`some`; the depth-six conditional, grouped-only, nested-only, zero, multiple and
top-level rows are `none`. This corrects the rejected initial 13/7 hypothesis;
the generic three-or-more direct-lambda spine accepts depth six.

Also preserve actual `none` for exactly thirteen inherited or boundary sources:
representative ADR-0332, ADR-0330, ADR-0328, ADR-0326, ADR-0324, ADR-0323,
ADR-0322, ADR-0320 and ADR-0317 selected failures, then tuple, nested-call,
returned-lambda and inferred-let-lambda boundaries. Expose a universal false-route
complete-Option equation.

The exact runtime-selection list has fifteen sources: three new successes, five
conditional controls at depths zero through four, and seven direct-lambda controls
at depths zero through six. Aggregate successes, runtime, and selected/inherited
failure plus complete-predecessor preservation into exactly three public roots.
Use compact data tables and shared indexed proofs so all exact rows fit below 300
lines; do not weaken any row to a Boolean-only or Core-only check.

## Independent parsed consumer

Create
`Solcore/Test/FrontendParsedFiveLevelGroupedConditionalExpectedLambdaArgumentApplication.lean`
strictly below 300 lines with exactly three authored public roots, including one
IO runner registered once in `Tests.Main`. Require empty lexer/parser diagnostics,
EOF, full-file span and proof-producing structural equality to each hand-built
AST. Never derive propositional equality from `BEq`.

Freeze the primary source:

```text
apply((((((flag ? lam(x){return x;} : ordinary))))))
```

Its parser-verified exact half-open spans are call/full file `0..52`, callee/name
`0..5`, arguments `5..52`, group spans `6..51`, `7..50`, `8..49`, `9..48`,
`10..47`, conditional `11..46`, condition/name `11..15`, question `16..17`,
lambda `18..35`, colon `36..37`, and ordinary identifier/name `38..46`. Lambda
keyword, parameters, parameter/name, body, return statement and returned
identifier/name are `18..21`, `21..24`, `22..23`, `24..35`, `25..34` and
`32..33`.

Use the exact remaining success texts:

```text
apply((((((flag ? ordinary : lam(x){return x;}))))))
apply((((((flag ? lam(x){return x;} : lam(y){return y;}))))))
```

For all three successes, prove exact AST, complete child relations, new relation,
classifier partition, literal checker/Core/type, typing and full provenance. The
primary Core is exactly `apply (var 0) (ifE (var 3)
(lambda Word Word (var 0)) (var 4))`.

Freeze proof-producing exact ASTs and spans for:

- the four-group predecessor
  `apply(((((flag ? lam(x){return x;} : ordinary)))))`, with call/full `0..50`,
  arguments `5..50`, groups `6..49`, `7..48`, `8..47`, `9..46`, conditional
  `10..45`;
- the six-group boundary
  `apply(((((((flag ? lam(x){return x;} : ordinary)))))))`, with call/full
  `0..54`, arguments `5..54`, groups `6..53`, `7..52`, `8..51`, `9..50`,
  `10..49`, `11..48`, and conditional `12..47`; and
- the five-group direct-lambda control `apply((((((lam(x){return x;}))))))`, with
  call/full `0..34`, arguments `5..34`, groups `6..33`, `7..32`, `8..31`,
  `9..30`, `10..29`, and lambda `11..28`.

Mirror all ten selected failures, twenty false neighbors and thirteen inherited
actual-none cases. Thus the parsed complete ADR-0333 preservation matrix contains
exactly thirty-three rows: fourteen `some` and nineteen `none`. Every false row
proves literal whole-`Option` equality; every true failure proves selected ADR-0334
`none` final. Retain proof routes rather than only runtime equality. Dense lists,
shared span constructors and loops are required to retain all obligations below
300 lines.

## Runtime contract

The adapter erases five source groups and adds no Core node or runtime step. Use
the exact nonempty environment and store containing an opaque closure, cell
reference and host function. For each new Core and both Boolean choices, retain
`Core.Evaluates`, `runStateful_evaluation_sound` and determinism. Fuel 13 is
exactly `outOfFuel`; fuel 14 is `done (Word 7)` with the identical store.

Conditional controls at depths zero through four retain 13/14. Direct-lambda
controls at depths zero through six retain 10/11. The standalone changes no Core,
environment, store, evaluation cost or result.

## Preserved, deferred and delivery boundaries

ADR-0317 through ADR-0333, every existing classifier, relation, checker and theorem,
ADR-0333's complete nested precedence, `RecursiveLocalComputation`, the ADR-0324
branch checker, canonical source unions, runtime entries, and Core Wire remain
textually and semantically unchanged. This unit adds only an opt-in static leaf.

ADR-0335 is the next integration step: a nonrecursive source-only wrapper selecting
the complete ADR-0334 `Option` before the complete ADR-0333 `Option`. Six or more
groups, a generic/deeper grouped-conditional spine, grouped branch lambdas, broader
nested/call/tuple/return/inferred-let/typed-body/multiple-argument/global expected
propagation, source-union integration, source closures, runtime-world safety,
costs and backend guarantees remain deferred. Parser/diagnostic proof work remains
paused, including the existing eight untracked files.

Deliver exactly six commits over exactly nine unique tracked paths: this decision;
`Solcore/Frontend/FiveLevelGroupedConditionalExpectedLambdaArgumentApplication.lean`;
the symbolic and parsed consumer paths named above; additive registrations in
`Solcore/Frontend.lean` and `Tests/Main.lean`; and documentation updates in
`docs/CURRENT_STATUS.md`, `docs/FEATURE_MATRIX.md` and `docs/M2_PLAN.md`.

Keep the decision, production and both consumers strictly below 300 lines, and
every commit at no more than 300 changed lines. Before production, freeze a scratch
prototype and direct/trust-zero artifact hashes. Use `set_option autoImplicit false`
in every Lean source. Forbid `sorry`, `admit`, authored `axiom`, `unsafe`,
`native_decide`, `partial`, `noncomputable`, `extern`, `implemented_by`,
`bv_decide` and `termination_by`. Before closure verify exact owned and generated
declarations, eight/three/three authored roots, safe/total flags, public simp/proof
leaks, all-owned axiom closure limited to `propext`, `Classical.choice` and
`Quot.sound`, masked forbidden-source and line scans, selected-failure finality,
complete ADR-0333 preservation, direct/focused/umbrella/full builds and tests,
parsed runner, kernel check, exact six-commit/nine-path scope, source/olean drift
and unchanged paused files. Do not record a final ADR-0334 implementation commit
hash in this decision.
