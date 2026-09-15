# ADR-0332: Four-level grouped conditional expected-lambda applications

## Status

Accepted; add one standalone source-only exact-singleton adapter for an immediate
conditional beneath exactly four transparent whole-expression groups.

## Context

ADR-0324 checks an immediate conditional application argument at the inferred
callee parameter type when at least one immediate branch is an ungrouped direct
computation lambda. ADR-0326, ADR-0328 and ADR-0330 lift that unchanged branch
contract through exactly one, two and three whole-expression groups. ADR-0331 is
the current complete opt-in local-application wrapper: its true branch is the
exact ADR-0330 `Option`, and its false branch is the complete unchanged ADR-0329
`Option`.

The next unhandled source has exactly four groups around the same immediate
conditional. ADR-0331 sees the exact-three ADR-0330 classifier as false because
the third group immediately contains a fourth group, not a conditional. It thus
returns the complete ADR-0329 `Option`. The older exact-depth conditional and
finite direct-lambda-spine classifiers also remain false. On all three new
success partitions the current ADR-0331 result is literally `none`.

A direct branch opposite a grouped or nested lambda remains inside the selected
source partition: the immediate direct branch establishes classification, while
the unchanged ordinary treatment of the opposite branch may reject it. Changing
branch semantics or introducing general group traversal is outside this unit.

The reviewed baseline is HEAD
`d0aed67491a4597feffeb89d8bface74429eef19`. Frozen ADR-0330 decision and
production SHA-256 values are
`56722882d91754beab547ca3d357542b6dfba1129644395645d824185eef24ca` and
`d4a6ad3f3f52980817e263aa591b9c09a0436d70b729a9e03dc4bb02fe9ce705`.
Frozen ADR-0331 decision and production SHA-256 values are
`e139303451fe91a9c2bb9e3f1e257b42da607e8d306740733321fd51ab418c26`
and `7720fc27b26f31632a47d65ec626db990c4e78325cecb1032d5fd8fd70ef23d2`.
Its final independent formal audit is GREEN with zero issues at SHA-256
`ca332c5a09a25092065e01fdaff955ce73e06d7e87c28dbc9078c38ab68b4041`.

## Decision and exact source partition

Add `FourLevelGroupedConditionalExpectedLambdaArgumentApplication` as a separate
standalone adapter. Its classifier is true exactly for:

```text
call callee [group (group (group (group
  (conditional condition ? thenBranch : elseBranch))))]
```

The call has exactly one argument. Its argument has exactly four outer groups;
the fourth group's immediate child is a conditional; and at least one immediate
branch satisfies the unchanged `isImmediateExpectedComputationLambda` classifier.
Classification is total and source-only. It ignores spans, owner, tables,
resolution, inferred types, diagnostics, checker results and runtime observations.

Conditional depths zero, one, two, three and five or more are false. At exact
depth four, all-ordinary, grouped-only and nested-only branch shapes are false.
Branch-only grouping is false. Direct computation lambdas at every group depth
are false because the required terminal node is a conditional.

The partition is disjoint from the frozen predecessors: ADR-0330 requires its
third group to contain the conditional immediately; ADR-0328 and ADR-0326 stop
after two and one groups; ADR-0324 requires an immediate conditional; and the
finite direct-lambda spine must terminate at a direct lambda.

Do not modify ADR-0331 or select this adapter in the current entry. ADR-0333 will
be a separate nonrecursive wrapper evaluating the new classifier once:

```text
if ADR0332-classifier(source)
then exact ADR0332 Option(source)
else exact ADR0331 Option(source)
```

A classifier-true `none` will be final. The future dispatch must not invoke
ADR-0331 after selected failure, use `Option.orElse`, retry based on checker
success, remove or add groups, rebuild the source, rewrite spans or recurse.

## Static semantics

Inspect the unchanged original call/group/group/group/group/conditional nodes.
Infer the original callee with `elaborateRecursiveLocalComputation?` and require
its type to be exactly `.function parameterType resultType`. Infer the original
condition with that same unchanged recursive checker and require exactly `.bool`.
At literal `parameterType`, check both original branch nodes with the unchanged
ADR-0324 `elaborateConditionalExpectedLambdaBranch?` contract:

- an immediate ungrouped direct computation lambda uses unchanged expected-lambda
  checking; and
- every other immediate branch uses unchanged recursive inference followed by
  exact type equality.

Return exactly:

```text
(.apply functionCore (.ifE conditionCore thenCore elseCore), resultType)
```

The four groups are transparent only in this Core. Retain all four group spans in
declarative provenance. Pass the original callee, condition and branch nodes to
the existing checkers. Selected semantic failure is final. Add no fallback,
normalization, source reconstruction, span rewriting, path enumeration, new
recursion or fuel.

## Declarative and executable interface

Define `FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates`
with one `application` constructor. It retains call and argument-list spans, all
four group spans, conditional/question/colon spans, every original source child,
literal parameter/result types, and complete callee, Bool-condition and two
unchanged ADR-0324 branch derivations.

Expose exactly these eight authored public roots:

1. `isFourLevelGroupedConditionalExpectedLambdaArgumentApplication`;
2. `FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates`;
3. `elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?`;
4. `elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff`;
5. `elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?_eq_none_iff`;
6. `FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.core_hasType`;
7. `FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.classified`;
8. `FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.provenance`.

The success theorem is literal complete-checker/declarative correspondence. The
failure theorem is exact absence of every Core/type witness. `core_hasType`
composes retained child typing only. `classified` fixes the exact source boundary.
`provenance` exposes four group spans, all other original spans and source nodes,
the branch-boundary equation, complete child derivations and literal Core equality.

Add no generic group extractor, recursive source checker, termination argument,
new branch relation/checker, wrapper, source union, public helper, generic failure
theorem or redundant generated public surface. A production-shaped implementation
is expected to remain comfortably below 300 lines by extending ADR-0330 with one
additional group field and match.

## Independent symbolic consumer

Create
`Solcore/Test/FrontendFourLevelGroupedConditionalExpectedLambdaArgumentApplicationProperties.lean`
strictly below 300 lines with exactly three authored public roots. Keep fixtures
and helpers private. Reuse the sparse table: first `apply` has
`(Word -> Word) -> Word`; a later duplicate has `Unit`; foreign-owner `flag` is
Bool variable 3; `ordinary` is `Word -> Word` variable 4; unrelated foreign
opaque and wrong rows remain.

Cover the three exact-depth-four successes: lambda/ordinary, ordinary/lambda and
lambda/lambda. Build complete callee, condition and two ADR-0324 branch children
before the new relation. Freeze the new classifier true, all predecessor
classifiers false, the literal checker/Core/type, Core typing, classification and
four-group provenance. For each success, prove the current ADR-0331 complete
`Option` equals its ADR-0329 false-branch result and is literally `none`.

Use exactly ten classifier-true selected failures:

- non-Bool and unresolved conditions;
- malformed immediate-lambda header and body;
- wrong-typed and unresolved ordinary branches;
- non-function and unresolved callees; and
- a direct lambda opposite a grouped direct lambda or a nested-call lambda.

Each row proves the new checker is exactly `none` and the literal planned ADR-0333
dispatch selects that `none` without inspecting or falling back to ADR-0331.

The classifier-false complete-Option matrix has exactly eighteen shapes:

- conditional depths zero, one, two, three and five;
- exact-depth-four all-ordinary, grouped-only and nested-only branches;
- direct lambdas at depths zero through five; and
- an ordinary singleton, zero arguments, multiple arguments and a top-level
  non-call.

For every row prove the whole planned dispatch equals the complete ADR-0331
`Option`, whether `some` or `none`, and retain its relation/nested provenance when
evidence exists. Also preserve actual `none` for exactly twelve inherited or
boundary sources: representative ADR-0330, ADR-0328, ADR-0326, ADR-0324, ADR-0323,
ADR-0322, ADR-0320 and ADR-0317 selected failures, then tuple, nested-call,
returned-lambda and inferred-let-lambda boundaries. Expose a universal false-route
complete-Option equation.

The exact runtime-selection list has thirteen sources: three new successes, four
conditional controls at depths zero through three, and six direct-lambda controls
at depths zero through five. Aggregate successes, runtime, and selected/inherited
failure plus complete-predecessor preservation into exactly three public roots.
Use compact data tables and shared indexed proofs so all exact rows fit below 300
lines; do not weaken any row to a Boolean-only or Core-only check.

## Independent parsed consumer

Create
`Solcore/Test/FrontendParsedFourLevelGroupedConditionalExpectedLambdaArgumentApplication.lean`
strictly below 300 lines with exactly three authored public roots, including one
IO runner registered once in `Tests.Main`. Require empty lexer/parser diagnostics,
EOF, full-file span and proof-producing structural equality to each hand-built
AST. Never derive propositional equality from `BEq`.

Freeze the primary source:

```text
apply(((((flag ? lam(x){return x;} : ordinary)))))
```

Its exact half-open spans are call/full file `0..50`, callee/name `0..5`, arguments
`5..50`, group spans `6..49`, `7..48`, `8..47`, `9..46`, conditional `10..45`,
condition/name `10..14`, question `15..16`, lambda `17..34`, colon `35..36`, and
ordinary identifier/name `37..45`. Lambda keyword, parameters, parameter/name,
body, return statement and returned identifier/name are `17..20`, `20..23`,
`21..22`, `23..34`, `24..33` and `31..32`.

Use the exact remaining success texts:

```text
apply(((((flag ? ordinary : lam(x){return x;})))))
apply(((((flag ? lam(x){return x;} : lam(y){return y;})))))
```

For all three successes, prove exact AST, complete child relations, new relation,
classifier partition, literal checker/Core/type, typing and full provenance. The
primary Core is exactly `apply (var 0) (ifE (var 3)
(lambda Word Word (var 0)) (var 4))`.

Freeze proof-producing exact ASTs and spans for:

- the three-group predecessor
  `apply((((flag ? lam(x){return x;} : ordinary))))`, with call/full `0..48`,
  arguments `5..48`, groups `6..47`, `7..46`, `8..45`, conditional `9..44`;
- the five-group boundary
  `apply((((((flag ? lam(x){return x;} : ordinary))))))`, with call/full `0..52`,
  arguments `5..52`, groups `6..51`, `7..50`, `8..49`, `9..48`, `10..47`,
  conditional `11..46`; and
- the four-group direct-lambda control `apply(((((lam(x){return x;})))))`, with
  call/full `0..32`, arguments `5..32`, groups `6..31`, `7..30`, `8..29`,
  `9..28`, and lambda `10..27`.

Mirror all ten selected failures, eighteen false neighbors and twelve inherited
actual-none cases. Thus the parsed complete ADR-0331 preservation matrix contains
exactly thirty rows. Every false row proves literal whole-`Option` equality; every
true failure proves selected ADR-0332 `none` final. Retain proof routes rather than
only runtime equality. Dense lists, shared span constructors and loops are required
to retain all obligations below 300 lines.

## Runtime contract

The adapter erases four source groups and adds no Core node or runtime step. Use
the exact nonempty environment and store containing an opaque closure, cell
reference and host function. For each new Core and both Boolean choices, retain
`Core.Evaluates`, `runStateful_evaluation_sound` and determinism. Fuel 13 is
exactly `outOfFuel`; fuel 14 is `done (Word 7)` with the identical store.

Conditional controls at depths zero through three retain 13/14. Direct-lambda
controls at depths zero through five retain 10/11. The standalone changes no Core,
environment, store, evaluation cost or result.

## Preserved, deferred and delivery boundaries

ADR-0317 through ADR-0331, every existing classifier, relation, checker and theorem,
ADR-0331's complete nested precedence, `RecursiveLocalComputation`, the ADR-0324
branch checker, canonical source unions, runtime entries and wire versions remain
textually and semantically unchanged. This unit adds only an opt-in static leaf.

ADR-0333 is the next integration step: a nonrecursive source-only wrapper selecting
the complete ADR-0332 `Option` before the complete ADR-0331 `Option`. Five or more
groups, a generic/deeper grouped-conditional spine, grouped branch lambdas, broader
nested/call/tuple/return/inferred-let/typed-body/multiple-argument/global expected
propagation, source-union integration, source closures, runtime-world safety,
costs and backend guarantees remain deferred. Parser/diagnostic proof work remains
paused, including the existing eight untracked files.

Deliver exactly six commits over exactly nine unique tracked paths: this decision;
`Solcore/Frontend/FourLevelGroupedConditionalExpectedLambdaArgumentApplication.lean`;
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
`Quot.sound`, masked forbidden-source and line scans,
selected-failure finality, complete ADR-0331 preservation, direct/focused/umbrella/
full builds and tests, parsed runner, kernel/metadata, exact six-commit/nine-path
scope, source/olean drift and unchanged paused files. Do not record a final ADR-0332
implementation commit hash in this decision.
