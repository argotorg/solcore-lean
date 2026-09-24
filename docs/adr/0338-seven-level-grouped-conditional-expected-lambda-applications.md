# ADR-0338: Seven-level grouped conditional expected-lambda applications

## Status

Accepted; add one standalone source-only exact-singleton adapter for an immediate
conditional beneath exactly seven transparent whole-expression groups.

## Context

ADR-0324 checks an immediate conditional application argument at the inferred
callee parameter type when at least one immediate branch is an ungrouped direct
computation lambda. ADR-0326, ADR-0328, ADR-0330, ADR-0332, ADR-0334 and ADR-0336
lift that unchanged branch contract through exactly one through six whole-
expression groups. ADR-0337 is the current complete local-application wrapper:
its true branch is the exact ADR-0336 `Option`, and its false branch is the
complete unchanged ADR-0335 `Option`.

The next unhandled source has exactly seven groups around the same immediate
conditional. ADR-0337 sees the exact-six ADR-0336 classifier as false because the
sixth group immediately contains a seventh group, not a conditional. It thus
returns the complete ADR-0335 `Option`. All older exact-depth conditional and
finite direct-lambda-spine classifiers remain false. On all three new success
partitions the current ADR-0337 result is literally `none`.

A direct branch opposite a grouped or nested lambda remains inside the selected
partition: the immediate direct branch establishes classification, while the
unchanged ordinary treatment of the opposite branch may reject it. General
conditional-group traversal and changed branch semantics remain outside this unit.

The reviewed final ADR-0337 HEAD is
`3b4cb14d73e3b1a347c9c40c60efbf591404a853`, with tree
`187069ecb6844fd65624fc6e9b3917f131ffb088`. Its decision, production, symbolic
consumer and parsed consumer SHA-256 values are respectively
`50ca634bd8d8567e15b197239880a82db3eb591991be619ec4f8cbf7e4f4ca94`,
`c41aaad59b6e13e3483520bcf34905160c5478fb6facf735f6c4164c62957aeb`,
`9dc3c3e9311da46c20084538fc1536ad389d22c6d87d49777a248db9e99ef812` and
`3ce7646a6d467b9eb03218117312a9ed4c95ac13aec0a10be31170434468dc03`.
The GREEN zero-issue completion audit at
`.lake/trace-audits/ADR0337CompletionIndependent.json` has SHA-256
`833e985063dc50240ee45346452bfcf098dc99fb640100557f39e0a5e7b5feef`;
its byte-identical generator SHA-256 is
`c301b4af76620a5e940a5aab5dedec63a9fcde547c92bfde96592f28e9eae62d`.

## Decision and exact source partition

Add `SevenLevelGroupedConditionalExpectedLambdaArgumentApplication` as a separate
standalone adapter. Its classifier is true exactly for:

```text
call callee [group (group (group (group (group (group (group
  (conditional condition ? thenBranch : elseBranch)))))))]
```

The call has exactly one argument. Its argument has exactly seven outer groups;
the seventh group's immediate child is a conditional; and at least one immediate
branch satisfies the unchanged `isImmediateExpectedComputationLambda` classifier.
Classification is total and source-only. It ignores spans, owner, tables,
resolution, inferred types, diagnostics, checker results and runtime observations.

Conditional depths zero through six and eight or more are false. At exact depth
seven, all-ordinary, grouped-only and nested-only branch shapes are false. Direct
computation lambdas at every group depth and branch-only grouping are false.

The partition is disjoint from all frozen predecessors: ADR-0336 requires its
sixth group to contain the conditional immediately; earlier exact-depth adapters
stop sooner; ADR-0324 requires an immediate conditional; and the finite direct-
lambda spine must terminate at a direct lambda.

Do not modify ADR-0337 or select this adapter in the current entry. ADR-0339 will
be a separate nonrecursive wrapper evaluating the new classifier once:

```text
if ADR0338-classifier(source)
then exact ADR0338 Option(source)
else exact ADR0337 Option(source)
```

A classifier-true `none` will be final. The future dispatch must not invoke
ADR-0337 after selected failure, use `Option.orElse`, retry based on checker
success, remove or add groups, rebuild the source, rewrite spans or recurse.

## Static semantics

Inspect the unchanged original call and seven group nodes around the conditional.
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

The seven groups are transparent only in this Core. Retain all seven group spans
in declarative provenance and pass every original child to the existing checkers.
Selected semantic failure is final. Add no fallback, normalization, source
reconstruction, span rewriting, path enumeration, new recursion or fuel.

## Declarative and executable interface

Define `SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates`
with one `application` constructor. It retains call and argument-list spans, all
seven group spans, conditional/question/colon spans, every original source child,
literal parameter/result types, and complete callee, Bool-condition and two
unchanged ADR-0324 branch derivations.

Expose exactly these eight authored public roots:

1. `isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication`;
2. `SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates`;
3. `elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?`;
4. `elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff`;
5. `elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?_eq_none_iff`;
6. `SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.core_hasType`;
7. `SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.classified`;
8. `SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.provenance`.

The mechanically stable depth-four, depth-five and depth-six surfaces each measure
8 roots, 37 owned declarations, 31 public and 6 private; ADR-0338 must preserve
exactly that 8/37/31/6 budget with no unrelated public declaration. The success
theorem is literal complete-checker/declarative correspondence; the failure theorem
is exact absence of every Core/type witness. `core_hasType`, `classified` and
`provenance` retain child typing, the source partition, every span/child, complete
child derivations and literal Core equality.

The independent exact-seven production prototype freezes this mechanical extension
at 253 lines with source SHA-256
`2976d35a47f38f23e8be335cf9cd719d153f44874e08b66a49a34ca5722aaed8`.
Its normal, trust-zero, warning-as-error and importable artifacts are byte-identical
at SHA-256 `836ef3ce08f9168cb7142ff7403a08059d85bc3546148a6e25e563ff2a027237`;
its GREEN audit SHA-256 is
`2550edad1ce7c77135f337e8bb056240c2f6528f7be57561e531c8a3ae3d1db7`.
The audit generator SHA-256 is
`c80612b2f3386ffa24fc1d3022699a4302cb067c6bfefaafbe0d375ce7124ec8`;
its rerun is byte-identical.

Add no group extractor, recursive source checker, termination argument, new branch
relation/checker, wrapper, source union, public helper, generic failure theorem or
redundant generated surface. Production must remain strictly below 300 lines and
be the mechanical one-level extension of the frozen ADR-0336 implementation.

## Independent symbolic consumer

Create
`Solcore/Test/FrontendSevenLevelGroupedConditionalExpectedLambdaArgumentApplicationProperties.lean`
strictly below 300 lines with exactly three authored public roots. Keep fixtures
and helpers private. Reuse the ADR-0336/ADR-0337 sparse table and exact owner,
duplicate-name, Bool, ordinary-function, opaque, wrong and unresolved rows.

Cover the three exact-depth-seven successes: lambda/ordinary, ordinary/lambda and
lambda/lambda. Build complete callee, condition and two ADR-0324 branch children
before the new relation. Freeze the new classifier true, predecessor classifiers
false, literal checker/Core/type, Core typing, classification and seven-group
provenance. For each success, prove the current ADR-0337 complete `Option` equals
its ADR-0335 false-branch result and is literally `none`.

Use exactly ten classifier-true selected failures: non-Bool and unresolved
conditions; malformed immediate-lambda header and body; wrong-typed and unresolved
ordinary branches; non-function and unresolved callees; and a direct lambda
opposite a grouped direct lambda or a nested-call lambda. Each proves the new
checker is exactly `none` and planned ADR-0339 selects it without fallback.

The classifier-false complete-Option matrix has exactly twenty-four shapes:

- conditional depths zero through six and depth eight;
- exact-depth-seven all-ordinary, grouped-only and nested-only branches;
- direct lambdas at depths zero through eight; and
- an ordinary singleton, zero arguments, multiple arguments and a top-level
  non-call.

For every row prove planned dispatch equals the complete ADR-0337 `Option` and
retain its wrapper/nested-child relation and provenance when evidence exists.
Outcomes are exactly eighteen `some` and six `none`: seven shallower conditionals,
the all-ordinary row, nine direct lambdas and ordinary singleton are `some`; the
depth-eight conditional, grouped-only, nested-only, zero, multiple and top-level
rows are `none`. Expose a universal false-route complete-Option equation.

Also preserve actual `none` for exactly fifteen inherited or boundary sources:
representative ADR-0336, ADR-0334, ADR-0332, ADR-0330, ADR-0328, ADR-0326,
ADR-0324, ADR-0323, ADR-0322, ADR-0320 and ADR-0317 selected failures, then tuple,
nested-call, returned-lambda and inferred-let-lambda boundaries.

The exact runtime-selection list has nineteen sources: three new successes, seven
conditional controls at depths zero through six, and nine direct-lambda controls
at depths zero through eight. Aggregate the contract into exactly these public
roots: `all_three_seven_level_grouped_conditional_partitions_have_exact_semantics`,
`all_selected_and_control_cores_have_exact_fuel_and_store` and
`selected_failures_and_complete_adr0337_options_are_exact`. The private planned
ADR-0339 dispatcher must be the literal two-branch expression above.

## Independent parsed consumer

Create
`Solcore/Test/FrontendParsedSevenLevelGroupedConditionalExpectedLambdaArgumentApplication.lean`
strictly below 300 lines with exactly three authored public roots:
`parsed_seven_group_conditional_static_contract`,
`independently_executed_seven_group_conditional_core` and the registered runner
`Tests.adr0338ParsedSevenLevelGroupedConditionalExpectedLambdaTests`.

Require clean lexer/parser diagnostics, EOF, full-file span and proof-producing
structural equality to every hand-built AST; never derive propositional equality
from `BEq`. Freeze the primary source:

```text
apply((((((((flag ? lam(x){return x;} : ordinary))))))))
```

Its exact half-open spans are call/full file `0..56`, callee/name `0..5`,
arguments `5..56`, group spans `6..55`, `7..54`, `8..53`, `9..52`, `10..51`,
`11..50`, `12..49`, conditional `13..48`, condition/name `13..17`, question
`18..19`, lambda `20..37`, colon `38..39`, and ordinary identifier/name `40..48`.
Lambda keyword, parameters, parameter/name, body, return statement and returned
identifier/name spans are `20..23`, `23..26`, `24..25`, `26..37`, `27..36` and
`34..35`.

Use the other two exact success texts:

```text
apply((((((((flag ? ordinary : lam(x){return x;}))))))))
apply((((((((flag ? lam(x){return x;} : lam(y){return y;}))))))))
```

For all three prove exact AST, all complete child relations, the new relation,
classifier, literal checker/Core/type, typing and full provenance. The primary
Core remains `apply (var 0) (ifE (var 3) (lambda Word Word (var 0)) (var 4))`.

Freeze proof-producing exact ASTs and spans for the exact-six predecessor
`apply(((((((flag ? lam(x){return x;} : ordinary)))))))` at call/full `0..54`;
the exact-eight boundary
`apply(((((((((flag ? lam(x){return x;} : ordinary)))))))))` at `0..58`; and the
seven-group direct-lambda control `apply((((((((lam(x){return x;}))))))))` at
`0..38`. Predecessor group spans are `6..53`, `7..52`, `8..51`, `9..50`,
`10..49`, `11..48`, with conditional `12..47`. Boundary group spans are
`6..57`, `7..56`, `8..55`, `9..54`, `10..53`, `11..52`, `12..51`, `13..50`,
with conditional `14..49`. Lambda-control group spans are `6..37`, `7..36`,
`8..35`, `9..34`, `10..33`, `11..32`, `12..31`, with lambda `13..30`.

Mirror all ten selected failures, twenty-four false neighbors and fifteen
inherited actual-none cases. Thus parsed complete ADR-0337 preservation has
exactly thirty-nine rows: eighteen `some` and twenty-one `none`. Every false row
proves literal whole-`Option` equality; every true failure proves selected
ADR-0338 `none` final, retaining proof routes rather than runtime equality alone.

## Runtime contract

The adapter erases seven source groups and adds no Core node or runtime step. With
the exact nonempty opaque/cell/host environment and store, retain `Core.Evaluates`,
`runStateful_evaluation_sound`, determinism and identical store. Fuel 13 is
exactly `outOfFuel`; fuel 14 is `done (Word 7)`. Conditional controls at depths
zero through six retain 13/14; direct-lambda controls at depths zero through eight
retain 10/11. No runtime cost, result or store changes.

## Preserved, deferred and delivery boundaries

ADR-0317 through ADR-0337, every existing classifier, relation, checker and
theorem, ADR-0337's complete nested precedence, `RecursiveLocalComputation`, the
ADR-0324 branch checker, canonical source unions, runtime entries, and Core Wire
remain textually and semantically unchanged. This adds one opt-in leaf.

ADR-0339 is the next integration step: a nonrecursive source-only wrapper selecting
the complete ADR-0338 `Option` before the complete ADR-0337 `Option`. Eight or more
groups, a generic/deeper grouped-conditional spine, grouped branch lambdas,
broader expected propagation, source-union integration, source closures, runtime-
world safety, costs and backend guarantees remain deferred. Frontend semantics
remains the active priority. Parser/diagnostic proof work remains paused; preserve
the existing eight untracked pause files without staging, editing or removal.

Deliver exactly six commits over exactly nine unique tracked paths: this decision;
`Solcore/Frontend/SevenLevelGroupedConditionalExpectedLambdaArgumentApplication.lean`;
the two consumer paths above; additive registrations in `Solcore/Frontend.lean`
and `Tests/Main.lean`; and updates to `docs/CURRENT_STATUS.md`,
`docs/FEATURE_MATRIX.md` and `docs/M2_PLAN.md`.

Keep the decision, production and both consumers strictly below 300 lines, and
every commit at no more than 300 changed lines. Use `set_option autoImplicit false`.
Stage only exact paths and create no seventh completion commit. Forbid `sorry`,
`admit`, authored `axiom`, `unsafe`, `native_decide`, `partial`, `noncomputable`,
`extern`, `implemented_by`, `bv_decide` and `termination_by`. Before closure
verify exact 8/3/3 roots and production 37/31/6 ownership, safe/total flags,
public simp/proof leaks, axiom closure limited to `propext`, `Classical.choice`
and `Quot.sound`, masked source, the exact matrices and spans, selected-failure
finality, complete ADR-0337 preservation, normal/trust-zero/warnings/direct/full
builds and tests, runner, registration, exact six-commit/nine-path scope,
dependency and source/olean parity, kernel checks and unchanged paused files.
Do not record a final ADR-0338 implementation commit hash in this decision.
