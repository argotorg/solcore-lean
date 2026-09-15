# ADR-0336: Six-level grouped conditional expected-lambda applications

## Status

Accepted; add one standalone source-only exact-singleton adapter for an immediate
conditional beneath exactly six transparent whole-expression groups.

## Context

ADR-0324 checks an immediate conditional application argument at the inferred
callee parameter type when at least one immediate branch is an ungrouped direct
computation lambda. ADR-0326, ADR-0328, ADR-0330, ADR-0332 and ADR-0334 lift that
unchanged branch contract through exactly one through five whole-expression
groups. ADR-0335 is the current complete local-application wrapper: its true
branch is the exact ADR-0334 `Option`, and its false branch is the complete
unchanged ADR-0333 `Option`.

The next unhandled source has exactly six groups around the same immediate
conditional. ADR-0335 sees the exact-five ADR-0334 classifier as false because
the fifth group immediately contains a sixth group, not a conditional. It thus
returns the complete ADR-0333 `Option`. All older exact-depth conditional and
finite direct-lambda-spine classifiers remain false. On all three new success
partitions the current ADR-0335 result is literally `none`.

A direct branch opposite a grouped or nested lambda remains inside the selected
partition: the immediate direct branch establishes classification, while the
unchanged ordinary treatment of the opposite branch may reject it. General
conditional-group traversal and changed branch semantics remain outside this unit.

The reviewed baseline is final ADR-0335 HEAD
`8d9bfdf466b2332612ff0c15bd396f6057a48077`. Frozen ADR-0335 decision,
production, symbolic-consumer and parsed-consumer SHA-256 values are
`65e3f5b212ec1c48d0cde4d14f1cb17bf60762cd616a4639b38780303793171a`,
`2a1219fdd4b4f19ac1738de6864a71f1a23d4ab1c2ecbb697c5c07971a9be657`,
`6a586a70ce47265812c61d6bf4f8fe3e7f8e6b3e3dbca6d4b0041392289707e8` and
`832d251c91d23d9ef6072dfbe96278451ef6b6832ec8b425dd49a5764ba415f0`.
The independent ADR-0335 completion freeze is GREEN with zero issues at
`.lake/trace-audits/ADR0335CompletionIndependent.json`, SHA-256
`0564c4926f7f142974ee48eef4ac9cec89ef954c0419773cf233ad0bf75a5ad2`.

The production-shaped ADR-0336 prototype is frozen at
`.lake/trace-audits/ADR0336SixLevelGroupedConditionalExpectedLambdaArgumentApplicationPrototypeRoot.lean`,
247 lines and SHA-256
`518355410f3b34a533a25580ce35922b44e7b92bc7c51816f31b881b1df843f1`.
Its GREEN zero-issue audit has SHA-256
`2152d0f2662911737facfdadcdc48fdb01238ccf82a7d00c26975d0518b90e57`.

## Decision and exact source partition

Add `SixLevelGroupedConditionalExpectedLambdaArgumentApplication` as a separate
standalone adapter. Its classifier is true exactly for:

```text
call callee [group (group (group (group (group (group
  (conditional condition ? thenBranch : elseBranch))))))]
```

The call has exactly one argument. Its argument has exactly six outer groups;
the sixth group's immediate child is a conditional; and at least one immediate
branch satisfies the unchanged `isImmediateExpectedComputationLambda` classifier.
Classification is total and source-only. It ignores spans, owner, tables,
resolution, inferred types, diagnostics, checker results and runtime observations.

Conditional depths zero through five and seven or more are false. At exact depth
six, all-ordinary, grouped-only and nested-only branch shapes are false. Direct
computation lambdas at every group depth and branch-only grouping are false.

The partition is disjoint from all frozen predecessors: ADR-0334 requires its
fifth group to contain the conditional immediately; earlier exact-depth adapters
stop sooner; ADR-0324 requires an immediate conditional; and the finite
direct-lambda spine must terminate at a direct lambda.

Do not modify ADR-0335 or select this adapter in the current entry. ADR-0337 will
be a separate nonrecursive wrapper evaluating the new classifier once:

```text
if ADR0336-classifier(source)
then exact ADR0336 Option(source)
else exact ADR0335 Option(source)
```

A classifier-true `none` will be final. The future dispatch must not invoke
ADR-0335 after selected failure, use `Option.orElse`, retry based on checker
success, remove or add groups, rebuild the source, rewrite spans or recurse.

## Static semantics

Inspect the unchanged original call and six group nodes around the conditional.
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

The six groups are transparent only in this Core. Retain all six group spans in
declarative provenance and pass every original child to the existing checkers.
Selected semantic failure is final. Add no fallback, normalization, source
reconstruction, span rewriting, path enumeration, new recursion or fuel.

## Declarative and executable interface

Define `SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates`
with one `application` constructor. It retains call and argument-list spans, all
six group spans, conditional/question/colon spans, every original source child,
literal parameter/result types, and complete callee, Bool-condition and two
unchanged ADR-0324 branch derivations.

Expose exactly these eight authored public roots:

1. `isSixLevelGroupedConditionalExpectedLambdaArgumentApplication`;
2. `SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates`;
3. `elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?`;
4. `elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff`;
5. `elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?_eq_none_iff`;
6. `SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.core_hasType`;
7. `SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.classified`;
8. `SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.provenance`.

The frozen prototype measures exactly 8 roots, 37 owned declarations, 31 public
and 6 private, with no unrelated public declarations. The success theorem is
literal complete-checker/declarative correspondence; the failure theorem is exact
absence of every Core/type witness. `core_hasType`, `classified` and `provenance`
retain child typing, the source partition, all spans/children, complete child
derivations and literal Core equality.

Add no group extractor, recursive source checker, termination argument, new
branch relation/checker, wrapper, source union, public helper, generic failure
theorem or redundant generated surface. Production must remain below 300 lines
and port the 247-line frozen prototype byte-for-byte.

## Independent symbolic consumer

Create
`Solcore/Test/FrontendSixLevelGroupedConditionalExpectedLambdaArgumentApplicationProperties.lean`
strictly below 300 lines with exactly three authored public roots. Keep fixtures
and helpers private. Reuse the ADR-0334/ADR-0335 sparse table and exact owner,
duplicate-name, Bool, ordinary-function, opaque, wrong and unresolved rows.

Cover the three exact-depth-six successes: lambda/ordinary, ordinary/lambda and
lambda/lambda. Build complete callee, condition and two ADR-0324 branch children
before the new relation. Freeze the new classifier true, predecessor classifiers
false, literal checker/Core/type, Core typing, classification and six-group
provenance. For each success, prove the current ADR-0335 complete `Option` equals
its ADR-0333 false-branch result and is literally `none`.

Use exactly ten classifier-true selected failures: non-Bool and unresolved
conditions; malformed immediate-lambda header and body; wrong-typed and unresolved
ordinary branches; non-function and unresolved callees; and a direct lambda
opposite a grouped direct lambda or a nested-call lambda. Each proves the new
checker is exactly `none` and planned ADR-0337 selects it without fallback.

The classifier-false complete-Option matrix has exactly twenty-two shapes:

- conditional depths zero through five and depth seven;
- exact-depth-six all-ordinary, grouped-only and nested-only branches;
- direct lambdas at depths zero through seven; and
- an ordinary singleton, zero arguments, multiple arguments and a top-level
  non-call.

For every row prove planned dispatch equals the complete ADR-0335 `Option` and
retain relation/provenance when evidence exists. Outcomes are exactly sixteen
`some` and six `none`: the six shallower conditionals, all-ordinary row, eight
direct lambdas and ordinary singleton are `some`; depth-seven conditional,
grouped-only, nested-only, zero, multiple and top-level rows are `none`.

Also preserve actual `none` for exactly fourteen inherited or boundary sources:
representative ADR-0334, ADR-0332, ADR-0330, ADR-0328, ADR-0326, ADR-0324,
ADR-0323, ADR-0322, ADR-0320 and ADR-0317 selected failures, then tuple,
nested-call, returned-lambda and inferred-let-lambda boundaries. Expose a
universal false-route complete-Option equation.

The exact runtime-selection list has seventeen sources: three new successes, six
conditional controls at depths zero through five, and eight direct-lambda
controls at depths zero through seven. Aggregate success, runtime, and all
failure/preservation obligations into exactly three public roots using compact
tables and shared indexed proofs; never weaken a row to Boolean/Core-only checks.

## Independent parsed consumer

Create
`Solcore/Test/FrontendParsedSixLevelGroupedConditionalExpectedLambdaArgumentApplication.lean`
strictly below 300 lines with exactly three authored public roots, including one
IO runner registered once in `Tests.Main`. Require empty lexer/parser diagnostics,
EOF, full-file span and proof-producing structural equality to every hand-built
AST. Never derive propositional equality from `BEq`.

Freeze the primary source:

```text
apply(((((((flag ? lam(x){return x;} : ordinary)))))))
```

Its exact half-open spans are call/full file `0..54`, callee/name `0..5`,
arguments `5..54`, group spans `6..53`, `7..52`, `8..51`, `9..50`, `10..49`,
`11..48`, conditional `12..47`, condition/name `12..16`, question `17..18`,
lambda `19..36`, colon `37..38`, and ordinary identifier/name `39..47`.

Use the exact remaining success texts:

```text
apply(((((((flag ? ordinary : lam(x){return x;})))))))
apply(((((((flag ? lam(x){return x;} : lam(y){return y;})))))))
```

For all three, prove exact AST, complete child relations, new relation, classifier,
literal checker/Core/type, typing and full provenance. The primary Core is exactly
`apply (var 0) (ifE (var 3) (lambda Word Word (var 0)) (var 4))`.

Freeze proof-producing exact ASTs and spans for the exact-five predecessor
`apply((((((flag ? lam(x){return x;} : ordinary))))))` at call/full `0..52`;
the exact-seven boundary
`apply((((((((flag ? lam(x){return x;} : ordinary))))))))` at call/full `0..56`;
and the six-group direct-lambda control
`apply(((((((lam(x){return x;})))))))` at call/full `0..36`.

Mirror all ten selected failures, twenty-two false neighbors and fourteen
inherited actual-none cases. Thus parsed complete ADR-0335 preservation has
exactly thirty-six rows: sixteen `some` and twenty `none`. Every false row proves
literal whole-`Option` equality; every true failure proves selected ADR-0336
`none` final, retaining proof routes rather than only runtime equality.

## Runtime contract

The adapter erases six source groups and adds no Core node or runtime step. With
the exact nonempty opaque/cell/host environment and store, retain `Core.Evaluates`,
`runStateful_evaluation_sound`, determinism and identical store. Fuel 13 is
exactly `outOfFuel`; fuel 14 is `done (Word 7)`. Conditional controls at depths
zero through five retain 13/14; direct-lambda controls at depths zero through
seven retain 10/11. No runtime cost, result or store changes.

## Preserved, deferred and delivery boundaries

ADR-0317 through ADR-0335, every existing classifier, relation, checker and
theorem, ADR-0335's complete nested precedence, `RecursiveLocalComputation`, the
ADR-0324 branch checker, canonical source unions, runtime entries and wire
versions remain textually and semantically unchanged. This adds one opt-in leaf.

ADR-0337 is the next integration step: a nonrecursive source-only wrapper selecting
the complete ADR-0336 `Option` before the complete ADR-0335 `Option`. Seven or more
groups, a generic/deeper grouped-conditional spine, grouped branch lambdas,
broader expected propagation, source-union integration, source closures,
runtime-world safety, costs and backend guarantees remain deferred.
Parser/diagnostic proof work remains paused, including the existing eight files.

Deliver exactly six commits over exactly nine unique tracked paths: this decision;
`Solcore/Frontend/SixLevelGroupedConditionalExpectedLambdaArgumentApplication.lean`;
the two consumer paths above; additive registrations in `Solcore/Frontend.lean`
and `Tests/Main.lean`; and updates to `docs/CURRENT_STATUS.md`,
`docs/FEATURE_MATRIX.md` and `docs/M2_PLAN.md`.

Keep the decision, production and both consumers strictly below 300 lines, and
every commit at no more than 300 changed lines. Use `set_option autoImplicit false`.
Forbid `sorry`, `admit`, authored `axiom`, `unsafe`, `native_decide`, `partial`,
`noncomputable`, `extern`, `implemented_by`, `bv_decide` and `termination_by`.
Before closure verify exact 8/3/3 roots, 37/31/6 production ownership, safe/total
flags, public simp/proof leaks, axiom closure limited to `propext`,
`Classical.choice` and `Quot.sound`, masked source, selected-failure finality,
complete ADR-0335 preservation, normal/trust-zero/warnings/direct/full builds and
tests, runner, registration, exact six-commit/nine-path scope, dependency and
source/olean parity, kernel/metadata and unchanged paused files. Do not record a
final ADR-0336 implementation commit hash in this decision.
