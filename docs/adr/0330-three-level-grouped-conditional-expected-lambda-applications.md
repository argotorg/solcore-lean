# ADR-0330: Three-level grouped conditional expected-lambda applications

## Status

Accepted; add one standalone exact-singleton adapter for an immediate conditional
beneath exactly three transparent whole-expression source groups.

## Context

ADR-0324 checks an immediate conditional application argument at the inferred
callee parameter type when at least one immediate branch is an ungrouped direct
computation lambda. ADR-0326 and ADR-0328 lift that exact branch contract through
respectively one and two transparent groups around the whole conditional.
ADR-0327 selects ADR-0326 before the older complete local-application result, and
ADR-0329 selects ADR-0328 before the complete unchanged ADR-0327 result.

The next unhandled source has exactly three groups around that same conditional.
The current ADR-0329 wrapper sees the exact-depth-two ADR-0328 classifier as false
because its second group immediately contains a third group rather than a
conditional. It therefore returns the complete ADR-0327 `Option` literally. The
older immediate-conditional and direct-lambda-spine classifiers also remain false:
they see a group or reach a conditional rather than an immediate direct lambda.

Changing conditional branch semantics is outside this unit. In particular, a
direct lambda opposite a grouped or nested lambda remains selected by the existing
branch boundary, and the unchanged ordinary-branch checker may reject the opposite
branch. Generalizing to arbitrary group depth would introduce recursive traversal
before exact depth three has been frozen independently.

The reviewed baseline is HEAD `f8f63cf642927a7768c4e426acb24d8b3fd379b8`.
Frozen decision/production SHA-256 pairs are ADR-0328
`77f688d38b60bbcbd8d63017c55579f43c8a2564eeaedba5e49ca0cb3ad12cf8` / `3bf4aece7e3b01abfe9bd1b816f54476022c92233a292ca66862bbb753880674`
and ADR-0329 `66db228670af823b7a8952e5037540055ed4c87d87127610fbf43326fe68dc16` / `4367b3582e81e743eceb6b80b2044bc05532e2805d2240d93a7c71e878749b5d`.

## Decision and exact source partition

Add `ThreeLevelGroupedConditionalExpectedLambdaArgumentApplication` as a separate
standalone adapter. Its classifier is true exactly for:

```text
call callee [group (group (group
  (conditional condition ? thenBranch : elseBranch)))]
```

The call has exactly one argument. That argument has exactly three outer groups,
the third group's immediate child is a conditional, and at least one immediate
branch is an ungrouped direct computation lambda according to the unchanged
`isImmediateExpectedComputationLambda` classifier. Classification is source-only;
it ignores spans, owner, tables, resolution, inferred types, header and body
validity, diagnostics, checker results and runtime observations.

Depths zero, one, two and four or more are false. Branch-only grouping is false. At exact
depth three, an all-ordinary conditional and a conditional whose lambda-bearing
branches are only grouped or nested are false. A direct branch opposite a grouped
or nested branch is true because the direct branch establishes the source
boundary; failure of the unchanged ordinary treatment of the opposite branch is
selected and final.

The new partition is structurally disjoint from every frozen predecessor:

- ADR-0328 expects its second group to contain the conditional immediately;
- ADR-0326 expects its first group to contain the conditional immediately;
- ADR-0324 expects an immediate conditional argument; and
- ADR-0323's finite direct-lambda spine cannot terminate at a conditional.

Do not modify ADR-0329 in this unit. A later additive wrapper may evaluate the new
classifier once on the unchanged source and dispatch exactly as follows:

```text
if ADR0330-classifier(source)
then exact ADR0330 Option(source)
else exact ADR0329 Option(source)
```

In that future wrapper, a classifier-true `none` is final. It must not invoke
ADR-0329 after selected failure, use `Option.orElse`, retry until a checker
succeeds, remove groups, rebuild the source or make dispatch depend on semantics.

## Static semantics

Inspect the unchanged original call/group/group/group/conditional source. Infer
the original callee with `elaborateRecursiveLocalComputation?` and require its
exact type to be `.function parameterType resultType`. Infer the original
condition and require its type to be exactly `.bool`. Check both original branch
nodes at the literal `parameterType` using the unchanged ADR-0324
`elaborateConditionalExpectedLambdaBranch?` contract:

- an immediate ungrouped direct lambda uses unchanged expected-lambda checking;
- every other immediate branch uses unchanged recursive inference and exact type
  equality.

Return exactly:

```text
(.apply functionCore (.ifE conditionCore thenCore elseCore), resultType)
```

The three groups are transparent only in this Core result. Retain all three group
spans in declarative provenance. Pass the original callee, condition and branch
nodes directly to existing checkers. Do not normalize or rewrite spans, invoke an
older adapter on a replacement source, enumerate paths, add recursion or fuel, or
try another checker after any recognized semantic failure.

## Declarative and executable interface

Define `ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates`
with one `application` constructor. Retain the call and argument-list spans, outer,
middle and inner group spans, conditional/question/colon spans, original callee,
condition and both branches, literal parameter and result types, and complete
callee, Bool-condition and two unchanged ADR-0324 branch derivations.

Expose exactly these eight authored roots:

1. `isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication`;
2. `ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates`;
3. `elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?`;
4. `elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff`;
5. `elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?_eq_none_iff`;
6. `ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.core_hasType`;
7. `ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.classified`;
8. `ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.provenance`.

The success theorem relates the literal complete checker result to the sole
constructor. The failure theorem states exact absence of every result witness.
`core_hasType` composes only retained child typing. `classified` fixes the exact
source boundary. `provenance` exposes all three group spans, every other original
span and source child, the branch-boundary equation, complete child derivations
and the literal Core equation.

Add no generic group extractor, recursive source checker, termination argument,
new branch relation or checker, wrapper, source union, public helper, generic
failure theorem or redundant generated public surface.

## Independent symbolic consumer

Create
`Solcore/Test/FrontendThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationProperties.lean`
strictly below 300 lines with exactly three authored public roots. Keep all
fixtures and helpers private. Reuse the established sparse table: first-match
`apply` is Core variable 0 with `(Word -> Word) -> Word`; a later duplicate has
`Unit`; foreign-owner `flag` is variable 3 with `Bool`; `ordinary` is variable 4
with `Word -> Word`; and the unrelated foreign opaque and wrong rows remain.

Cover all three exact-depth-three success partitions: lambda/ordinary,
ordinary/lambda and lambda/lambda. For each, independently construct the complete
callee, condition and two ADR-0324 branch children before constructing the
complete ADR-0330 relation. Freeze the new classifier true, ADR-0328/0326/0324 and
the finite direct-lambda-spine classifiers false, literal checker/Core/result
type, Core typing, classification and complete three-group provenance.

Also freeze the current predecessor route for every new source: ADR-0329 must be
the complete ADR-0327 `Option`, and on the three success shapes both are literally
`none`. The standalone remains unreachable until a later wrapper is added.

Use exactly these ten selected-failure categories:

- non-Bool condition and unresolved condition;
- malformed immediate-lambda header and malformed body;
- wrong-typed ordinary branch and unresolved ordinary branch;
- non-function callee and unresolved callee; and
- a direct lambda opposite a grouped direct lambda, and a direct lambda opposite
  a nested-call lambda.

Every row proves the new classifier true and the exact ADR-0330 result `none`.
Also prove that the literal planned dispatch expression returns ADR-0330's `none`
without inspecting or falling back to ADR-0329.

For classifier-false sources, prove the literal planned dispatch equals the
complete ADR-0329 `Option`, both `some` and `none`, and expose a universal
false-branch equation. Cover conditional depths zero, one, two and four; exact-
depth-three all-ordinary, grouped-only and nested-only shapes; direct lambdas at
group depths zero through four; an ordinary singleton; zero and multiple
arguments; top-level non-calls; tuples; nested calls; returned lambdas and
inferred-let lambdas. Retain complete ADR-0329 relations and nested provenance
where evidence exists.

Include actual `none` preservation for representative inherited failures from
ADR-0328, ADR-0326, ADR-0324, ADR-0323, ADR-0322, ADR-0320 and ADR-0317. Do not
claim ADR-0330 accepts any neighboring shape.

Aggregate the three success contracts in one public root, runtime controls in a
second, and selected/inherited failures plus complete predecessor `Option`
preservation in the third.

## Independent parsed consumer

Create
`Solcore/Test/FrontendParsedThreeLevelGroupedConditionalExpectedLambdaArgumentApplication.lean`
strictly below 300 lines with exactly three authored public roots, including one
IO runner registered exactly once in `Tests.Main`. Require clean lexer and parser
diagnostics, EOF, full-file span and proof-producing structural equality to each
hand-built AST; do not derive propositional equality from `BEq`.

Freeze the primary source:

```text
apply((((flag ? lam(x){return x;} : ordinary))))
```

Its exact half-open spans are call/full file `0..48`, callee/name `0..5`, arguments
`5..48`, outer group `6..47`, middle group `7..46`, inner group `8..45`,
conditional `9..44`, condition/name `9..13`, question `14..15`, then lambda
`16..33`, colon `34..35`, and ordinary identifier/name `36..44`. The lambda
keyword, parameters, parameter/name, body, return statement and returned
identifier/name spans are `16..19`, `19..22`, `20..21`, `22..33`, `23..32` and
`30..31`.

Freeze the other two success texts:

```text
apply((((flag ? ordinary : lam(x){return x;}))))
apply((((flag ? lam(x){return x;} : lam(y){return y;}))))
```

For all three sources prove the exact AST, complete child relations, ADR-0330
relation, classifier partition, literal checker/Core/type, typing and provenance.
The primary Core is `apply (var 0) (ifE (var 3)
(lambda Word Word (var 0)) (var 4))`.

Freeze exact ASTs and spans for a two-group conditional predecessor, a four-group
conditional boundary and a three-group direct-lambda predecessor. In particular,
the four-group conditional text
`apply(((((flag ? lam(x){return x;} : ordinary)))))` has call/full-file span
`0..50`, arguments `5..50`, group spans `6..49`, `7..48`, `8..47`, `9..46`, and
conditional span `10..45`; the three-group direct-lambda source
`apply((((lam(x){return x;}))))` has call `0..30`, arguments `5..30`, group spans
`6..29`, `7..28`, `8..27`, and lambda `9..26`.

Mirror the symbolic selected-failure, false-boundary and inherited-failure
matrices with parsed sources. Every false row must compare the entire planned
dispatch result with the complete ADR-0329 `Option`; every true failure must prove
the selected ADR-0330 `none` is final. Retain exact proof routes rather than only
Boolean equality checks.

## Runtime contract

The adapter erases only the three source groups and adds no Core node or runtime
step. Use the exact nonempty environment and store containing an opaque closure,
cell reference and host function. For each of the three new Cores and both Boolean
choices, independently retain `Core.Evaluates`, `runStateful_evaluation_sound` and
determinism. Fuel 13 is exactly `outOfFuel`; fuel 14 is exactly
`done (Word 7)` with the identical store.

Immediate, one-group and two-group conditional controls retain 13/14. Direct and
finite-group expected-lambda controls retain 10/11. The standalone must not change
Core, environment, store, evaluation cost or result.

## Preserved and deferred boundaries

ADR-0317 through ADR-0329, every existing classifier, relation, checker and
theorem, ADR-0329's complete two-level-first precedence, `RecursiveLocalComputation`,
the shared ADR-0324 branch checker, canonical source unions, runtime entries and
public wire versions remain textually and semantically unchanged. This unit adds
only an opt-in static adapter.

The next integration step is the additive wrapper that selects the complete
ADR-0330 result before the complete ADR-0329 result. Defer four or more
whole groups and any generic grouped-conditional spine; grouped conditional branch
lambdas; broader nested conditional/call, tuple, return, inferred-let and typed-
body expected propagation; multiple arguments and global resolution; canonical
source-union integration; source closures; runtime-world safety, costs and backend
guarantees. General parser and diagnostic proof development remains paused.

Preserve exactly the existing eight untracked pause files under `Solcore/Syntax`
and `Solcore/Syntax/Parser`; do not stage, edit or remove them.

## Prototype, verification and delivery contract

Before the production port, freeze a production-shaped scratch prototype and
audit its source hash, direct and trust-zero compiled artifact hashes, exact owned
and generated declarations, public/private split, safe/total flags, public simp
and proof leaks, and complete axiom closure. Permit only `propext`,
`Classical.choice` and `Quot.sound`; forbid `sorry`, `admit`, authored `axiom`,
`unsafe`, `native_decide`, `partial`, `noncomputable`, `extern`, `implemented_by`,
`bv_decide` and `termination_by`. Port the audited theorem bodies unchanged.

Deliver exactly six commits over exactly these nine unique tracked paths:

1. decision: `docs/adr/0330-three-level-grouped-conditional-expected-lambda-applications.md`;
2. production: `Solcore/Frontend/ThreeLevelGroupedConditionalExpectedLambdaArgumentApplication.lean`;
3. symbolic consumer: `Solcore/Test/FrontendThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationProperties.lean`;
4. parsed consumer: `Solcore/Test/FrontendParsedThreeLevelGroupedConditionalExpectedLambdaArgumentApplication.lean`;
5. registration: `Solcore/Frontend.lean` and `Tests/Main.lean`;
6. documentation: `docs/CURRENT_STATUS.md`, `docs/FEATURE_MATRIX.md` and
   `docs/M2_PLAN.md`.

Keep the decision, production and both consumers strictly below 300 lines. Keep
every commit at no more than 300 changed lines. Stage only the exact paths for
each commit; do not add a seventh completion commit or include scratch/paused
files.

Before closure verify exact ownership/generated names, safe/total flags, root and
all-owned axiom closure, masked forbidden-source and line-limit scans, exact source
partitions, selected-failure finality and universal complete ADR-0329 preservation;
direct/focused/umbrella/aggregate builds, direct parsed runner and full tests;
registration counts; exact six-commit/nine-path range; textual preservation of
ADR-0317 through ADR-0329 and all paused files; and source/olean drift plus
dependency closure. Do not record a final ADR-0330 implementation commit hash in
this decision.
