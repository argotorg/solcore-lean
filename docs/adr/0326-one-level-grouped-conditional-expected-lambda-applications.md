# ADR-0326: One-level grouped conditional expected-lambda applications

## Status

Accepted; add one standalone, exact-singleton adapter for a conditional argument
under exactly one transparent source group.

## Context

ADR-0324 checks an immediate conditional argument at a callee's inferred parameter
type when at least one branch is an immediate, ungrouped computation lambda. Its
branch relation sends those direct lambdas to expected checking and every other
immediate source to unchanged recursive checking with exact type equality.

ADR-0325 selects that complete conditional result before the finite group-spine
adapter and the frozen ADR-0322 local-application entry. It deliberately leaves a
group around the whole conditional outside the conditional classifier. The finite
spine classifier also rejects that source because its grouped terminal is a
conditional rather than a direct computation lambda.

The smallest disjoint semantic frontier is therefore one outer group around the
whole conditional. Grouping only a branch is not the next unit: a conditional with
one direct lambda and one grouped lambda is already ADR-0324-selected, so a branch
adapter would overlap a recognized-failure boundary or require an irregular
exclusion. Supporting every outer group depth would add recursion before the first
new source shape is independently settled.

## Decision

Add `OneLevelGroupedConditionalExpectedLambdaArgumentApplication` as a standalone
adapter. Its classifier is true exactly for this source shape:

```text
call callee [group (conditional condition ? thenBranch : elseBranch)]
```

The call must have exactly one argument, the argument must have exactly one outer
group whose immediate child is a conditional, and at least one conditional branch
must be an immediate, ungrouped direct computation lambda according to the unchanged
`isImmediateExpectedComputationLambda` classifier. Header and body validity, name
resolution, inferred types, owner, tables, checker results and runtime behavior do
not participate in source classification.

The selected source is structurally disjoint from both ADR-0325 classifiers:

- `isConditionalExpectedLambdaArgumentApplication` is false because the immediate
  argument is a group rather than a conditional; and
- `isThreeOrMoreGroupedExpectedLambdaArgumentApplication` is false because the
  one-element group spine ends at a conditional rather than a direct lambda.

ADR-0325 therefore continues to return the exact complete ADR-0322 result for every
newly classified source. Do not modify ADR-0325 in this unit. A later wrapper may
select ADR-0326 before the exact ADR-0325 result.

## Static semantics

Infer the original callee with `elaborateRecursiveLocalComputation?`. Require its
type to be `.function parameterType resultType`. Infer the original condition and
require its type to equal `.bool`. Check the two original branch subtrees at the
literal `parameterType` using the unchanged
`elaborateConditionalExpectedLambdaBranch?`:

- an immediate direct lambda uses the existing expected-lambda checker; and
- every other immediate branch uses unchanged recursive inference plus exact type
  equality.

Return exactly:

```text
(.apply functionCore (.ifE conditionCore thenCore elseCore), resultType)
```

The source group is transparent only in that Core result. The checker must inspect
the original nested pattern and pass the original callee, condition and branch
nodes directly to child checkers. It must not construct an ungrouped conditional,
rewrite spans, normalize the AST, call the ADR-0324 whole-application checker on a
replacement source, use `Option.orElse`, or fall through after any recognized
semantic failure. A selected `none` is final.

## Declarative and executable interface

Define `OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates` with
one constructor retaining the call span, argument-list span, group span,
conditional span, question and colon spans, all four original source children, the
callee function signature, and the complete callee, condition and two unchanged
ADR-0324 branch derivations.

Expose exactly these eight authored roots:

1. `isOneLevelGroupedConditionalExpectedLambdaArgumentApplication`;
2. the declarative relation;
3. `elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?`;
4. checker `= some (core, type)` iff the relation;
5. checker `= none` iff no `core` and `type` inhabit the relation;
6. `core_hasType`, composed from the retained child derivations;
7. `classified`, proving every relation inhabitant lies on the exact public
   boundary; and
8. `provenance`, exposing every original span and child, the branch-boundary
   equation, complete child derivations and literal Core equation.

Add no generic group extractor, recursion, fuel, termination argument, wrapper,
combined path enum, source union, redundant branch relation, public helper theorem,
or generated public proof surface to the minimum module.

## Independent symbolic consumer

Create a consumer below 300 lines with exactly three authored public roots. Reuse
the ADR-0325 sparse local table shape: `apply` at Core variable 0 has
`((Word -> Word) -> Word)`, `flag` at variable 3 has `Bool`, `ordinary` at variable
4 has `Word -> Word`, and unrelated duplicate/foreign rows remain present. Runtime
uses the exact nonempty opaque/cell-reference/host-function store.

The successful matrix contains all three branch partitions beneath exactly one
outer group:

- direct lambda / ordinary;
- ordinary / direct lambda; and
- direct lambda / direct lambda.

For each, fix the new classifier as true and both ADR-0325 classifiers as false;
construct the complete relation independently; prove the literal checker result,
Core typing, classification and provenance. Both Boolean choices must evaluate to
`Word 7` while preserving the literal initial store. The small-step runner boundary
remains fuel 13 = `outOfFuel` and fuel 14 = the exact completed result.

Recognized failures include a non-Bool condition, malformed direct-lambda header or
body, ordinary-branch exact-type mismatch, non-function callee, unresolved callee,
and a grouped direct lambda in the opposite branch. Fix that each remains selected
and that failure is final.

Freeze neighboring results rather than broadening them: the ungrouped conditional
continues to have the exact ADR-0325 result; two outer groups remain unclassified;
an all-ordinary grouped conditional remains unclassified by ADR-0326 and keeps the
exact ADR-0325/ADR-0322 result; zero or multiple arguments, top-level conditionals,
tuples, nested calls, returns and inferred lets remain unchanged.

## Independent parsed consumer

Create a second consumer below 300 lines with exactly three authored public roots.
Require clean diagnostics, EOF, full-file span and proof-producing equality to the
hand-built AST; do not derive equality from `BEq`.

Freeze this primary fixture:

```text
apply((flag ? lam(x){return x;} : ordinary))
```

Its exact spans are call `0..44`, callee `0..5`, arguments `5..44`, outer group
`6..43`, conditional `7..42`, condition `7..11`, question `12..13`, lambda
`14..31`, colon `32..33`, and ordinary branch `34..42`. Also fix lambda keyword
`14..17`, parameters `17..20`, parameter `18..19`, body `20..31`, return statement
`21..30`, and returned identifier `28..29`.

The literal Core is `apply (var 0) (ifE (var 3) (lambda Word Word (var 0))
(var 4))`. Prove its independent child relation, new relation, checker result,
typing, classification, provenance and both false legacy classifiers. Cover the
other two successful branch partitions compactly, plus the symbolic recognized
failures and frozen neighbors. Execute both Boolean choices with the exact nonempty
store and freeze fuel 13/14.

## Preserved and deferred boundaries

ADR-0317 through ADR-0325, every existing classifier, checker and relation,
`RecursiveLocalComputation`, canonical source unions, runtime entries and public
wire versions remain textually and semantically unchanged. This unit adds an
opt-in static adapter only.

Remain deferred: a wrapper selecting this adapter; two or more groups around a
conditional; grouped conditional branch lambdas; nested conditional/call
propagation; tuple, return, inferred-let and typed-body expected propagation;
multiple arguments and global resolution; runtime-world safety, cost and backend
guarantees; principal inference, coercion and overload policy. Parser and
diagnostic proof work remains paused, including the eight existing untracked pause
files.

## Prototype freeze and delivery contract

The independent production-shaped prototype is fixed at 214 lines with SHA-256
`974d4f06922d9c51a28808ef0a34df68f45520d85a77e8952331dd3c540e9487`.
Its compiled artifact SHA-256 is
`128f6d95de5524b3f32db1779e76d2ff2e96fc12145947b613ac8b925f22c32a`.
It has exactly eight authored roots. All are safe and total, with no generated
partial helper, public generated leak, public simp leak, or axiom outside
`propext`, `Classical.choice`, and `Quot.sound`. Port it with only namespace and
module-comment adjustments, then freeze production ownership independently.

Use six commits: decision, production, symbolic consumer, parsed consumer,
umbrella/test registration, then `CURRENT_STATUS`/`FEATURE_MATRIX`/`M2_PLAN`
documentation. Keep the production module and both consumers strictly below 300
lines and every commit at no more than 300 changed lines.

Before closure, verify exact module ownership and generated names; safe/total flags;
public-root and all-owned axiom closure; masked forbidden-source and line-limit
scans; exact source partition, success, recognized-failure and frozen-result probes;
direct, focused, umbrella and aggregate builds; the direct parsed runner and full
test suite; registration counts; git-range preservation of ADR-0317 through
ADR-0325; the eight paused files; and source/olean drift plus dependency closure.
Do not record a final implementation commit hash in this decision.
