# ADR-0325: Conditional-first finite-group local applications

## Status

Accepted; add one nonrecursive, opt-in, source-only wrapper that selects ADR-0324 first,
ADR-0323 second, and the complete unchanged ADR-0322 entry otherwise.

## Context

ADR-0322 is the frozen unified entry for ordinary singleton applications and direct
expected lambdas under zero, one, or two source groups. ADR-0323 adds a standalone
adapter for every finite maximal group spine of depth at least three ending immediately
at a direct computation lambda. ADR-0324 adds one for an immediate conditional argument
with at least one immediate, ungrouped direct computation-lambda branch.

The two new semantic leaves are intentionally unreachable from ADR-0322. Trying the
standalone checkers in sequence would make precedence depend on semantic success: a
malformed recognized conditional or group spine could be reinterpreted later. Reopening
an accepted checker or relation would change a frozen boundary. An ordered wrapper is
therefore the smallest additive unit.

## Decision

Add `LocalApplicationWithConditionalAndFiniteGroupedExpectedLambda` as a separate entry.
Dispatch on the unchanged original `Syntax.Expr` in this exact order:

| Source equation | Selected complete result |
| --- | --- |
| `isConditionalExpectedLambdaArgumentApplication source = true` | `elaborateConditionalExpectedLambdaArgumentApplication? ... source` |
| conditional `= false`, `isThreeOrMoreGroupedExpectedLambdaArgumentApplication source = true` | `elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? ... source` |
| both classifiers `= false` | `elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? ... source` |

Return the selected `Option` literally. Once either true boundary is recognized, its
checker result is final, including `none`. Do not use `Option.orElse`, try checkers until
one succeeds, shorten a group spine, unwrap a conditional branch, rebuild or normalize
the AST, or fall through after any semantic failure.

Do not add a combined classifier or path enum. The two settled public Boolean classifiers
already express the source partition; another public surface would duplicate policy.
They inspect no callee resolution, inferred type, owner, tables, diagnostics, checker
result, or runtime behavior.

The nominal `(true, true)` pair is structurally impossible. ADR-0324 requires the sole
argument payload to be an immediate conditional; ADR-0323 requires that payload to begin
a maximal group spine ending at a direct lambda. Invert the conditional shape and apply
the public ADR-0323 classifier equivalence; no private extractor is needed. Keep both
ordered equations on the group path. The disjointness lemma is not minimum production API.

## Declarative and executable interface

Define `LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates` with
three constructors, each retaining the complete selected child:

- `conditional`: the conditional classifier is true and a complete ADR-0324
  `ConditionalExpectedLambdaArgumentApplicationElaborates` child exists;
- `threeOrMoreGrouped`: the conditional classifier is false, the finite-spine
  classifier is true, and a complete ADR-0323
  `ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates` child exists;
- `existing`: both classifiers are false and a complete ADR-0322
  `LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates` child exists.

Expose exactly these nine authored roots:

1. the three-way relation;
2. `elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?`;
3. the exact conditional branch equation;
4. the exact three-or-more-grouped branch equation;
5. the exact existing branch equation;
6. checker `= some (core, type)` iff the relation;
7. checker `= none` iff no `core` and `type` inhabit the relation;
8. `core_hasType`, delegated literally to the selected child; and
9. nested provenance exposing every evaluated classifier equation and the
   complete selected child.

The checker is finite nested pattern-independent dispatch:

```text
if conditional source then ADR0324 source
else if threeOrMoreGrouped source then ADR0323 source
else ADR0322 source
```

Add no recursion, fuel, termination argument, source rewriting, redundant `classified`
theorem, child-field duplication, or generic failure theorem to the minimum module.

## Independent symbolic consumer

Create a consumer below 300 lines with exactly three authored public roots:
`all_three_dispatch_routes_have_exact_semantics`,
`all_selected_cores_execute_without_store_change`, and
`recognized_failures_and_frozen_results_are_exact`. Keep helpers private.

Use an empty type table; sparse `apply` owner/index 17 of `(Word -> Word) -> Word`
at Core var 0; a later duplicate `apply` at owner/index 3 with `Unit`; foreign-owner
701 `flag : Bool` at var 3; owner/index 29 `ordinary : Word -> Word` at var 4;
foreign-owner 702 `Word` at var 5; and foreign-owner 700 opaque closure. Runtime
starts from the exact nonempty opaque/cell-reference/host-function store.

The exact success and preservation matrix is:

| Route | Sources |
| --- | --- |
| ADR-0324 `(true, false)` | lambda/ordinary, ordinary/lambda, lambda/lambda immediate conditional partitions |
| ADR-0323 `(false, true)` | direct-lambda group spines at depths 3, 4, and 16 |
| ADR-0322 `(false, false)` | direct, depth-1, depth-2 lambdas; ordinary at depths 0, 1, and 3; all-ordinary conditional |

Construct each selected child independently before the wrapper relation and iff.
Fix literal Core terms, inferred types, typing, classifier pairs, ordered group
spans, and nested provenance. For the existing route, also prove equality of the
entire wrapper `Option` to ADR-0322, not only equality of successful Core terms.

Construct `Core.Evaluates` independently. Both Boolean choices for all three
conditional partitions yield `Word 7` and the literal initial store. Depths 3
and 16, the direct/depth-1/depth-2 old paths, and the old all-ordinary
conditional likewise execute their stated Core terms and preserve that store.

Recognized ADR-0324 failures include a non-Bool condition, bad immediate-lambda
header, ordinary-branch exact-type mismatch, unresolved callee, and an immediate
lambda opposite a three-group lambda. The last source remains ADR-0324-selected;
its grouped branch is ordinary-selected and failure is final. Recognized
ADR-0323 failures include bad terminal header/body and non-function or unresolved
callees. Malformed old direct/depth-1/depth-2 lambdas and zero/multiple arguments,
top-level forms, nested calls, tuples, returns, and inferred lets retain their
exact ADR-0322 results. Exercise all three generic branch equations first.

## Independent parsed consumer

Create a consumer below 300 lines with exactly three authored public roots:
`parsed_unified_static_contract`, `independently_executed_unified_core`, and
`Tests.adr0325ParsedLocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaTests`.
Require clean diagnostics, EOF/full-file span, equality to each hand-built AST, exact
classifier pairs, independent child and wrapper relations, literal Core, typing, and
provenance. Do not derive equality from `BEq`; `Syntax.Expr` lacks `LawfulBEq`.

Freeze these primary exact fixtures:

| Route | Text | Exact outer spans |
| --- | --- | --- |
| ADR-0324 | `apply(flag ? lam(x){return x;} : ordinary)` | call `0..42`, callee `0..5`, args `5..42`, conditional `6..41`, condition `6..10`, `?` `11..12`, then lambda `13..30`, `:` `31..32`, else `33..41` |
| ADR-0323 | `apply((((lam(x){return x;}))))` | call `0..30`, callee `0..5`, args `5..30`, groups `6..29`, `7..28`, `8..27`, lambda `9..26` |
| ADR-0322 | `apply(((lam(x){return x;})))` | call `0..28`, callee `0..5`, args `5..28`, groups `6..27`, `7..26`, lambda `8..25` |

For the conditional lambda, also freeze keyword `13..16`, parameters `16..19`,
parameter `17..18`, body `19..30`, return statement `20..29`, and result
`27..28`. Its literal Core is `apply (var 0) (ifE (var 3)
(lambda Word Word (var 0)) (var 4))`; both grouped fixtures elaborate to
`apply (var 0) (lambda Word Word (var 0))`.

The compact preservation loop covers the other two conditional partitions;
group-spine depths 4 and 8; direct/depth-1 lambdas; ordinary depths 0, 1, and 3;
and the exact old all-ordinary conditional result. The failure loop mirrors the
symbolic recognized failures and checks grouped conditionals, nested calls,
tuples, zero/multiple arguments, and top-level conditionals against ADR-0322.

Runtime fuel is exact:

| Core family | Lower fuel | Completing fuel |
| --- | --- | --- |
| three conditional modes, both Boolean choices, plus old all-ordinary conditional | 13 = `outOfFuel` | 14 = `done (Word 7)` with the exact initial store |
| expected-lambda applications at depths 2, 3, 4, and 8 | 10 = `outOfFuel` | 11 = `done (Word 7)` with the exact initial store |

## Preserved and deferred boundaries

ADR-0317 through ADR-0324, every existing checker and relation,
`RecursiveLocalComputation`, and canonical source unions remain textually and
semantically unchanged. The wrapper adds reachability and fixed precedence, not
new accepted expression semantics.

Remain deferred: groups around a conditional or a conditional branch lambda;
nested conditional/call propagation; tuple, return, inferred-let, and typed-body
expected propagation; multiple arguments and global resolution; global catalog,
source closure, runtime inhabitant, world safety, cost theorem, backend guarantee,
principal inference, coercion, and overload policy. Parser and diagnostic proof
work remains paused, including the eight existing untracked pause files.

## Prototype freeze and delivery contract

The production-shaped scratch prototype is fixed at 203 lines with SHA-256
`f072de46a0096a5f0adab1916fc5b4be607e0d320316d0046becd30b372d7d38`.
Its compiled artifact SHA-256 is
`bd24697bc07553fda5d85bf28b8f6a269cc656dcdd7b99ff0402810edd5e64cc`.
It has exactly 9 authored roots and 17 owned declarations: 17 public, 0 private.
All are safe and total, with no generated partial helper or public generated
leak, and their axiom closure is exactly within `propext`, `Classical.choice`,
and `Quot.sound`. Port the source with only its module comment adjusted, then
freeze production ownership again.

Keep the production module and both consumers strictly below 300 lines and each
commit at no more than 300 changed lines. Use six commits: decision, production,
symbolic consumer, parsed consumer, umbrella/test registration, then
`CURRENT_STATUS`/`FEATURE_MATRIX`/`M2_PLAN` documentation.

Before closure, verify exact module ownership and all generated names; safe and
total flags; public-root and all-owned axiom closure; masked forbidden-source and
line-limit scans; exact branch and recognized-failure probes; direct, focused,
umbrella, and aggregate builds; the direct parsed runner and full test suite;
registration counts; git-range preservation of ADR-0317 through ADR-0324; the
eight paused parser/diagnostic files; and source/olean drift plus dependency
closure. Do not record a final implementation commit hash in this decision.
