# ADR-0339: Seven-level-grouped-conditional-first local applications

## Status

Accepted; add one nonrecursive source-only wrapper that selects the complete
ADR-0338 result before the complete unchanged ADR-0337 result.

## Context

ADR-0338 is the standalone exact-singleton adapter for an immediate conditional
beneath exactly seven transparent whole-expression groups when at least one
immediate branch is an ungrouped direct computation lambda. ADR-0337 is the
current complete local-application entry: its true branch is the exact ADR-0336
six-group result, and its false branch is the complete unchanged ADR-0335 result
with all older conditional and finite direct-lambda-group precedence.

Every ADR-0338 candidate is false for ADR-0337's ADR-0336 classifier because the
sixth group immediately contains a seventh group rather than a conditional.
ADR-0337 therefore returns the complete ADR-0335 `Option`; on all three new
ADR-0338 success partitions this is literally `none`. On classifier-selected
ADR-0338 semantic failure, that predecessor value is irrelevant and must not be
inspected. Dispatch after a failed checker would make precedence depend on
semantic success instead of the frozen source partition.

Editing ADR-0337, copying its nested dispatch, or introducing recursive group
traversal would reopen frozen behavior. The smallest additive integration is a
two-child wrapper around the complete ADR-0338 and ADR-0337 results. It adds no
new expression, type, Core or runtime semantics.

ADR-0338 completed at HEAD
`552d973e0b3d04730cd2172b9dad857fe4bea469` with tree
`2a8bc68e5b440c88e3b5c158d9e1fc9aa85d1d5c`. Its frozen decision,
production, symbolic-consumer and parsed-consumer SHA-256 values are
`10b0e4a3dfa9f5d94d6afc72af416cde1aa4bcdb87b8bc20833719740c205410`,
`2976d35a47f38f23e8be335cf9cd719d153f44874e08b66a49a34ca5722aaed8`,
`c81b28b28f9574156712b07062faf1923b913d1564e170a6ba0f385e97633ee7` and
`0b675e7fff9d57a76f1a4c048300707edba8e243e2b583db571fe97c8db89f66`.
The zero-issue GREEN completion report is
`.lake/trace-audits/ADR0338CompletionIndependent.json`, SHA-256
`ecf4c8f741701f0a19f7f225d7545628e1bdecfe73bff9a4246de961ee5a2e25`,
and two consecutive full runs used the byte-identical generator SHA-256
`d658d09f318ab6ab021b10c8f24c2729e25c91e10c4a4c50322ea8cc72040a6f`.

## Decision

Add `LocalApplicationWithSevenLevelGroupedConditionalExpectedLambda` as a
separate additive wrapper. Evaluate the unchanged
`isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication` classifier once
on the unchanged original `Syntax.Expr`:

```text
if ADR0338-classifier(source)
then exact ADR0338 Option(source)
else exact ADR0337 Option(source)
```

The true branch returns
`elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?`
literally. The false branch returns
`elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?`
literally. Classification stays source-only: it does not read owner, tables,
resolution, inferred types, diagnostics, checker results or runtime observations.

A classifier-true `none` is final. Do not invoke ADR-0337 after selected failure,
use `Option.orElse`, retry until a checker succeeds, remove or add groups, rebuild
or normalize the source, rewrite spans, or change either child. Conversely, every
classifier-false input preserves the complete ADR-0337 `Option`, both `some` and
`none`, including ADR-0337's ADR-0336-before-ADR-0335 nested precedence.

Add no classifier, combined classifier, path enum, group extractor, recursion,
fuel, termination argument, source reconstruction, source union, runtime node,
generic failure theorem or change to ADR-0337/ADR-0338.

## Declarative and executable interface

Define `LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates`
with exactly two constructors:

1. `sevenLevelGroupedConditional` retains
   `isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source = true`
   and a complete
   `SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates` child;
2. `existing` retains the same classifier equal to `false` and a complete
   `LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates` child.

Expose exactly these eight authored public roots, mechanically isomorphic to the
measured ADR-0337 wrapper API of 8 roots, 15 owned declarations, 15 public and
zero private:

1. `LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates`;
2. `elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?`;
3. `elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_of_sevenLevelGroupedConditional`;
4. `elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_of_existing`;
5. `elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_iff`;
6. `elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_eq_none_iff`;
7. `LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates.core_hasType`;
8. `LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates.provenance`.

Both branch theorems are universal literal complete-`Option` equations. The
success theorem is exact executable/declarative correspondence, and the failure
theorem equates checker `none` with absence of every Core/type relation witness.
Typing delegates directly to the selected complete child. Provenance is the exact
disjunction of the classifier equation plus complete ADR-0338 child provenance,
or the false equation plus complete ADR-0337 wrapper and nested-child provenance.
Do not add a wrapper classifier or `classified` theorem; the unchanged ADR-0338
Boolean and its negation are already the complete partition.

Production imports only the exact ADR-0338 leaf and complete ADR-0337 wrapper and
must be the mechanical ADR-0337 wrapper extension, expected at 151 lines and
strictly below 300. Advance only selected classifier/child and wrapper names.

The independent production prototype is frozen at 151 lines and source SHA-256
`728ae7c25292a1ad4e50bbcebd93fe1b041a594946ca5373db1e7a6dfc072e15`.
It is the exact 62-addition/62-deletion mechanical mapping of ADR-0337 production;
normal, trust-zero, warning-as-error and importable artifacts are byte-identical
at SHA-256 `05a21efa55c32baf264403354d6241e7fcca88e2fb4d51f9087eee5299bbec31`.
Its zero-issue GREEN audit and byte-identical generator SHA-256 values are
`2eb6cae9895eb0456fb790e4d0a1137b7cb30407a6556052f31765060cac223b` and
`1ca22fe3a6786d484a782da3150e3516a7bef79a6f6f612415bcd1c87098d8d9`.

## Independent symbolic consumer

Create
`Solcore/Test/FrontendLocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaProperties.lean`
strictly below 300 lines with exactly three authored public roots. Keep fixtures
and helpers private. Reuse the established sparse table, exact owner, duplicate-
name, Bool, ordinary-function, opaque, wrong and unresolved rows. Port ADR-0338's
frozen planned-dispatch obligations to the real public wrapper and remove the
private planned dispatcher.

The true route covers all three ADR-0338 exact-depth-seven branch partitions:
lambda/ordinary, ordinary/lambda and lambda/lambda. Independently construct the
complete ADR-0338 relation before the wrapper relation. Freeze the classifier,
true-branch equation, literal checker/Core/type, Core typing and complete nested
wrapper/leaf provenance. Also freeze exact ADR-0337 `none` for all three.

Use exactly ten classifier-true selected failures: non-Bool and unresolved
conditions; malformed immediate-lambda header and body; wrong-typed and unresolved
ordinary branches; non-function and unresolved callees; and a direct lambda
opposite a grouped direct lambda or a nested-call lambda. Every row proves exact
ADR-0338 `none`, wrapper equality to that `none`, and no ADR-0337 fallback.

The classifier-false complete-Option matrix has exactly twenty-four shapes:

- conditional depths zero through six and depth eight;
- exact-depth-seven all-ordinary, grouped-only and nested-only branches;
- direct lambdas at depths zero through eight; and
- an ordinary singleton, zero arguments, multiple arguments and a top-level
  non-call.

For every false row prove the whole wrapper result equals the complete ADR-0337
`Option`. Outcomes are exactly eighteen `some` and six `none`: seven shallower
conditionals, exact-seven all-ordinary, nine direct-lambda depths and ordinary
singleton are `some`; depth-eight conditional, grouped-only, nested-only, zero,
multiple and top-level rows are `none`. Construct complete ADR-0337 evidence and
retain wrapper and nested-child provenance wherever evidence exists. Expose the
universal false-branch equation for an arbitrary source.

Also preserve actual `none` for exactly fifteen inherited or boundary examples:
representative selected failures from ADR-0336, ADR-0334, ADR-0332, ADR-0330,
ADR-0328, ADR-0326, ADR-0324, ADR-0323, ADR-0322, ADR-0320 and ADR-0317, followed
by tuple, nested-call, returned-lambda and inferred-let-lambda boundaries.

The exact runtime-selection list has nineteen sources: three new successes, seven
conditional controls at depths zero through six and nine direct-lambda controls
at depths zero through eight. Aggregate the contract into exactly these roots:
`all_three_seven_level_grouped_conditional_partitions_have_exact_semantics`,
`all_selected_and_control_cores_have_exact_fuel_and_store` and
`selected_failures_and_complete_adr0337_options_are_exact` in the isolated
ADR-0339 consumer namespace.

## Independent parsed consumer

Create
`Solcore/Test/FrontendParsedLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda.lean`
strictly below 300 lines with exactly three authored public roots:
`parsed_seven_group_wrapper_static_contract`,
`independently_executed_seven_group_wrapper_core` and
`Tests.adr0339ParsedLocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaTests`.
Require clean lexer/parser diagnostics, EOF, full-file span and proof-producing
structural equality to every hand-built AST; never derive propositional equality
from `BEq`. Replace ADR-0338 planned observations with the public wrapper.

Reuse the three exact true-route texts, led by:

```text
apply((((((((flag ? lam(x){return x;} : ordinary))))))))
```

Its half-open spans are call/full `0..56`, callee/name `0..5`, arguments `5..56`,
group spans `6..55`, `7..54`, `8..53`, `9..52`, `10..51`, `11..50`, `12..49`,
conditional `13..48`, condition/name `13..17`, question `18..19`, lambda
`20..37`, colon `38..39` and ordinary/name `40..48`. Lambda keyword, parameters,
parameter/name, body, return statement and result/name spans are `20..23`,
`23..26`, `24..25`, `26..37`, `27..36` and `34..35`.

For all three prove exact AST, complete ADR-0338 child and wrapper relations,
classifier and branch equation, literal checker/Core/type, Core typing and nested
provenance. The primary Core remains
`apply (var 0) (ifE (var 3) (lambda Word Word (var 0)) (var 4))`.

Mirror all ten selected failures, twenty-four false neighbors and fifteen
inherited actual-none cases. Thus there are exactly thirty-nine complete ADR-0337
preservation rows: eighteen `some` and twenty-one `none`. Every false row proves
literal whole-`Option` equality; every true failure proves selected ADR-0338
`none` final, retaining proof routes rather than runtime equality alone.

Freeze exact predecessor, boundary and direct-lambda control texts and ASTs:

```text
apply(((((((flag ? lam(x){return x;} : ordinary)))))))
apply(((((((((flag ? lam(x){return x;} : ordinary)))))))))
apply((((((((lam(x){return x;}))))))))
```

Their call/full spans are `0..54`, `0..58` and `0..38`. Predecessor group spans
are `6..53`, `7..52`, `8..51`, `9..50`, `10..49`, `11..48`, with conditional
`12..47`. Boundary group spans are `6..57`, `7..56`, `8..55`, `9..54`, `10..53`,
`11..52`, `12..51`, `13..50`, with conditional `14..49`. Direct-lambda group
spans are `6..37`, `7..36`, `8..35`, `9..34`, `10..33`, `11..32`, `12..31`,
with lambda `13..30`.

## Runtime contract

The wrapper returns the selected child Core verbatim and adds no runtime step.
With the exact nonempty opaque/cell/host environment and store, retain
`Core.Evaluates`, `runStateful_evaluation_sound`, determinism and identical store.
Fuel 13 is exactly `outOfFuel`; fuel 14 is `done (Word 7)`. Conditional controls
at depths zero through six retain 13/14; direct-lambda controls at depths zero
through eight retain 10/11. No runtime cost, result or store changes.

## Preserved, deferred and delivery boundaries

ADR-0317 through ADR-0338, every existing classifier, relation, checker and
theorem, ADR-0337's complete nested precedence, `RecursiveLocalComputation`, the
ADR-0324 branch checker, canonical source unions, runtime entries and wire
versions remain textually and semantically unchanged. This adds one wrapper only.

ADR-0340 is the next standalone exact-eight grouped-conditional leaf; its
selecting wrapper remains separate. Nine or more groups, a generic/deeper spine,
grouped branch lambdas, broader expected propagation, source-union integration,
source closures, runtime-world safety, costs and backend guarantees remain
deferred. Frontend semantics remains the active priority. Parser/diagnostic proof
work remains paused; preserve all eight untracked pause files unchanged.

Deliver exactly six commits over exactly nine unique tracked paths: this decision;
`Solcore/Frontend/LocalApplicationWithSevenLevelGroupedConditionalExpectedLambda.lean`;
the two consumer paths above; registrations in `Solcore/Frontend.lean` and
`Tests/Main.lean`; and `docs/CURRENT_STATUS.md`, `docs/FEATURE_MATRIX.md` and
`docs/M2_PLAN.md`.

Keep decision, production and both consumers strictly below 300 lines, and every
commit at no more than 300 changed lines. Use `set_option autoImplicit false`.
Stage exact paths only and create no completion commit. Forbid `sorry`, `admit`,
authored `axiom`, `unsafe`, `native_decide`, `partial`, `noncomputable`, `extern`,
`implemented_by`, `bv_decide` and `termination_by`. Before closure verify exact
8/3/3 roots, production 15/15/0 ownership, safe/total flags, public simp/proof
leaks, axiom closure limited to `propext`, `Classical.choice` and `Quot.sound`,
masked source, exact matrices and spans, selected-failure finality, universal
complete ADR-0337 preservation, normal/trust-zero/warnings/direct/full builds and
tests, runner, registration, six-commit/nine-path scope, dependency and
source/olean parity, kernel checks and unchanged paused files. Do not record a
final ADR-0339 implementation commit hash in this decision.
