# ADR-0298: original closed short-circuit evaluation

## Status and scope

Accepted design after independent production and consumer review.
Implementation and final aggregate verification remain separate required gates.
Baseline is completed ADR-0297 at `6aefd838e5601e32b5a725e255c9fb10da64f66a`.
Its completion record is `.lake/trace-audits/ADR0297CompletionRoot.json`, SHA256
`4929f8965a0c3bcd82bf4b7ca961aec9b84baf1b90fbb2e1abdc0654a071e45e`; final audit SHA256
`755b035ce69876b44794a70bce67794244e97360d0ddf36a09f762450d4afcb9`.
Canonical Rust remains fixed at 18fd9f75d290df0070e21ee56e0a5691f232596f.
Only fixed-commit `git show` reads are used in the sibling repository.
Diagnostics and parser proofs remain paused.

Adopt original closed logicalAnd/logicalOr evaluation, not an extension of
the recursive data-image gate and not a canonical compiler-correctness claim.
Keep the original AST and every outer/operator/child span.
The actual left result must be a RuntimeValue.bool; there is no truthiness.
Selected right results are unrestricted RuntimeValue values, including complete
saved source closures, Core closures, unit, words, pairs and inert host values.
This raw semantic result does not assert whole-expression Boolean typing.

## Four rules and two runner branches

At arbitrary owner, ordered name table, captured rows and complete input store:

| Rule | Original child evaluations | Whole endpoint |
| --- | --- | --- |
| andTrue | left yields true and middleStore; right runs at middleStore | exact right value/finalStore |
| andFalse | left yields false and finalStore | false/finalStore, no right premise |
| orTrue | left yields true and finalStore | true/finalStore, no right premise |
| orFalse | left yields false and middleStore; right runs at middleStore | exact right value/finalStore |

Skipped constants are constructed directly, irrespective of caller bindings
spelled true or false. Skipped right syntax is not inspected, resolved or checked.
No typing, NoDup, store-validity, projection, callback or termination premise is added.
Owner remains an index of the existing mutual judgments so saved calls can switch
to the actual saved owner, names and captured values.

At budget n+1 the runner evaluates left at n. A non-Bool or unsuccessful left
returns none. A selected right runs at n with the actual left final store;
the result pair is forwarded unchanged. A skipped right has no recursive call.
Budget zero, all old expression branches and the body runner remain unchanged.
None continues to combine exhaustion, unsupported syntax and unsuccessful lookup.

## Preserved contracts and proofs

Change seven existing production files: ClosedSourceEvaluation, ClosedSourceEvaluator,
ClosedSourceEvaluationCompatibility, ClosedSourceEvaluationProperties,
ClosedSourceEvaluatorSoundnessProperties, ClosedSourceEvaluatorCompletenessProperties
and ClosedSourceEvaluatorMonotonicityProperties, all under Solcore/Frontend.
Preserve the sixteen authored public headers in those files literally.
Retain all twelve old expression clauses and nine body clauses in their order.
The expression count becomes sixteen rules, not sixteen distinct syntax forms.

Compatibility adds only four trivial expression cases to the mutual body argument.
Determinism first equates left endpoints, excludes opposite Boolean branches,
and, when selected, equates the complete right endpoints at that same middleStore.
Soundness and monotonicity add binary/operator cases and reject actual non-Bool left
values; selected cases use both child hypotheses, skipped cases only the left one.
Completeness composes selected thresholds with max and skipped thresholds with
the left threshold alone. Old body cases and ordinary public proof boundaries stay.

The legacy FrontendClosedSourceBoundaryProperties consumer requires four new
mutual-recursion cases for store preservation. Preserve its eight public headers
and all other old proof bytes; selected store equalities compose right then left.
This is not a new premise restricting stores in any semantic law.
The generic exact-depth threshold theorems remain unchanged.

Add one production module ClosedSourceShortCircuitProperties with exactly four
public declarations in namespace Solcore.Frontend:

- closedSourceExpressionEvaluates_logicalAnd_iff
- closedSourceExpressionEvaluates_logicalOr_iff
- evaluateClosedSourceExpression?_logicalAnd
- evaluateClosedSourceExpression?_logicalOr

Their full literal contracts and proofs are frozen in
ADR0298ClosedSourceShortCircuitPropertiesPrototypeRoot.lean, SHA256
9d336a9ce707338e41c866e8e2483854d2f98d5f07d9b98a55bc7334ff5c4286.
The iff laws decompose into the exact skip/selected alternatives above, with
actual RuntimeValue and whole final store quantified on both sides. Runner laws
give literal predecessor-budget equations without resolution or Core execution.
Formal adoption changes prototype imports to formal names and removes obsolete
candidate-only comments. Exact reversible transformations and complete sources are
frozen in `.lake/trace-audits/ADR0298FormalPortFreezeRoot.json`, SHA256
`e1487ef86547b74dd17a9e11dd76249a27ad8305171461b0da78725d2317e1cc`.

## Independent consumers and depth

Independent original constructor witnesses must precede iff/soundness conversions.
Cover four Boolean choices, groups/nesting, unrestricted selected values, opaque
nonempty stores, duplicate/conflicting capture tails and mismatched saved/caller owners.
For returned source closures preserve every saved field and the actual creationStore.
For subsequent saved calls use actual calleeStore, argumentStore and body inputs.
Do not rebuild inputs from an expected projected value, or infer typing from success.

Given exact child cutoff functions, prove the complete budget-indexed result:
skip has threshold DL+1; selection has threshold max DL DR+1.
These are minimal thresholds, not merely eventual success bounds. A skipped proof
has no right cutoff premise. Exact cutoff functions already exclude an impossible
zero child threshold; no redundant positivity assumption is needed.
Existing Local/Core transition costs are separate: KL+3 for skip, KL+KR+2 for selection.
No equality between closed search depth and Core transition cost is claimed.

A successful non-Bool left witness excludes all whole-expression endpoints by
inversion and determinism; only then derive none at every budget from soundness.
A missing reference right is independently impossible. Skips still have original
successful witnesses; selected cases exclude every value and every full final store.
An available unit right demonstrates that a selected value need not be Bool.
Whole resolution/checking still inspects both operands and may reject skipped syntax.

Parsed consumers must use returned original ASTs, including groups and all source
ranges, verify zero diagnostics and EOF, and exercise 0, D-1, D and D+3 from an
independently derived bound. Parser correctness and diagnostic proofs are not added.
Freeze literal consumer headers and imports before formal adoption; keep each
source file below 300 lines and symbolic, negative, depth and parsed concerns separate.

## Data-image and verification boundaries

Keep ADR-0297's nine-form ClosedSourceDataExpression and seven-form body gate,
its four private unary proof additions and six public image laws whole-byte exact.
Logical binary expressions remain outside that gate. Existing Local/Resolved/Core
correspondence may be used only with its actual resolution/lowering premises;
this step does not establish a general closed binary data-image bridge.

Preserving authored headers does not preserve generated mutual recursor types:
the four new rules deliberately extend their elimination cases. Enumerate the
actual complete before/after families and compare full stored types, flags, axioms,
module-owned declarations and complete logical closures. Do not infer generated
inventories or normalization rules from a predicted count or a hash-only record.
Retain all unrelated ordered public/consumer catalogs and source/import edges.

Before source adoption freeze exact source/import reversals and authored headers.
Enumerate generated declarations using a count-independent discovery configuration;
before final kernel comparison freeze the actual public/consumer inventories,
affected direct clients and literal name/type rules from those complete captures.
Before completion require focused and direct-client builds, new and retained parsed
regressions, full frontend/syntax/tests builds, full tests, policy/metadata/whitespace
checks, selected public/consumer axiom checks and independently repeated final audits.
Retain bounded failed attempts. Commit exact approved paths in small coherent units.

No Word binary semantics, overload dispatch, staging, mutation, effects, recursion
termination, whole-frontend totality or source/Core closure identity is added.

## Exact consumer registration

All files below are in `Solcore/Test/`; imports point only to production modules.

| File | Public declarations | Purpose |
| --- | ---: | --- |
| FrontendClosedShortCircuitDepthProperties.lean | 4 | Universal skipped/selected child-cutoff composition |
| FrontendClosedShortCircuitNegativeProperties.lean | 4 | Non-Bool left excludes every endpoint and budget |
| FrontendClosedShortCircuitMissingRightProperties.lean | 5 | Independent missing lookup, skip success, selected failure and unit right |
| FrontendClosedShortCircuitSavedCallProperties.lean | 1 | Actual returned closure, foreign caller and fresh parameter shadowing |
| FrontendClosedShortCircuitCostDepthProperties.lean | 4 | Independent depth 2/5 and Core cost 4/8 on the same nested AST |
| FrontendParsedClosedSourceShortCircuit.lean | 1 IO | Returned grouped AST, all cutoffs, separate Core lane; 32 plans / 256 runs |
| FrontendParsedClosedSourceShortCircuitBoundaries.lean | 1 IO | 104 arbitrary-value/missing/returned-closure fixtures |

The last two register `Tests.frontendParsedClosedSourceShortCircuitTests` and
`Tests.frontendParsedClosedSourceShortCircuitBoundaryTests` in the existing test runner.
The boundary fixture certificate stores an expected depth annotation and runs
adjacent-budget checks; it does not itself contain a universal cutoff theorem.
Universal cutoff proofs reside in the depth and main parsed consumers.
The complete public/private header inventories, source text and exact import
reversals for all sixteen ports are in the frozen record above.

## Four literal public law headers

Namespace: `Solcore.Frontend`. Proof bodies are retained from the reviewed candidate.

```lean
theorem closedSourceExpressionEvaluates_logicalAnd_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore finalStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan}
    {left right : Syntax.Expr} {value : RuntimeValue} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ value finalStore ↔
    (value = .bool false ∧
      ClosedSourceExpressionEvaluates owner names captured initialStore
        left (.bool false) finalStore) ∨
    (∃ middleStore,
      ClosedSourceExpressionEvaluates owner names captured initialStore
        left (.bool true) middleStore ∧
      ClosedSourceExpressionEvaluates owner names captured middleStore
        right value finalStore) := by

theorem closedSourceExpressionEvaluates_logicalOr_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore finalStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan}
    {left right : Syntax.Expr} {value : RuntimeValue} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ value finalStore ↔
    (value = .bool true ∧
      ClosedSourceExpressionEvaluates owner names captured initialStore
        left (.bool true) finalStore) ∨
    (∃ middleStore,
      ClosedSourceExpressionEvaluates owner names captured initialStore
        left (.bool false) middleStore ∧
      ClosedSourceExpressionEvaluates owner names captured middleStore
        right value finalStore) := by

theorem evaluateClosedSourceExpression?_logicalAnd
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    (span operatorSpan : Syntax.SourceSpan) (left right : Syntax.Expr) :
    evaluateClosedSourceExpression? (budget + 1) owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalAnd⟩ right⟩ =
    (do
      let (.bool choice, middleStore) ←
        evaluateClosedSourceExpression? budget owner names captured initialStore left | none
      if choice then evaluateClosedSourceExpression? budget owner names captured middleStore right
      else return (.bool false, middleStore)) := by

theorem evaluateClosedSourceExpression?_logicalOr
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    (span operatorSpan : Syntax.SourceSpan) (left right : Syntax.Expr) :
    evaluateClosedSourceExpression? (budget + 1) owner names captured initialStore
      ⟨span, .binary left ⟨operatorSpan, .logicalOr⟩ right⟩ =
    (do
      let (.bool choice, middleStore) ←
        evaluateClosedSourceExpression? budget owner names captured initialStore left | none
      if choice then return (.bool true, middleStore)
      else evaluateClosedSourceExpression? budget owner names captured middleStore right) := by
```
