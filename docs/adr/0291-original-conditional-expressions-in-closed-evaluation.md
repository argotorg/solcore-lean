# ADR-0291: original conditional expressions in closed source evaluation

## Status

Accepted after ADR-0290 was fully verified and published.
Implementation follows the independently reviewed scope and signatures below.
Canonical Rust remains fixed at
`18fd9f75d290df0070e21ee56e0a5691f232596f`.

## Motivation

The closed evaluator can create, return and call source closures, but it cannot
evaluate an original conditional expression that selects a closure. Extend this
same executable semantics so conditionals compose recursively with calls, tuples,
initializers and original bodies. Do not copy the complete expression/body family
into another permanent profile just to add one syntax constructor.

## Deliberate existing-definition extension

After ADR-0290 is complete, extend ClosedSourceExpressionEvaluates with two rules:
conditionalTrue and conditionalFalse. Preserve the names and exact types of every
existing constructor, ordinary public theorem and evaluator function. The generated
mutual recursors necessarily gain cases; update explicit dependent inductions rather
than weakening their motives or replacing independent proofs with evaluator premises.

This phase deliberately changes a small allowlist of existing frontend sources.
The prior phase's whole-file byte freeze applies until that phase is complete.
For this extension, keep all other old source bytes and all published theorem
headers unchanged; record and independently review every allowlisted proof-body
edit. Existing selector, source-shape, open-body, Core and Resolved definitions
remain unchanged. No old consumer theorem is removed or weakened.

Adding supported successful paths intentionally changes some former none results.
Do not claim all-input equality with the old evaluator or universal absence
preservation. Existing successful regression fixtures must retain their exact
actual endpoints. A formal cross-version conservativity theorem is not supplied
merely by compiling the old theorem signatures; do not present it as proved.

## Exact original conditional rules

For original source ⟨span, .conditional condition question thenBranch colon elseBranch⟩,
evaluate the original condition under the current owner, literal name/capture rows
and initial raw store. Require the actual result to be Bool true or Bool false.
Evaluate only the corresponding original branch, starting at the condition's actual
final store under exactly the same owner and lexical rows. Return that branch's
actual RuntimeValue and store without projecting or checking its type.

Retain span, question and colon independently. Do not rewrite the expression to a
body if, normalize either branch, require a body scope, or inspect an unselected
branch. The selected value may be any mixed value, including a newly created source
closure with all captured rows. Non-Bool guards have no successful rule.
These two constructors bring the expression family from eight to ten forms;
the nine body constructors remain exactly as they are.

## Executable and proof changes

Add one conditional branch to evaluateClosedSourceExpression? at successor depth.
The guard and selected branch each receive the same predecessor depth; explicitly
thread the guard's actual store. Budget zero remains none. Body clauses and their
existing depth policy are unchanged, but bodies can gain successes through the new
expression children. No runtime error, cost, checkpoint or type layer is added.

Extend the unconditional joint expression/body determinism proof: guard uniqueness
excludes opposite Bool rules, and selected-branch uniqueness fixes the endpoint.
Preserve the existing exact open-body/unary-call compatibility statements.
Update private simultaneous soundness and joint eventual completeness for the two
new constructors, using one plus the maximum guard/selected-branch threshold.
Extend the successful-store invariance consumer with the two transitivity cases.

## Settled implementation scope

The only existing implementation/test sources that may change are:

- `Solcore/Frontend/ClosedSourceEvaluation.lean`
- `Solcore/Frontend/ClosedSourceEvaluationCompatibility.lean`
- `Solcore/Frontend/ClosedSourceEvaluationProperties.lean`
- `Solcore/Frontend/ClosedSourceEvaluator.lean`
- `Solcore/Frontend/ClosedSourceEvaluatorSoundnessProperties.lean`
- `Solcore/Frontend/ClosedSourceEvaluatorCompletenessProperties.lean`
- `Solcore/Test/FrontendClosedSourceBoundaryProperties.lean`

The first six receive exactly the definition/proof extensions above; the last
receives only two additional successful-store induction cases. The fourteen
ordinary public headers of ADR-0289/0290 and all seventeen original constructor
clauses remain literal. All old consumer headers remain unchanged. Generated
mutual recursors, recOn and casesOn gain the two necessary cases; their generated
types are expressly outside the header-freeze promise.
All other old implementation/test bytes remain unchanged. Normal umbrella, Main
and progress-document publication changes are a separately reviewed scope.

Add only `Solcore/Frontend/ClosedSourceConditionalProperties.lean` to the production
module surface. Its two ordinary public declarations have these exact headers:

```lean
theorem closedSourceExpressionEvaluates_conditional_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore finalStore : List RuntimeValue}
    {span question colon : Syntax.SourceSpan}
    {condition thenBranch elseBranch : Syntax.Expr} {value : RuntimeValue} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .conditional condition question thenBranch colon elseBranch⟩ value finalStore ↔
    ∃ (choice : Bool) (middleStore : List RuntimeValue),
      ClosedSourceExpressionEvaluates owner names captured initialStore
        condition (.bool choice) middleStore ∧
      ClosedSourceExpressionEvaluates owner names captured middleStore
        (if choice then thenBranch else elseBranch) value finalStore

theorem evaluateClosedSourceExpression?_conditional
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    (span question colon : Syntax.SourceSpan)
    (condition thenBranch elseBranch : Syntax.Expr) :
    evaluateClosedSourceExpression? (budget + 1) owner names captured initialStore
      ⟨span, .conditional condition question thenBranch colon elseBranch⟩ =
    (do
      let (.bool choice, middleStore) ←
        evaluateClosedSourceExpression? budget owner names captured initialStore condition | none
      evaluateClosedSourceExpression? budget owner names captured middleStore
        (if choice then thenBranch else elseBranch))
```

Keep all proof files below 300 lines. No additional exported helper or permanent
duplicate expression/body family is introduced. The frozen pre-extension contract
inventory records the fourteen ordinary headers, seventeen constructors and the
eight headers of the one allowlisted old consumer. All seven other existing closed
consumers, including the parsed evaluator test, are expected to rebuild unchanged.

## Canonical evidence and boundaries

At the fixed pin, hir-ty/src/infer/expr.rs:174-194 constrains the condition to Bool
and checks/unifies both branch types. yul/src/translate/lower.rs:376-400 places
branch computations inside the emitted conditional switch after condition work.
This supports selected-branch runtime order, not a proof of raw/core equivalence.
The raw semantics intentionally does not implement the compiler's both-branch
type checking, overload resolution, Bool representation correspondence or staging.
No canonical acceptance, total termination or whole-language safety follows.

## Required consumers and validation

Independently construct original conditional proofs before using completeness;
obtain executable actual results before consuming soundness. Cover both choices
on the same original source, an arbitrary unselected unsupported branch, original
marker spans, selected source closures, callee/argument/nested-body positions,
capture-before-shadow behavior and fresh IDs under a different saved owner.

Use actual parsed conditional selection followed by a unary call, with mixed
source/Core/host payloads and literal raw stores. Check zero/threshold budgets,
non-Bool guards and preservation of all pre-extension successful fixtures.
Run focused/aggregate/full tests, all public/consumer standard-only axiom audits,
old-header and allowlisted-diff audits, independent reviews, kernel checks,
and small commits. Keep diagnostics/parser proof work paused.
