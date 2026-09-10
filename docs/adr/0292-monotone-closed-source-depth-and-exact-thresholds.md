# ADR-0292: monotone successful depth and exact finite thresholds

## Status

Accepted after completed ADR-0291 publication at
1de3fafbcad2a902ab821d84fae2a93dad8a2a18. Its durable final audit is
.lake/trace-audits/ADR0291FinalAudit.json (SHA256
b8a49c4f9a140fefacbd40bf16bc6dd540a3aeabfb807265d2bb4f71576503b9).
Adopted after two independent design reviews; implementation follows this contract.

## Context

The closed original evaluator is sound and eventually complete for every finite
successful derivation. These two facts do not alone state that a result already
found at depth n is retained at every depth m >= n. An eventually stable sequence
may have earlier holes. The existing self-application and unsupported-path
boundaries also mean that no whole-fragment termination claim is available.

The same predecessor is supplied to all recursive children, including the
callee, argument and saved body and the guard and selected original branch.
Depth is not consumed fuel, execution cost, comparison count or a checkpoint.

## Decision

Prove unconditional successful-depth monotonicity for both existing functions.
Keep the owner, all lexical rows, actual initial store, original source and the
entire returned value/final store literal. The only premises are n <= m and
the actual computed Some result at n. No typing, scope, uniqueness, closedness,
store/world invariant, child callback law or finite-derivation premise is added.

Use a private simultaneous budget induction over the unchanged evaluator.
Its expression/body motives quantify all inputs, so saved-owner recursive calls
and actual intermediate stores remain covered. Nonrecursive shape decoding and
ordered match selection are independent of the budget and remain unchanged.
Do not derive monotonicity from eventual completeness or endpoint uniqueness.

Derive none-downward laws: an actual None result at m implies None at every
n <= m. The reverse implication is deliberately not provided.

Using the new monotonicity and existing finite-derivation completeness, prove an
exact positive threshold for each finite expression/body derivation:
there exists required > 0 such that the whole Option at every budget is
if required <= budget then some (value, finalStore) else none.
Establish the least successful budget only within the proof by induction on a
known successful budget and a case split on the predecessor's Option result. This is an existential
property, not an executable total minimum finder. A private generic Option lemma
may factor the natural-number minimum argument without adding public helpers.

## Scope and contracts

Add exactly two production proof modules:
- ClosedSourceEvaluatorMonotonicityProperties: expression/body monotonicity and
  expression/body none-downward, four ordinary public theorems.
- ClosedSourceEvaluatorThresholdProperties: expression/body finite exact
  threshold, two ordinary public theorems.

Every existing implementation and consumer stays byte-for-byte unchanged.
In particular, the ten expression rules, nine body rules, evaluator functions,
ordinary public headers, generated recursors, old constructor clauses, selector,
compatibility, determinism, soundness and completeness remain untouched.
Normal publication adds only two umbrella imports, new consumer registrations
and bounded status/plan/matrix paragraphs. Each new proof/consumer is below
300 lines; source/proof commits stay small and independently reviewable.
No new axiom, proof placeholder, unsafe execution or native decision shortcut.

The following six literal headers define the public contract.

```lean
theorem evaluateClosedSourceExpression?_monotone
    {small large : Nat} {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore : List RuntimeValue}
    {source : Syntax.Expr} {value : RuntimeValue} {finalStore : List RuntimeValue}
    (order : small ≤ large)
    (accepted : evaluateClosedSourceExpression? small owner names captured initialStore source =
      some (value, finalStore)) :
    evaluateClosedSourceExpression? large owner names captured initialStore source = some (value, finalStore)

theorem evaluateClosedSourceExpression?_none_of_le
    {small large : Nat} {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore : List RuntimeValue}
    {source : Syntax.Expr}
    (order : small ≤ large)
    (rejected : evaluateClosedSourceExpression? large owner names captured initialStore source = none) :
    evaluateClosedSourceExpression? small owner names captured initialStore source = none

theorem ClosedSourceExpressionEvaluates.exact_depth_threshold
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore finalStore : List RuntimeValue}
    {source : Syntax.Expr} {value : RuntimeValue}
    (evaluated : ClosedSourceExpressionEvaluates owner names captured initialStore source value finalStore) :
    ∃ required : Nat, 0 < required ∧ ∀ budget,
      evaluateClosedSourceExpression? budget owner names captured initialStore source =
        if required ≤ budget then some (value, finalStore) else none

theorem evaluateClosedSourceBody?_monotone
    {small large : Nat} {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore : List RuntimeValue}
    {source : Syntax.Block} {value : RuntimeValue} {finalStore : List RuntimeValue}
    (order : small ≤ large)
    (accepted : evaluateClosedSourceBody? small owner names captured initialStore source =
      some (value, finalStore)) :
    evaluateClosedSourceBody? large owner names captured initialStore source = some (value, finalStore)

theorem evaluateClosedSourceBody?_none_of_le
    {small large : Nat} {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore : List RuntimeValue}
    {source : Syntax.Block}
    (order : small ≤ large)
    (rejected : evaluateClosedSourceBody? large owner names captured initialStore source = none) :
    evaluateClosedSourceBody? small owner names captured initialStore source = none

theorem ClosedSourceBodyEvaluates.exact_depth_threshold
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue} {initialStore finalStore : List RuntimeValue}
    {source : Syntax.Block} {value : RuntimeValue}
    (evaluated : ClosedSourceBodyEvaluates owner names captured initialStore source value finalStore) :
    ∃ required : Nat, 0 < required ∧ ∀ budget,
      evaluateClosedSourceBody? budget owner names captured initialStore source =
        if required ≤ budget then some (value, finalStore) else none
```

## Independent verification

Build original derivations before using completeness or threshold theorems.
Consumers should separately establish concrete successful and rejected budgets,
then use monotonicity/none-downward without rebuilding an expected endpoint
from soundness. Include actual mixed payloads/raw stores, arbitrary shadowing,
different saved/caller owners and original conditional selection.

Use a symbolic unbounded syntax family with an independently computed exact
threshold and an independent original derivation; compare its explicit result
with the general existential theorem without assuming the threshold in a premise.
Parsed consumers should reuse an actual computed endpoint and increase its
budget, checking its literal original closure fields and final store. Include
zero, immediately insufficient depth, a successful depth and larger depths.
None at an insufficient depth is not proof of a fault or global absence.

Freeze final source before independent full-file review, direct compilation and
standard-three-axiom checks. Recheck all old implementation/test bytes, public
and consumer catalogs/import closures, aggregate build and actual full tests.
Preserve the diagnostic/parser worktree and use repo-local scratch only.

## Non-goals

No new syntax, operator resolution, source typing, Core/host dispatch, effects,
total termination, universal source-size bound, source/Core equivalence,
minimal execution cost, persistent evaluator state or failure classifier.
No change to the fixed canonical pin or its interpretation. In particular,
operators are not assigned primitive semantics from their spelling.
