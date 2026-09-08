# ADR-0166: Local-expression cost invariance and same-fuel input extension

- Status: Accepted
- Decision date: 2026-09-08
- Scope: proof-only preservation of independent source costs and checked observations

## Decision

Lift the existing injective local-ID relabeling and unused-name input-insertion
laws to ADR-0165's independent source evaluation costs. Preserve the exact
source AST, result value, initial and final stores, and cost in both directions.
The raw cost laws require no whole-expression resolution or typing: skipped
unresolved branches and selected untyped short-circuit right values retain
their existing semantics.

ID relabeling changes the name table and runtime identity labels together and
requires an injective map. Source spellings and runtime values do not change.
Fresh input insertion requires `AvoidsLocalName` for every written child,
including unselected children; every literal payload avoids names even when
it has no Word meaning. Freshness of a new ID alone does not prevent an equal
spelling from shadowing an old binding.

Prove these laws by preserving cost derivations structurally. Equality of
erased evaluations and separate existence of costs is insufficient to identify
the costs. At identifier leaves, reuse the existing raw-evaluation preservation
laws to recover the needed independent lookup premises, without duplicating
private allocation or freshness proofs.

## Same-fuel executable observations

Use the new source-cost laws, existing source-type preservation, and exact
fuel thresholds to strengthen unused input insertion: at the same fuel,
completed bundled runs have exactly the same type, value, and final store in
both directions. Whole-check failure continues to be preserved.

Provide a reusable typed-cost characterization of present fuel exhaustion:
whole source typing and an independent successful cost greater than the fuel
are equivalent to existence of a suspended bundled result with that type.
Then prove exhaustion presence is preserved at the same fuel under unused
input insertion. Quantify the old and new suspended states separately.

Do not claim equality of suspended states after insertion. Core free indices
and runtime environments shift; already at fuel zero, the retained initial
states can differ even for a literal. The existing injective-ID bundle law
already preserves complete same-fuel results and suspended states, so do not
duplicate that executable theorem. The new ID result concerns raw source costs.

## Validation and exclusions

Consumers cover injective relabeling, valid and invalid literal nodes,
conditional and short-circuit cost differences, strict bitwise operands,
raw skipped unresolved branches, whole-check rejection, and exact fixed-fuel
done/exhaustion observations on nonempty stores. Include a same-spelling fresh
insertion that preserves the final Boolean value but changes the cost, showing
why the unused-name premise is essential. Include unequal suspended states
with equal exhaustion presence to protect the weaker observation boundary.

Audit public declarations against standard kernel axioms; run focused and
aggregate builds, complete tests, kernel and metadata checks. Keep new proof
files below 300 lines. No allocation algorithm, source rule, parser, evaluator,
gas or elapsed-time model, wire format, Oracle endpoint, or golden bytes change.
