# ADR-0197: Terminal-body identity and store invariance

- Status: Accepted
- Decision date: 2026-09-08
- Scope: acyclic body-level laws needed before runtime-entry integration

## Decision

Lift injective local-identity relabeling and store replay through singleton,
conditional and common terminal return-body profiles. Identity relabeling keeps
the same source, exact elaborated Core, return type and ordered runtime values.
Prove exact independent-elaboration transport, whole optional checker equality
and full same-fuel runner equality, including rejection and suspended states.
Retain global injectivity; do not claim that merging distinct IDs preserves
lookup, typing or execution.

Raw and exact-cost evaluation can replay at any replacement store with the
same value and cost. Characterize evaluation at arbitrary initial/final stores
by equality of those stores plus replay at the chosen replacement. Completed
runner observations retain the same value/type/cost but each carries its own
initial store. Fuel-exhaustion presence is equivalent at the same fuel; do not
identify suspended states or complete results across different stores.

Move the existing `ReturnBodyElaborates.mapIds` declaration unchanged from the
runtime-owner module into a body-level renaming module. Likewise move existing
`ReturnBodyEvaluates.change_store` and `ReturnBodyEvaluatesWithCost.change_store`
unchanged from the runtime-store module into a body-level store module. Preserve
all three public names and statements, and preserve availability through their
old imports by importing the new modules there. New body modules must not import
runtime-entry, owner, compilation or observation modules. This avoids a cycle
when a future runtime-entry profile depends on terminal body invariance.

## Boundaries

No checker acceptance, syntax shape, primitive semantics, cost, fuel bound,
type-only/actual-input factorization or runtime-function entry behavior changes.
The conditional arms remain singleton returns; whole checking still covers
invalid unselected arms. General input insertion/shadowing, noninjective maps,
store effects, closure invocation and entry integration remain separate.

## Validation

Independent and parsed consumers retain actual arguments, nontrivial identity
maps and nonempty differing stores. Cover singleton and conditional forms,
selected values and unequal costs, exact same-fuel mapped checkpoints, replay
completion/exhaustion, checker failure, and the distinction between preserved
observations and store-dependent full states. Confirm old owner/store APIs are
still available with their original contracts. Include a noninjective lookup
counterexample rather than silently weakening the injectivity requirement.

Audit relocated declarations and all new public APIs for standard axioms only.
Run focused and aggregate builds, full tests, dependency-cycle, kernel,
forbidden-token and whitespace checks. Keep files below 300 lines and commits
small, preserve paused diagnostic files and use repository-local scratch.
