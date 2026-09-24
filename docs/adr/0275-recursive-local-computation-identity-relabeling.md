# ADR-0275: Exact identity relabeling of recursive local computations

- Status: Accepted for implementation
- Decision date: 2026-09-10
- Scope: Additive static and raw proof laws for the existing recursive child

## Why the child boundary comes first

The shared body/function layers do not yet expose owner covariance for their
recursive children. The older pure expression and fresh-name body adapters
already have identity/owner laws, but RecursiveLocalComputation lacks them.
A fixed arbitrary child checker alone does not justify relabeling: it may
inspect the literal local identities. Unlike type-table transport, its missing
equivariance cannot be removed by choosing the checker's success graph.

First prove the concrete recursive child's own identity laws. Its source
expression profile introduces no named binder or fresh LocalId allocator.
An arbitrary injective LocalId map can therefore change owners and binder
indices, including a non-surjective shift, while preserving original spelling,
source AST/ranges and positional Core. This is not a claim that such a map
commutes with the body layer's fresh allocator.

No new Rust/source interpretation, runtime policy, syntax or executable
definition is chosen. Preserve the existing recursive fourteen and shared
twelve/entry four contracts and all old proof bodies and consumers.

## Independent static evidence and complete checking

Publish recursiveLocalComputationElaborates_mapIds_iff and
recursiveLocalComputationHasType_mapIds_iff. Simultaneously map original local
name and context identities with existing mapIds; retain row order, duplicate
spellings/IDs, every source child, the same Core and result type. No runtime
inhabitants, global well-formedness, scope uniqueness or surjectivity are needed.

Prove independent elaboration in both directions by induction on evidence.
For the pure constructor, use original-resolution relabeling/reflection and
Resolved lowering/typing relabeling. Recover the original resolved expression
from the existing existential reflection law, not an invented inverse map.
The independent HasType iff may reuse its existing elaboration-existence iff
after independent elaboration transport has been proved. Overlapping pure and
recursive constructors are preserved by their own rules; do not assume their
source shapes are disjoint.

Publish elaborateRecursiveLocalComputation?_mapIds for exact whole Option
equality, including rejection. Derive it from the independent elaboration iff
and existing checker correspondence. Keep every original static branch,
including skipped lazy/conditional children. No repeated size-recursion through
the checker, new checked judgment or success-only substitute is required.

## Raw evaluation and exact costs remain independent

Publish recursiveLocalComputationEvaluatesWithCost_mapIds_iff, simultaneously
mapping local-name and actual-environment identities. Prove both directions by
raw-cost induction. Pure children use their existing raw-cost relabeling iff;
application retains the actual closure body, captured values, argument and
the very same Core path. Every constructor retains its original intermediate
and final stores, operator interpretation and exact cost.

Publish recursiveLocalComputationEvaluates_mapIds_iff through the existing
raw-evaluation / cost-existence correspondence. Neither law needs checking,
typing, name uniqueness, ID alignment, runtime-world evidence or a bound on
arbitrary closure execution. Preserve selected non-Bool lazy RHS values and
raw success that skips unsupported or unresolved source. Absence of successful
raw evaluation is reflected, but this alone is not a fault-classification or
termination theorem.

Use two proof files: RecursiveLocalComputationRenamingProperties (three static
laws) and RecursiveLocalComputationEvaluationRenamingProperties (two raw laws).
Keep the public surface to these five iff/equality laws; forward-only, owner-only
and runner wrappers are not needed in this unit.

## Independent consumers and next boundary

Symbolic and original parsed consumers must exercise all five laws: arbitrary
nominal types without fabricated values, arbitrary recursive depth and mixed
operators/tuples/conditionals/calls; sparse foreign IDs and duplicate spellings;
non-surjective maps that change indices; actual closures, captures and ordered
allocation/write/read effects. Establish original evidence, literal Core paths
and exact costs separately before comparing mapped results or saved states.
Same actual values and stores plus unchanged Core give same-fuel execution
results and genuine checkpoint/resumption comparisons without a new runner.

Retain explicit non-injective collapse counterexamples: first-match type or
runtime lookup and positional Core can change. Demonstrate whole rejection
despite selected raw success, and raw success absence separately. Do not claim
general index changes preserve fresh body allocation, or rename captured Core
positions, cell locations, values, source spellings or type-name tables.

After this child foundation, shared-body owner-only covariance can use the
existing owner map and fresh-binding commutation; that integration is separate.
Keep proof files below 300 lines and commits small. Review decision, independent
proofs, consumers and publication separately; run focused/aggregate/full tests,
exact public/consumer standard-axiom catalogs, and old-contract, import,
kernel-policy, EOF, whitespace, and hash audits. Diagnostics remain paused and all scratch
stays in the repository.
