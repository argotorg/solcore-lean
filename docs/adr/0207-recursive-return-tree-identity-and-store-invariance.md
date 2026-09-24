# ADR-0207: Recursive return-tree identity and store invariance

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Body-level identity relabeling and store replay, without entry changes

## Decision

Extend the body-level invariance contracts of ADR-0197 to the separate recursive
return-tree adapter of ADR-0204 through ADR-0206. Keep the original source,
ordered children, exact Core, type and positional runtime values unchanged.
The new modules depend only on body/local/Core semantics, not runtime-function
compilation, preparation or parameter allocation. No existing helper moves.

For any globally injective local-identity mapping, transport independent exact
tree elaboration to the mapped name table and context. Prove full optional
checker equality, including rejection, by structural recursion on the original
block. A one-way success transport alone is not enough to preserve failure.
Derive the proof-carrying input checker and full same-fuel runner equalities;
these retain real checkpoint control, environments, frames and store, not merely
completed values. Do not infer injectivity from row count, types or values, and
do not conflate identity relabeling with reordering runtime rows or source names.

Replay raw and costed recursive tree evidence from an arbitrary replacement
store to that same replacement store, with identical value and exact cost.
Induct on the independent selected-path evidence and reuse local-expression and
singleton store replay. No whole checking, runtime typing or identity alignment
premise is required. In particular, an invalid unselected deep subtree does not
prevent raw replay and does not become accepted by the checker.

Characterize original raw/cost evidence by unchanged original store together
with replacement-store replay. At actual typed-input runners, preserve completed
value/type observations at the same fuel, with each result carrying its own
store; relate only the presence of exhaustion between stores. Distinct stores
must not be equated, and their complete run results or suspended states are not
claimed equal. Genuine resumption uses the corresponding actual checkpoint from
ADR-0206, never a reset control or discarded continuation.

The fuel bound is already a function of source alone and needs no new mapping
law. No raw/cost identity-renaming family or new operational policy is needed
for these contracts. Runtime-function entry integration remains separate.

## Boundaries and validation

Add two production modules with four identity and six store contracts. Consumers
use independent arbitrary-depth elaboration/cost evidence and actual parsed
trees, injective maps that genuinely change IDs, exact positional values,
arbitrary and opaque typed payloads, asymmetric selected costs, both stores and
real checkpoints. A noninjective raw-table counterexample distinguishes changed
first-match lookup from the supported relabeling law. Whole rejected deep trees
retain failure even when their raw selected paths replay successfully.

Do not change diagnostics, parsers, Core, Resolved, existing entry policy or
frozen interfaces. Audit public declarations and consumers using only standard
axioms, and run focused/aggregate builds, actual parsed tests, full tests,
dependency-cycle, kernel and whitespace checks. Keep proof files below
300 lines, commits small and scratch files inside the repository.
