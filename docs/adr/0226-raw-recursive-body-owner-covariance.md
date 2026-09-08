# ADR-0226: Owner covariance of raw recursive body evaluation

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Relabel actual raw scopes without assuming whole checking or typing

## Decision

Prove that globally injective relabeling of `Resolved.DeclarationId` owners,
with every local binder index fixed, preserves direct recursive-body results.
Map the evaluator's owner and both original caller tables through the existing
`ownerLocalIdMap`. Keep source syntax, spelling, annotations, spans, actual values
and row order unchanged. Equality includes the full optional value/cost pair,
so absence is preserved as well as success, even for non-surjective owner maps.

The existing static and checked-runner owner contracts do not cover arbitrary
raw caller rows. This layer does: duplicate spellings or IDs, sparse mixed owners,
unaligned environment order and untyped actual values remain valid inputs.
No name freshness, ID uniqueness, environment alignment, runtime/store typing,
annotation meaning, whole resolution or source acceptance premise is added.

Reuse the existing injective-ID expression-cost iff and exact direct-expression
correspondence to obtain a private expression-result lemma. Prove direct body
equality by recursion on original syntax size. Strict initializers yield the
same actual value and cost in the old scope. Existing `freshLocalId_map_owner`
applies to the name table's IDs, preserving the precise freshly extended tail;
environment-only collisions still respect the newly prepended first match.
Both conditional arms start in the same original scope, and only the actual
selected arm is evaluated. No inverse owner map or invented preimage is used.

## Minimal public contracts

Publish three laws: full optional direct-result equality, independent raw-cost
iff with identical value/both stores/cost, and uncosted raw-evaluation iff with
identical value/both stores. Derive the raw laws from ADR-0224's exact general-store
correspondence and cost erasure/existence. Preserve its final-store equality;
the store-free evaluator does not license an unrelated final store.

Do not add duplicate forward-only, absence-only or typed-input wrapper APIs.
Existing checking, direct entry gates, owner runners, Core states and resumption
contracts remain separate and unchanged. Raw selected success still cannot
establish whole acceptance when annotations or unselected children are invalid.

## Boundaries and validation

Global injectivity matters: collapsing two owners with equal binder indices can
merge first-match environment keys and change the value. Include an explicit
counterexample with distinct original values. Arbitrary binder-index shifts
need not commute with fresh allocation, but that allocator counterexample alone
is not a counterexample to raw result invariance; make no stronger claim.

Independent arbitrary-depth source proofs and complete parsed original blocks
must consume all three laws. Use non-surjective owner maps, sparse mixed tables,
duplicate spellings/IDs, actual fresh-ID/environment collisions, selected raw
success despite whole rejection, genuine raw absence and opaque untyped values.
Keep independently specified results/costs and original raw certificates, with
own-store equality explicit. Where checked paths are also exercised, retain
their separate whole-checking and actual-ID premises rather than deriving them
from this raw law. No source syntax or executable policy changes are required.

Keep proof/consumer/publication commits separate and small, proof files below
300 lines, public/consumer axiom and dependency audits explicit. Run focused and
aggregate builds, complete parsed execution, full tests and kernel/metadata/
whitespace checks. Diagnostics remain paused; scratch stays in the workspace.
