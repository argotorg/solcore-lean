# ADR-0277: shared raw computation owner covariance

## Status

Accepted; additive raw-semantics proofs. Canonical Rust remains fixed at
`18fd9f75d290df0070e21ee56e0a5691f232596f`. No executable definition, grammar
or source admission decision changes.

## Context

ADR-0275 preserves recursive-child raw evaluation and exact costs under
injective local-ID maps. ADR-0276 separately transports shared-body typing,
elaboration and checking under owner-only maps. Neither result is a shared
raw-body owner theorem.

Raw bodies take two independent ordered tables rather than `LocalTypeInputs`.
Names, IDs and environment rows may repeat, and the two tables need not align.
Fresh IDs are computed from the name table alone. An environment-only row may
already use the chosen fresh ID; the new binding is still prepended literally,
without deleting or repairing old rows.

Raw typed lets do not interpret their annotations. A conditional or match
evaluates only its chosen body; unselected annotations, scope guards and global
coverage are not additional raw premises. These boundaries must not disappear
when owner transport is proved.

## Decision

Add the generic module `ComputationReturnTreeRawOwnerProperties`, exporting
only:

- `computationReturnTreeEvaluates_mapOwner_iff`;
- `computationReturnTreeEvaluatesWithCost_mapOwner_iff`.

Map declaration owners injectively and retain binder indices using the existing
`ownerLocalIdMap`. Simultaneously map every ID in the original name table and
environment, preserving row order, names and every literal actual value.
Keep the original source block/ranges, initial and final stores, result value
and, for the cost relation, exact cost.

Each theorem assumes covariance of its own same fixed raw child relation,
quantified over arbitrary original tables, environments, stores and source.
Prove both directions by independent induction on that body's judgment.
Do not derive the uncosted theorem through a cost-existence bridge: the generic
child evaluation and child cost interfaces have no such imposed relation.

In reflection keep explicit original preimages for the name table and the
environment separately. Under typed/inferred lets, commute fresh allocation
through the mapped name table and prepend the same actual bound value to the
mapped environment. Reuse the existing injective-owner fresh lemma; do not
introduce an inverse, surjectivity or a fresh-in-environment hypothesis.

Strict initializers and discarded expressions retain their complete store
transitions and costs. Preserve the same selected conditional arm and the exact
`WordMatchChooses` evidence, including actual scrutinee value, source case
order, optional default, selected body and visited comparison count. Wildcards
do not add another comparison or avoid evaluating the scrutinee.

Keep the module independent of child implementations, checking, typing and
older direct evaluators. Concrete recursive-child instantiation belongs in
consumers via ADR-0275, not in the production module's dependency graph.

## Consumers and verification

Use independent symbolic and original parsed raw evidence, including arbitrary
nesting, repeated typed/inferred lets, discards, conditionals and ordered
literal/wildcard/default selection. Exercise actual closure captures and ordered
allocation/write/read with explicit original costs.

Include duplicate, missing, reordered and environment-only fresh-ID rows
without silently aligning them. Check first-match selection, unselected unknown
annotations or syntax and exposed then-shadowing as raw/checking distinctions.
Include absence reflection and the necessity of the supplied child covariance.

Only separately elaborated/aligned examples may use the existing source-to-Core
correspondence. For them compare independent original literal Core paths, exact
fuel thresholds, full saved states and resumption using the same actual values.
Arbitrary raw rows must not acquire a positional-Core or runtime-world claim.

Require focused and aggregate builds, full tests, standard-only exact public
and consumer axiom catalogs, old-contract/import audits, kernel-policy, EOF, and
whitespace checks, and independent reviews. Keep each new proof/consumer file
under 300 lines, and decision, proof, consumers and publication in small commits.

## Non-goals

No raw evaluator, termination result, fault classification from absence, runtime
safety, reconstructed world, typing/checking premise, general binder-index map,
nominal/type-table renaming, function/header owner transport, parser/diagnostic
work, new source feature, or change to old definitions/contracts/consumers.
