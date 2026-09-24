# ADR-0276: shared computation body owner covariance

## Status

Accepted; additive proof integration. Canonical Rust remains fixed at
`18fd9f75d290df0070e21ee56e0a5691f232596f`. No executable or source admission
decision changes; this unit transports the existing shared body judgments.

## Context

ADR-0275 established exact recursive-child meaning and checking under arbitrary
injective local-ID maps. Shared bodies additionally allocate fresh IDs for
typed and inferred lets. An arbitrary binder-index transformation need not
commute with that allocator, so the child result alone is insufficient.

The existing owner-only map retains binder indices, and the fresh allocator
filters by owner before choosing its index. Its existing injective-owner
commutation holds even with sparse indices and interleaved foreign owners.
`LocalTypeInputs` already carries its own distinct-ID invariant; no new
runtime inhabitants, alignment or additional row-uniqueness premise is needed.

The shared body exposes independent typing, exact elaboration and executable
checking, each with a fixed child interface. Every branch is checked, including
unselected branches and an optional match default. Scope protection is based
on spelling lists, not the declaration identities being transported.

## Decision

Add one generic proof module, `ComputationReturnTreeOwnerProperties`, with
exactly three public laws:

- `computationReturnTreeElaborates_mapOwner_iff`;
- `computationReturnTreeHasType_mapOwner_iff`;
- `elaborateComputationReturnTree?_mapOwner`.

Use an arbitrary globally injective declaration-owner map, the existing
`ownerLocalIdMap`, and the existing mapped `LocalTypeInputs`. Keep the same
type-name table, original block, all source spans, positional Core and result
type. The caller supplies covariance for the same fixed child interface.
The typing theorem uses only independent child typing covariance; it does not
assume a checker graph or the existence of an elaboration.

Prove both semantic iff laws directly by induction on their independent
judgments. In reflection retain an explicit original-input preimage in the
induction motive. Under a let, existing `bindFresh_mapOwner` transports that
preimage to the tail. No inverse function, surjectivity, reconstructed values
or fresh-ID side condition is introduced.

Transport condition protection through the unchanged spelling list. Preserve
both conditional branches, all ordered match entries, pattern classification,
compatibility, optional default and the original lowering fold literally.
Typed annotations retain the same first-match structural meaning.

Derive complete optional checker equality from its supplied complete child
checker covariance, using a private checker graph only as an operational
proof device. This law does not require child correctness or claim independent
source meaning for an arbitrary checker. Both success and rejection remain
unchanged. Concrete recursive-child instantiation belongs in consumers, not
the generic module's import dependency.

## Consumers and verification

Use new independent symbolic and original parsed consumers. Exercise typed
and inferred repeated-name lets, old-input initializers, scoped and exposed
conditional boundaries, discard sequencing, ordered match branches and default,
arbitrary types and nesting, sparse/interleaved owner IDs and a non-surjective
owner shift. Preserve the original independent body evidence and exact Core.

Where execution is observed, use the actual values/captures/stores and
independently justified original Core paths; literal Core equality and unchanged
environment values then transport complete fuel/checkpoint/fault records.
Do not infer raw body owner covariance or runtime safety from this static unit.
Include whole rejection and the fresh-allocation limitation of arbitrary
binder-index maps. Keep malformed actual values separate from static evidence.

Require focused and aggregate builds, full tests, and kernel-policy and whitespace
checks, exact old-contract/import/catalog audits, standard-only public and
consumer axioms, and independent reviews. Each new proof/consumer file remains
under 300 lines; decision, proof, consumers and publication use small commits.

## Non-goals

No source grammar/parser/diagnostic changes, nominal declaration renaming,
type-table change, general binder-index map, raw body/cost equivalence, function
header/entry owner transport, runtime-world construction, new source lambda,
global resolution, or changes to old definitions, signatures and consumers.
