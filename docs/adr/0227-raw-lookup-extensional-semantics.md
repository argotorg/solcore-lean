# ADR-0227: Raw lookup-extensional semantics

## Status

Accepted for implementation.

## Context

ADR-0226 preserves raw recursive results under globally injective owner-only
relabeling. Its exact fresh-ID transport requires fixed binder indices. That
allocator restriction does not itself imply a restriction on observable raw
values or transition costs: raw expressions see names through two first-match
lookups, not through the identity or position of the intermediate key.

## Decision

Prove direct expression and recursive-body equality under the explicit premise
that every spelling has the same composed optional actual-value lookup:

`(leftTable.lookup? name).bind leftEnvironment.lookup? =`
`(rightTable.lookup? name).bind rightEnvironment.lookup?`.

The direct expression theorem preserves its entire Option of value and cost.
The recursive theorem allows independently chosen owners and preserves the
entire Option, including absence. Costed and uncosted raw iff laws retain the
same initial and final stores as separate quantified arguments.

No new evaluator, lookup policy or relation definition is needed. Keep the
expression proof and recursive proof in separate acyclic frontend modules.
Existing raw/checked/entry APIs remain unchanged. Use original syntax-size
recursion, and existing raw evaluator correspondence for the relational laws.

For each let, evaluate its initializer in the old scope and use its actual
value on both sides. Each side independently allocates an ID fresh relative
to its own name table. First-match lookup then implements the same name update
on both sides. An environment-only row may collide with this fresh ID; no old
name can refer to it. Selected arms keep their original input scopes.

## Boundaries

The premise is equality for every spelling, not equality of tables, individual
lookup IDs, row order, scope length or Core environment layout. It allows
duplicate names or IDs, missing environment values, sparse mixed owners,
unaligned rows and untyped opaque values. No injection, surjection, inverse,
whole checking, name freshness, runtime typing or store typing is assumed.

Name absence and a name whose first ID has no value may be indistinguishable.
Different fresh IDs and index-changing injective maps may preserve raw results
without commuting with allocation. A genuinely changed visible first match can
change results. The premise must therefore concern actual composed lookup.

Raw selected success still does not establish whole acceptance. The new laws
do not preserve static type tables, exact fresh IDs, internal tables, compiled
Core syntax, arbitrary continuations or checkpoint payloads. Checked execution
may only be consumed with separate accepted provenance and matching IDs.

## Validation

Independent source proofs and complete parsed-source consumers must exercise
depth, asymmetric costs, different owners and layouts, missing-versus-unbound
names, shadowing, fresh environment collisions, opaque values, genuine absence
and raw/whole contrasts. Include allocator-noncommuting equal-result examples
and unequal-visible-value counterexamples, without claiming checkpoint equality.
Run focused and aggregate builds, full tests, public and consumer axiom audits,
kernel-policy and whitespace checks and independent reviews. Keep proof files
below 300 lines, commits small and publication separate from implementation.
