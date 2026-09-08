# ADR-0228: Binary pairs in the local Core fragment

## Status

Accepted for implementation.

## Context

Core already has binary products, ordered pair evaluation and exact machine
transitions (ADR-0019). The independent local-fragment insertion proofs used
by frontend lowering currently exclude pair construction. This is a prerequisite
for a later explicit two-element source-tuple adapter, not that adapter itself.

## Decision

Extend `Core.Expr.LocalFragment` with existing `Expr.pair` when both children
belong to the fragment. This extends the initial eight-form boundary to nine
forms without changing Core syntax, types, values, typing, evaluation or machine
semantics. Existing projections remain outside this predicate.

Extend structural weakening, retained-prefix evaluation insertion/reflection,
typing insertion/reflection and paired exact-cost paths with the pair case.
Both children retain the same original environment. Evaluation threads the
initial, intermediate and final stores in left-to-right order. The value is the
existing ordered pair of the actual component values, without a primitive or
runtime-typing condition.

Exact paths use child induction hypotheses with their shared costs selected
before arbitrary outer continuations. Construct each side's own `pairRight`
and `pairApply` frames and saved environments. Pair cost is left cost plus right
cost plus three. Do not obtain two unrelated existential costs by separately
invoking general evaluation correspondence.

Keep existing public theorem names and signatures unchanged. Existing inference,
closed-path iff, zero-cutoff, typing and evaluation corollaries inherit the new
case. Add only the structural predicate constructor to the public boundary.
Preserve the acyclic Core-to-Resolved-to-Frontend dependency direction.

## Boundaries

No typing, inhabitants, well-formed data environment, scope validity, runtime
world, freshness or store-passivity premise is added to the untyped laws.
Typing laws retain their arbitrary unchanged data definitions. Opaque closure,
cell and constructed values may be paired literally, but closure creation/calls,
cell access and other excluded syntax do not become local forms.

All syntactic children must belong, even inside an unselected conditional.
Missing references remain missing after positional insertion. Arbitrary retained
continuations are not executed by the transported endpoint paths. Genuine
checkpoints retain their own frames and environments and need not be equal.

Do not change Resolved constructors, canonical source acceptance, entry gates,
parser, diagnostics or frozen wire interfaces. Two-element source tuples,
nullary or larger tuples, tuple type syntax, projection spelling and multiple
returns are not implemented by this prerequisite. Historical ADRs remain intact.

## Validation

Independent proof and executable boundary consumers must cover nested pairs
and lets, arbitrary retained prefixes and opaque values, exact component order,
missing or wrongly shaped children, nominal static types without inhabitants,
L+R+3 cost, both insertion directions and actual pair checkpoints/resumption.
Retain old lambda/application/cell and wire-rejection counterexamples.
Run focused/aggregate builds, full tests, all-public and consumer axiom audits,
kernel/metadata/whitespace checks and independent reviews. Keep files below
300 lines and definition, proof, consumer and publication commits separate.
