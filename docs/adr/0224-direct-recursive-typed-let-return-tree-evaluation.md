# ADR-0224: Direct recursive typed-let return-tree evaluation

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Execute the existing raw recursive body semantics on original syntax

## Decision

Compose ADR-0223's direct local-expression evaluator into a total evaluator of
the existing `TypedLetReturnTreeEvaluatesWithCost` grammar. Its inputs are the
original `Syntax.Block`, explicit owner and name table, and actual environment;
its output is `Option (Core.Value × Nat)`. Recursion decreases syntax size.
It does not resolve, check, lower, or run Core, and does not accept a store.

A singleton bare return yields Unit at cost one. A singleton expression return
keeps the expression's computed value and cost. An annotated, initialized head
let strictly evaluates its initializer in the old scope, computes the existing
`freshLocalId owner (table.map Prod.snd)`, and prepends this identity and the
actual obtained value to the two tables before evaluating the remaining body.
The initializer and tail costs add two existing Core transitions. Even unused
initializers must succeed and contribute their full cost.

A singleton explicit if/else evaluates its condition to an actual Bool, then
evaluates only the selected arm in the same input scope. Their costs also add
two. Other shapes return `none`: omitted annotations or initializers, absent
else, empty bodies, and statements after return or terminal if are not silently
discarded. Expression support and primitive behavior are exactly ADR-0223's.

This executable follows raw semantics, not whole typing. Annotation presence is
required, but its meaning, agreement with the initializer type, and name freshness
are not raw premises. Repeated names, arbitrary sparse/mixed-owner rows and
untyped actual values remain allowed. Fresh allocation uses the name table,
not environment length or IDs; an extra unaligned environment row can have the
same ID, and the new head must still win first-match lookup. Siblings do not
thread allocation through one another. Opaque supplied values are only forwarded.
Selected raw success may coexist with whole rejection, including an unknown
annotation or invalid unselected arm. No source acceptance policy follows.

## Proof boundary

Construct independent raw cost evidence from successful output and prove the
converse by induction on the existing evidence. Publish exact unchanged-store
iff, general final-store iff retaining `finalStore = initialStore`, absence iff,
and cost-existence/uncosted-value projection laws. Reuse expression soundness and
completeness; never use checked Core as the raw proof oracle.

Whole checking and actual ID alignment separately connect computed results to
exact Core paths and fuel thresholds. Completed checked runs reflect computed
value and cost without runtime typing; typed aligned actual environments supply
successful typed results. Bundled runner laws retain whole source typing. A
retained-continuation endpoint does not assert completion after its frames run.
Existing bounds, store replay and checkpoint/resumption theorems can consume the
new raw evidence without duplicate APIs or changes to function entry.

## Validation and exclusions

Use independent arbitrary-depth source proofs and completely parsed recursive
fixtures with independently specified Core, values and costs. Exercise strict
noncommutative/unused initializers, old-scope and actual fresh identities, both
branches, raw/whole contrasts, opaque values, duplicate or unaligned rows, every
fuel boundary and real checkpoint resumption under distinct stores.
No changes to existing body/checker/entry definitions, public contracts, parser,
Core, Resolved or Wire; no calls, mutation, runtime allocation or general returns.
Keep definition/proof/consumer/publication commits separate and small, proof
files below 300 lines, and public/consumer axiom and dependency audits explicit.
Run focused/aggregate builds, actual parsed tests, full tests, the kernel-policy
check, and whitespace checks. Diagnostics stay paused and scratch stays in the
workspace.
