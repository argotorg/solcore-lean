# ADR-0250: A shared pure-or-application computation child

- Status: Accepted
- Decision date: 2026-09-09
- Scope: A nonrecursive child profile for subsequent mixed-body semantics

## Evidence and decision

The original recursive body uses the pure local-expression profile independently
for let initializers, expression discards, conditions and returned expressions.
ADR-0243/0244 supplies a separate root single-argument application with exact
source provenance and actual effectful evaluation. ADR-0249 adds the positional
insertion laws needed at an application leaf. Repeating a pure/application split
at every body position would duplicate both definitions and correspondence proofs.

Add a small lower-layer `LocalComputation` profile shared by those future body
positions. It is exactly the union of the existing pure expression profile and
the existing root single-argument application profile, not a new recursive
expression language. The checker dispatches an original root call to
`elaborateLocalFunctionApplication?` and any other root to
`elaborateLocalExpression?`. All original syntax, spans, ordered children and
caller tables are passed through unchanged. Failure remains profile rejection.

Keep independent whole `LocalComputationHasType` and exact
`LocalComputationElaborates` relations. Their pure branch retains the original
resolution, positional lowering and resolved type evidence; their application
branch retains the existing exact application evidence. Do not define provenance
as checker success or replace either branch by an arbitrary equally typed Core.
No new Resolved language, source identity, owner, global lookup or type policy is
needed. Both original checkers and their acceptance sets remain unchanged.

Add separate raw and cost relations, each with just pure and application
constructors. They retain the child value, both stores and the child's exact
cost without added transitions. Raw semantics has no checker or typing premise:
unselected children remain unexamined, and an actual closure's tags, captures,
body and stores are those provided by the existing raw application relation.

## Small proof interface

Publish the following common contracts rather than parallel families of aliases:
checker iff exact elaboration; whole typing iff an exact elaboration exists;
elaboration implies open Core typing; raw evaluation iff some cost exists;
costed value/store/cost determinism; exact elaboration gives raw/Core equivalence
under the same source-ID layout; a supplied cost gives uniform continuation
paths; and exact elaboration gives closed Core path equivalence at that cost.

Also lift the three insertion kernels needed for later body induction: arbitrary
context typing equivalence, arbitrary caller raw equivalence, and paired paths
with one cost chosen before the outer continuation. Pure branches reuse the old
local-fragment laws; application branches reuse ADR-0249. Do not duplicate all
derived known-cost, runner, resumption or runtime-world wrappers at this boundary.
Actual runtime typing is not inferred from structural typing or successful raw
evaluation. No source-only cost bound, unchanged-store law or unfuelled total
evaluator can be inherited for the union.

## Integration boundary and validation

This child prepares later support for forms such as `let r=f(x); return r+1;`,
an effectful discarded call, a callable returned into a local binding, or a call
used as a condition. It does not yet implement those whole bodies. Nested calls,
calls inside pure operators and a group surrounding a whole call remain outside
this union. General source-function resolution and source closure construction
also remain separate. Existing bodies, entries, parser, Core, wire and diagnostic
definitions are unchanged. A future mixed recursive body must prove its own
insertion closure, threading actual intermediate stores and respecting the
original named-binder versus hidden-discard scope rules.

Use independent source, parsed-expression and original-function consumers for
both branches, all published kernels and all new constructors. Separate nominal
value-free typing from actual higher-order values. Include effects, selected
versus unselected branches, independent manual costs, unknown names, invalid
stores, insertion and pending-continuation boundaries. Keep proof/test files
below 300 lines and separate decision, definitions, proofs, consumers and
publication commits. Require focused/aggregate builds, full tests, all
public/consumer standard-axiom audits, dependency closure, kernel-policy and
whitespace checks, plus independent reviews.
