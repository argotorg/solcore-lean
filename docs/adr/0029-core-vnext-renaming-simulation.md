# ADR-0029: Semantic Core vNext renaming and environment-insertion foundation

- Status: Accepted
- Decision date: 2026-08-27
- Scope: eleventh internal Semantic Core vNext vertical slice
- Implementation: In progress

## Context

ADR-0011's derived `wordLt` and `wordGe` builders preserve source operand order
by binding the left operand, weakening the right expression under that binding,
then applying swapped `wordGt` values. Their arbitrary-expression proof surface
therefore needs a general account of de Bruijn renaming and runtime environment
insertion. The Core currently has `Expr.weakenAt`, but not the corresponding
static preservation and dynamic simulation foundation.

This is proof infrastructure. It changes no expression, value, evaluation,
fault, fuel, source, profile, schema, wire, Oracle, or observation semantics.

## Decision

The Core proof library will define:

- a general de Bruijn `Renaming`, its binder-aware lift, and `Expr.rename`;
- insertion renaming and a theorem identifying existing `Expr.weakenAt` with
  that renaming;
- a context-respecting relation for renamings;
- preservation of `HasType` and `BranchesHaveType` under a respecting
  renaming; and
- a typed binary simulation relation for runtime values and environments.

The expression renaming must lift beneath lambda, case, let, and named-data
branch binders. Context lookup and insertion lemmas must expose the exact index
mapping rather than relying on incidental simplification.

## Dynamic relation

Runtime simulation is relational, not raw value equality. At unit, boolean,
word, and cell-reference types, related values are equal. Product, sum, and
named-data values are related structurally through their components. Closures
are related through appropriately renamed bodies and related captured
environments, with application preserving the relation; they are not required
to be equal Lean values.

The paired evaluation theorem relates an expression and its renaming under
related typed environments. For environment insertion, both executions start
with the same store and finish with the same store. This literal store equality
is justified by the existing `CellPayload` boundary: stored payload types
exclude closures and other values that would require syntax renaming, including
through their permitted recursive structure.

## Rejected proof shortcuts

Unary `Reducible` or `RuntimeValueHasType` results are insufficient. They prove
termination or typing of each execution independently, but do not prove equal
base results, equal final stores, or correspondence between the executions.

Raw equality for arbitrary result values is false. For example, evaluating a
lambda before and after insertion produces closures whose captured environment
and renamed body differ structurally even though they represent the same typed
behavior. The binary relation records that behavior without asserting a false
closure equality.

## Exit condition

The implementation must yield this usable insertion corollary: if a word-typed
expression evaluates under a typed environment, weakening it at zero and
inserting a typed runtime value at the environment head evaluates to the
identical word and identical final store from the same initial store.

That corollary enables later arbitrary-expression typing, evaluation, and
weakening proofs for the existing `wordLt` and `wordGe` expansions. Completing
those comparison interfaces is a separate slice; this ADR does not change their
definitions or exact fuel.

## Required proof and tests

- prove renaming lift, lookup, insertion, identity, and composition laws;
- prove `Expr.rename` binder behavior and its equivalence with `weakenAt`;
- prove mutual `HasType` and `BranchesHaveType` renaming preservation;
- define typed value and environment simulation for every current type/value;
- prove evaluation simulation for every current expression form;
- prove same-store insertion and base-type equality corollaries;
- prove the word-typed head-insertion exit theorem;
- test nested binders, free-variable insertion, closures, application, cells,
  named data, store effects, and the `wordLt`/`wordGe` prerequisite shape; and
- run warning, trust, axiom, full-test, and whitespace audits.

## Boundaries

No new public tag or wire projection is introduced, so all frozen wire behavior
is unchanged. This ADR defines no source syntax, elaboration, optimizer rewrite,
ABI rule, opcode mapping, gas rule, or new comparison operation.

## Consequences

Future binder-introducing derived expressions can reuse one sound static and
dynamic renaming foundation instead of adding ad hoc weakening assumptions.
