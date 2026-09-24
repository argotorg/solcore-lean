# ADR-0279: independent shared function argument factorization

## Status

Accepted; additive frontend-semantics proofs. Canonical Rust remains fixed at
`18fd9f75d290df0070e21ee56e0a5691f232596f`. Existing executable operations,
source admission, header policy and all old contracts remain unchanged.

## Context

The shared function interface already distinguishes independent compilation and
actual preparation. Its public operational factorization laws apply to any
child checker, but their private reconstruction helpers use that checker's
graph. They do not expose argument reconstruction for an arbitrary independent
child elaboration relation.

Static compilation has no actual argument values. It must not manufacture them
or assume inhabitants for every annotated type. Conversely, matching only the
list of types cannot justify permuting or replacing the supplied actual values
and closure captures. The exact prepared record must retain their order.

An arbitrary child elaboration relation need not determine a unique Core term.
Independent argument factorization therefore must not silently assume child
determinism, checker correctness or unconditional compilation uniqueness.

## Decision

Add `ComputationFunctionArgumentProperties` with five public laws:

- `ComputationFunctionPrepares.compiles`;
- `ComputationFunctionCompiles.prepare_arguments`;
- `computationFunctionPrepares_toCompiled_iff`;
- `ComputationFunctionPrepares.argument_values`;
- `ComputationFunctionPrepares.unique_of_toCompiled_eq`.

Quantify over the same arbitrary independent `ChildElab`. Erasing values from
independent preparation gives compilation of the exact `toCompiled` record.
Given independent compilation and a supplied list of structurally typed actual
arguments whose types equal the reverse of the compiled context's values,
construct independent preparation with exactly that compiled projection.
The type equation retains arity and written argument order.

Expose the converse as an iff over the existence of a prepared record with
that fixed compiled projection. Preserve the original declaration, parameter
names/IDs, annotation meanings, Core and return type. Actual input environment
values are exactly the supplied values reversed once; closure captures remain
literal. No default or reconstructed runtime inhabitant is introduced.

Two preparations of the same original declaration and actual arguments are
equal when their compiled projections are equal. Keep that last premise:
the theorem does not claim that arbitrary child elaboration determines one
compiled Core term, nor that different same-typed actual arguments give equal
prepared records.

Use the existing independent parameter erasure, argument reconstruction,
layout and result-uniqueness laws. The existing `PreparedRuntimeFunction.toCompiled`
definition retains its historical imports. Do not use shared checker-graph
helpers, a concrete child implementation, a runtime world, a store, execution
evidence or child determinism in the new production module.

## Consumers and verification

Build independent original compilation before reconstructing actual
preparation. Exercise arbitrary source nesting and annotated types without
requiring an actual inhabitant for the static proof. For reconstruction supply
every actual argument and its structural evidence explicitly.

Check original parsed functions with actual closures and captured cell
references. Compare independently built actual binding rows and the exact
compiled projection, original raw body evidence and separate literal Core
paths. Include same-typed value/capture changes and permutations, ordered
effects, precise costs, full intermediate states and resumption. Preparation
with structurally typed arguments is not runtime safety for an arbitrary store.

Include wrong arity and ordered-type mismatches, hand-built records without
compilation evidence, and an explicitly artificial nondeterministic child
relation. The latter must retain separate compiled terms and demonstrate why
uniqueness is restricted to a fixed compiled projection. It is not a claim
about nondeterminism of the actual source language or a checker graph.

Require focused/aggregate builds, full tests, exact standard-only public and
consumer axiom catalogs, independent semantic reviews, old bytes/contracts/
imports, kernel-policy, EOF, and whitespace checks. Keep new proof and consumer files
below 300 lines and decision, proof, consumers and publication in small commits.

## Non-goals

No new executable factorization, source function evaluator, raw function
judgment, cost semantics, child-checker correctness theorem, unconditional
compilation/preparation uniqueness, runtime-world construction, source feature,
parser/diagnostic work or change to old definitions/contracts/consumers.
