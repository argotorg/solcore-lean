# Semantic Core roadmap

The active goal is a syntax-independent executable semantics rich enough to
represent Solcore programs after resolution and typing. The existing published
Core remains frozen while the internal Core grows additively.

## Completed foundation

The current Core already has:

- a closed value and type algebra for unit, boolean, and word;
- immutable de Bruijn bindings and conditionals;
- a specified primitive subset;
- declarative typing and big-step evaluation;
- a deterministic CEK machine and fuelled runner;
- executable inference and detailed diagnostics;
- static and dynamic correspondence;
- progress, preservation, typed results, and sufficient fuel; and
- two frozen wire versions with Oracle v2 and v3.

These results remain regression obligations for every extension.

## Implementation order

| Order | Feature family | Status | Why it is here |
| ---: | --- | --- | --- |
| 1 | Binary products and projections | Complete | Exercises every Core layer without introducing divergence |
| 2 | Functions, application, and lexical closures | Complete | Establishes callable values and reusable computation |
| 3 | Binary sums and elimination | Complete | Adds structured branching without choosing source pattern syntax |
| 4 | First-order local cells | Complete | Introduces explicit local state after pure values are stable; source assignment elaborates later |
| 5 | Named algebraic data and direct matching | Next | Builds on sums after constructor identity is accepted |
| 6 | Additional primitives and conversions | Planned | Added one closed, typed family at a time |
| 7 | Recursion and divergence | Blocked | Requires a deliberate change to termination and resource claims |
| 8 | Contract runtime state and observations | Planned | Adds external effects independently of source syntax |
| 9 | ABI and storage | Planned | Follows accepted layout and admissibility decisions |
| 10 | Resolved static semantics and elaboration adapters | Planned | Connects stabilized source syntax last |

This order can change when a prerequisite is discovered, but grammar work does
not become a prerequisite for Core execution.

## Completed Core vNext slice: products

ADR-0019 fixes:

- binary product types and pair values;
- pair construction;
- first and second projection;
- left-to-right, exactly-once component evaluation;
- exactly-once evaluation of a projected operand;
- no product equality, ABI mapping, source tuple nesting, or public wire tag;
- rejection by Semantic Core v1 and v2 projections.

The current implementation satisfies all of the following:

1. Declarative typing covers pair construction and both projections.
2. Executable inference is sound and complete.
3. Detailed checking agrees with ordinary inference.
4. Big-step evaluation is deterministic.
5. CEK transitions execute the same order and result.
6. Machine and big-step evaluation correspond in both directions.
7. Value, environment, frame, and state typing cover products.
8. Progress, preservation, typed-result, sufficient-fuel, and no-fault
   theorems still hold.
9. Tests cover nesting, evaluation order, invalid projection, exact fuel, and
   old-wire rejection.

The feature remains internal and therefore does not change Oracle v2 or v3.

## Completed Core vNext slice: functions and closures

ADR-0020 fixes:

- unary functions with explicit parameter and result annotations;
- a de Bruijn parameter at index zero;
- callee-before-argument evaluation;
- lexical capture of immutable environments;
- direct, non-recursive binding; and
- continuation-based return from a function body.

Recursion, divergence, named functions, explicit return, and Surface syntax
remain separate. This keeps the current totality and sufficient-fuel theorems
meaningful while the call mechanism is established.

The implementation now covers declarative and executable typing, detailed
diagnostics, lexical capture, callee-before-argument CEK execution, evaluator
correspondence, state safety, old-wire rejection, and focused regressions. A
logical-relations argument preserves total evaluation and sufficient fuel for
the extended non-recursive language.

## Completed Core vNext slice: sums and elimination

ADR-0021 fixes:

- left and right injection representation;
- how both alternative payload types remain available at runtime;
- branch binders and de Bruijn scope;
- scrutinee-before-selected-branch evaluation;
- detailed checking paths and mismatch diagnostics; and
- the boundary between binary sums and later named algebraic data.

Exhaustive binary elimination is complete without choosing Surface pattern
syntax or constructor identity.

The implementation now covers both injections, payload binders, selected-only
branch evaluation, detailed diagnostics, weakening, CEK/big-step
correspondence, safety, logical-relations totality, exact fuel, interactions
with products and closures, and old-wire rejection.

## Completed Core vNext slice: first-order local cells

[ADR-0022](adr/0022-core-vnext-first-order-local-cells.md) fixes:

- first-class `cell` types and typed cell-reference values;
- explicit `newCell`, `loadCell`, and `storeCell` Core operations;
- an append-only local store with stable natural-number locations;
- initializer-before-allocation and reference-before-right-hand-side order;
- `unit` as the result of a successful store;
- closure sharing through captured references rather than copied stores;
- a stateful internal runner that returns the final local store; and
- rejection of every cell form by the frozen Core wire projections.

Cell contents are limited recursively to unit, boolean, word, product, and sum
data. Functions and cells cannot be stored in cells during this slice. This is
not merely an implementation convenience: function-valued cells can encode
recursion and divergence, which belong to a later roadmap decision that will
replace the current totality and sufficient-fuel claims.

The existing `Program.run` behavior remains available as a compatibility
wrapper that discards the final local store. Oracle v2 and v3 inputs cannot
construct cells, so their store stays empty and their published behavior does
not change.

The implementation covers declarative and executable typing, store-threaded
evaluation, CEK execution, correspondence, store-indexed safety, logical
reducibility, sufficient fuel, detailed diagnostics, composite-payload and
aliasing tests, and old-wire rejection. Existing public Core and Oracle
behavior remains unchanged.

## State and contracts

Local mutation uses the explicit typed-cell store fixed by ADR-0022, never
hidden host mutation. This store contains local runtime values and is scoped to
one Core execution. Contract execution will later add a separate explicit
world state, call frames, transaction inputs, and rollback checkpoints.

Runtime observations are defined over semantic effects. They do not require
executing compiler-generated EVM bytecode.

## Per-feature workflow

For each feature:

1. Accept a small ADR fixing observable meaning.
2. Extend syntax, types, values, and declarative rules.
3. Extend executable checking and evaluation.
4. Extend the CEK machine.
5. Re-establish correspondence and safety.
6. Add compatibility rejection for old wires.
7. Add focused tests and run the full repository audit.
8. Keep the feature internal until a separate publication decision.

## Publication

Core vNext has no public schema or profile. When a useful closed subset is
ready, publication must be additive. Existing Core schemas and Oracle behavior
remain byte-for-byte compatible.
