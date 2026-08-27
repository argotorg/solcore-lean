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

| Order | Feature family | Why it is here |
| ---: | --- | --- |
| 1 | Binary products and projections | Exercises every Core layer without introducing divergence |
| 2 | Functions, application, and lexical closures | Establishes callable values and reusable computation |
| 3 | Sum values, algebraic data, and pattern matching | Adds structured branching and user data |
| 4 | Mutable locals and assignment | Introduces explicit local state after pure values are stable |
| 5 | Additional primitives and conversions | Added one closed, typed family at a time |
| 6 | Recursion and divergence | Requires a deliberate change to termination and resource claims |
| 7 | Contract runtime state and observations | Adds external effects independently of source syntax |
| 8 | ABI and storage | Follows accepted layout and admissibility decisions |
| 9 | Resolved static semantics and elaboration adapters | Connects stabilized source syntax last |

This order can change when a prerequisite is discovered, but grammar work does
not become a prerequisite for Core execution.

## Active slice: products

ADR-0019 fixes:

- binary product types and pair values;
- pair construction;
- first and second projection;
- left-to-right, exactly-once component evaluation;
- exactly-once evaluation of a projected operand;
- no product equality, ABI mapping, source tuple nesting, or public wire tag;
- rejection by Semantic Core v1 and v2 projections.

The slice is complete when all of the following hold:

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

## Functions and closures

The next decision must fix:

- parameter and argument representation;
- left-to-right argument evaluation;
- closure environments and their typing;
- direct versus recursive binding;
- return and control transfer;
- recursion support; and
- the relation between divergence and explicit fuel.

Non-recursive functions can be delivered separately if doing so preserves a
clear later path to recursion.

## State and contracts

Local mutation should use explicit typed cells rather than hidden host
mutation. Contract execution should then add an explicit world state, call
frames, transaction inputs, and rollback checkpoints.

Runtime observations are defined over semantic effects. They do not require
executing compiler-generated EVM bytecode.

## Per-feature workflow

For each feature:

1. Accept a small ADR fixing observable meaning.
2. Extend syntax, types, values, and declarative rules.
3. Extend executable checking and evaluation.
4. Extend the CEK machine.
5. re-establish correspondence and safety.
6. Add compatibility rejection for old wires.
7. Add focused tests and run the full repository audit.
8. Keep the feature internal until a separate publication decision.

## Publication

Core vNext has no public schema or profile. When a useful closed subset is
ready, publication must be additive. Existing Core schemas and Oracle behavior
remain byte-for-byte compatible.
