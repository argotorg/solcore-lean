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

## Next active design: sums and elimination

The next decision must fix:

- left and right injection representation;
- how both alternative payload types remain available at runtime;
- branch binders and de Bruijn scope;
- scrutinee-before-selected-branch evaluation;
- detailed checking paths and mismatch diagnostics; and
- the boundary between binary sums and later named algebraic data.

Exhaustive binary elimination can be completed without choosing Surface
pattern syntax or constructor identity.

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
