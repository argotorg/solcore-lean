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
| 5 | Named algebraic data and direct matching | Complete | Adds program-local constructor identity without source pattern syntax |
| 6 | Boolean and word conversions | Complete | Derives total conversions without a new Core tag |
| 7 | Word zero test | Complete | Derives a canonical word result from existing expressions |
| 8 | Short-circuit boolean operators | Complete | Fixes selected-branch-only effects without a new Core tag |
| 9 | Word nonzero test | Complete | Composes total truthiness and canonical word conversion without a new tag |
| 10 | Word comparison flags | Complete | Derives canonical word equality and unsigned-greater results without new tags |
| 11 | Renaming and environment insertion | Complete | Establishes static and dynamic weakening without changing semantics |
| 12 | Derived boolean word comparisons | Complete | Completes proof interfaces for the existing comparison builders |
| 13 | Derived word comparison flags | Complete | Wraps existing boolean comparisons with canonical word conversion |
| 14 | Derived-builder arbitrary renaming laws | Complete | Backfills the general renaming API for eight existing builders |
| 15 | Direct unary primitive interface | Complete | Completes focused APIs and regressions for existing boolNot and wordNot |
| 16 | Totalized unsigned division and modulo | Active | Completes focused APIs and strict zero-divisor regressions |
| 17 | Additional conversions and primitives | Planned | Added one closed, typed family at a time |
| 18 | Recursion and divergence | Blocked | Requires a deliberate change to termination and resource claims |
| 19 | Contract runtime state and observations | Planned | Adds external effects independently of source syntax |
| 20 | ABI and storage | Planned | Follows accepted layout and admissibility decisions |
| 21 | Resolved static semantics and elaboration adapters | Planned | Connects stabilized source syntax last |

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

## Completed Core vNext slice: named algebraic data

[ADR-0023](adr/0023-core-vnext-named-algebraic-data.md) fixes the semantic
shape implemented by this slice:

- every program has an immutable, program-local data-definition table;
- a data type is identified by its table index, while a constructor is
  identified by its owning data type and constructor index;
- each constructor carries one payload (`unit` for a nullary constructor and a
  product for multiple fields after later elaboration);
- definitions may be recursive or mutually recursive;
- constructor payloads are first-order, excluding functions while allowing
  named data and admissible local-cell references;
- a match has one branch per constructor in table order and binds the selected
  payload at de Bruijn index zero; and
- an explicit result type makes elimination of an empty data type well formed.

This match form is already normalized. It has no wildcard, nested source
pattern, guard, overlap, or textual first-match behavior. A future resolved
adapter will translate those source concepts into constructor-order branches.

The implementation covers the full vertical proof boundary: whole-table
validity, declarative and executable typing, recursive-data safety and
termination, store-threaded evaluation, CEK execution, machine correspondence,
detailed diagnostics, exact fuel, and rejection of named forms and nonempty
definition tables by both frozen Core wires.

## Completed Core vNext slice: boolean and word conversions

[ADR-0024](adr/0024-core-vnext-bool-word-conversions.md) fixes the first completed
conversion family:

- `boolToWord(false)` is word zero and `boolToWord(true)` is word one;
- `wordToBool(0)` is `false`, while every nonzero word becomes `true`;
- both operations are derived builders for existing conditional and primitive
  expressions rather than new expression tags; and
- each operand is evaluated exactly once and its resulting store is preserved.

The implementation does not extend the CEK machine or big-step relation.
Dedicated typing, inference, evaluation, zero/nonzero, store-threading, and
weakening theorems are complete. Effectful exactly-once, exact-fuel,
word-boundary, type-error, and frozen-wire tests pass with the full repository
audit.

This slice is independent of ABI decoding. Total nonzero truthiness does not
validate a canonical ABI boolean: strict zero-or-one admissibility, byte layout,
and rejection behavior remain a later ABI decision. No wire schema, Oracle
operation, profile, capability, or source spelling changes here.

## Completed Core vNext slice: word zero test

[ADR-0025](adr/0025-core-vnext-word-is-zero.md) fixes `wordIsZero : word -> word`.
It maps zero to word one and every nonzero word to word zero by expanding to
`boolToWord(wordEq(value, word(0)))`. The operand appears once, and no new Core,
CEK, wire, or Oracle tag is introduced. Wire v1 rejects the required primitive
form and wire v2 projects the existing expansion. This operation remains
distinct from `wordToBool` truthiness and from ABI boolean decoding.

The implementation includes named expansion, typing, inference, general and
zero/nonzero evaluation, store-threading, and weakening theorems. Boundary,
type-error, effectful exactly-once, exact-fuel, and frozen-wire tests pass.

## Completed Core vNext slice: short-circuit booleans

[ADR-0026](adr/0026-core-vnext-short-circuit-booleans.md) fixes boolean
conjunction and disjunction as conditional expansions. Each left operand runs
once and first. The right operand runs only when selected, so its effects,
faults, store changes, and fuel cost are skipped with the branch. No new Core,
CEK, wire, or Oracle tag is introduced, and both frozen wires project the exact
ordinary conditional expansion.

Named expansion, typing, inference, and all four store-threaded branch theorems
are complete. Tests cover truth, left and right operand types, skipped and
selected faults, allocation and writes, left-to-right store threading into the
right operand, exact fuel, weakening, and exact v1/v2 wire projection.

## Completed Core vNext slice: word nonzero test

[ADR-0027](adr/0027-core-vnext-word-is-nonzero.md) fixes
`wordIsNonzero : word -> word` as `boolToWord(wordToBool(x))`. Zero maps to word
zero and every nonzero word to word one. The operand runs exactly once and its
final store is preserved. The derived form adds no tag; wire v1 rejects it and
wire v2 projects the exact expansion. Named expansion, typing, inference,
general and zero/nonzero store theorems, and weakening are complete. Tests cover
0/1/2/maximum, types/raw faults, exact 9/10 fuel, exactly-once allocation and
writes with final-store preservation, semantic distinctions, and exact v1/v2
projection. Audits pass. Additional primitives remain planned.

## Completed Core vNext slice: word comparison flags

[ADR-0028](adr/0028-core-vnext-word-comparison-flags.md) derives
`wordEqFlag` and unsigned `wordGtFlag` by applying `boolToWord` to the existing
boolean comparisons. Both return canonical word one or zero and preserve
left-to-right exactly-once evaluation, stores, and faults. They add no tag;
wire v1 rejects and wire v2 projects the exact expansions. Existing boolean
comparisons remain unchanged. Named expansions, typing, inference, general and
eq/ne/gt/not-gt store theorems, and weakening are complete. Tests cover values,
boundaries, types, raw fault order, two allocating/writing operands and final
store, exact 7/8 and 31/32 fuel, boolean comparison preservation, and exact
v1/v2 projections. Audits pass. Additional primitives remain planned.

## Completed Core vNext slice: renaming and environment insertion

[ADR-0029](adr/0029-core-vnext-renaming-simulation.md) establishes general
de Bruijn renaming and lift, preservation of expression and branch typing, and
structural relations for values, environments, and stores. `Evaluates.rename`
covers every evaluation form. `CellPayload` exactness and
`Evaluates.weakenAt_zero_word` preserve the identical ground result and final
store after head insertion. Static and dynamic tests cover the full foundation.

## Completed Core vNext slice: derived word comparisons

[ADR-0030](adr/0030-core-vnext-derived-word-comparisons.md) completes the proof
interfaces for the existing `wordNe`, `wordLt`, `wordLe`, and `wordGe`
builders. Their ADR-0011 expansions do not change. All four provide expansion,
typing, inference, renaming, and weakening results. `wordNe` and `wordLe`
provide general untyped evaluation results; `wordLt` and `wordGe` provide typed,
store-threaded evaluation results. Their eight truth cases are proved.
`wordLt` and `wordGe` retain
nested lets and right-operand weakening, which preserves left-to-right,
exactly-once evaluation for effectful and faulting expressions. Value, type,
fuel, fault, effect, Wire v1 rejection, and exact Wire v2 projection and
round-trip tests pass without a new tag or public behavior. The next additional
primitive or conversion is selected by a separate ADR; ADR-0031 is that next
decision.

## Completed Core vNext slice: derived word comparison flags

[ADR-0031](adr/0031-core-vnext-derived-word-comparison-flags.md) derives
`wordNeFlag`, `wordLtFlag`, `wordLeFlag`, and `wordGeFlag` by applying
`boolToWord` to the existing boolean comparisons. All four have expansion,
typing, inference, renaming, weakening, general evaluation, and two case
theorems. Value, type, exact-fuel, fault, effect, Wire v1 rejection, and exact
Wire v2 projection and round-trip tests pass. Right-side faults in `wordLtFlag`
and `wordGeFlag` retain the completed left store while weakening lifts their
variable index across the internal binding. The slice keeps left-to-right
exactly-once evaluation and adds no Core or wire tag. The next feature is
selected by a separate ADR.

## Completed Core vNext slice: direct unary primitives

[ADR-0033](adr/0033-core-vnext-direct-unary-primitive-interface.md) keeps
`boolNot` and `wordNot` as raw `.unary` expressions and adds their named typing,
inference, general and case evaluation, renaming, and weakening interfaces.
Zero, maximum, and universal involution facts characterize `Word.bitNot`.
Focused tests cover values, types, raw faults, an exactly-once effectful operand
and final store, exact 2/3 and 14/15 fuel, Wire v1 rejection, and exact Wire v2
projection and round trips. No alias, tag, runtime meaning, or byte encoding
changes. The next feature is selected by a separate ADR.

## Active Core vNext slice: totalized unsigned division

[ADR-0034](adr/0034-core-vnext-totalized-unsigned-division.md) keeps `wordDiv`
and `wordMod` as raw binary operators. Named zero and nonzero value, exact
primitive-application, and store-threaded evaluation results expose their
existing behavior. A zero divisor does not skip either operand: numerator and
divisor retain left-to-right effects, faults, final stores, and fuel. No alias,
tag, Safety rule, or Wire encoding changes.

## Completed Core vNext slice: derived-builder renaming laws

[ADR-0032](adr/0032-core-vnext-derived-builder-renaming-laws.md) backfills
arbitrary `Expr.rename` laws for exactly eight older derived builders:
`boolToWord`, `wordToBool`, `wordIsZero`, `wordIsNonzero`, `boolAnd`, `boolOr`,
`wordEqFlag`, and `wordGtFlag`. Each law lives in its builder's module, with
`rename_boolToWord` relocated to `Conversions`. The non-insertion `swap01`
goldens exchange free variables zero and one. Runtime witnesses cover the
conversion, short-circuit, and comparison-flag families under corresponding
environments. No weakening law, runtime semantics, or wire behavior changes.
The next feature is selected by a separate ADR.

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
