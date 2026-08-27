# Current status

This page is the revision-local answer to what works now. It distinguishes the
stable published system, internal completed work, paused work, and the active
semantics program.

## Summary

Two external interfaces are stable:

- Oracle v3 checks and evaluates the closed Semantic Core v2 language.
- Oracle v4 parses the closed Surface v1 single-file language.

The larger internal Multi frontend can lex, parse, structurally validate, and
certify one file for its current grammar. That work is not published and is
now frozen because the concrete Solcore syntax may change.

Active development has moved to Semantic Core vNext. The goal is to define
types, evaluation, state, and observations independently of concrete source
spelling, then connect a stabilized future Surface language through a separate
adapter. The explicit local-cell store accepted by ADR-0022 and the
program-local named algebraic data and normalized constructor matching accepted
by ADR-0023 are complete internal slices. The derived `boolToWord` and `wordToBool`
conversions accepted by ADR-0024 are also complete without adding a new Core
expression form. The `wordIsZero` slice accepted by ADR-0025 is complete and
likewise adds no new Core expression form. The derived short-circuit `boolAnd`
and `boolOr` slice accepted by ADR-0026 is complete. The derived word-valued
nonzero predicate accepted by ADR-0027 is also complete. Core vNext as a whole
remains active. The word-valued equality and unsigned greater-than flags from
ADR-0028 are complete, with additional conversions and primitives planned.

## Implementation status

| Area | Implementation | Proof | Publication |
| --- | --- | --- | --- |
| Versioning, profiles, verdicts | Complete | Applicable invariants checked | Oracle v1 and later |
| Small Semantic Core machine | Complete | Complete for the closed fragment | Oracle v2 and v3 |
| Semantic Core primitive subset | Complete | Complete | Oracle v3 / Core v2 |
| Internal Core binary products | Complete | Complete | Not published |
| Internal non-recursive functions | Complete | Complete, including totality | Not published |
| Internal binary sums | Complete | Complete, including totality | Not published |
| Internal first-order local cells | Complete | Complete, including store safety and totality | Not published |
| Internal named algebraic data | Complete | Complete, including recursive-data safety and totality | Not published |
| Internal boolean/word conversions | Complete | Complete | Not published |
| Internal word zero test | Complete | Complete | Not published |
| Internal short-circuit boolean operators | Complete | Complete | Not published |
| Internal word nonzero test | Complete | Complete | Not published |
| Internal word comparison flags | Complete | Complete | Not published |
| Restricted single-file parser | Complete | Complete | Oracle v4 / Surface v1 |
| Workspace identity and validation | Complete | Complete | Internal only |
| Multi lexer and chart parser | Complete for the frozen grammar | Soundness, total selection, and grammar-specific certificates | Internal only |
| Structural validation | Complete for the frozen AST | Executable/declarative equivalence and resource bound | Internal only |
| Source locations and retained tokens | Complete for the frozen AST and grammar | Parser-wide correspondence | Internal only |
| Certified one-file Multi frontend | Complete for the frozen grammar | Lexical, parse, structural, location, and token evidence | Internal only |

The frozen parser baseline passed the full test, warning, metadata,
kernel-policy, and axiom audits used during development.

## What the published Semantic Core contains

The current public Core is deliberately small:

- unit, boolean, and bounded 256-bit word values;
- de Bruijn variables and initialized immutable bindings;
- condition-first, selected-branch-only conditionals;
- boolean and word negation;
- modular word arithmetic;
- unsigned division and modulo with a zero result for a zero divisor;
- word equality and unsigned greater-than;
- bitwise operations and bounded logical shifts; and
- left-to-right, exactly-once operand evaluation.

For this fragment, executable checking and evaluation are connected to
declarative typing and big-step evaluation. The repository proves typing
uniqueness, machine determinism, checker soundness and completeness, CEK and
big-step correspondence, progress, preservation, sufficient fuel, and fault
unreachability for well-typed closed programs.

## Missing semantics

The public Core fragment is complete, but it is not the complete Solcore
language. The following remain:

- explicit return, recursion, and divergence;
- source-level mutable declarations, assignment syntax, and their elaboration;
- source-level data declarations, pattern syntax, and elaboration into the
  completed internal named-data Core;
- additional conversions and primitives beyond the completed short-circuit slice;
- resolved-name and typed intermediate representations;
- polymorphism, class evidence, and staging;
- contract entry and call semantics;
- explicit state, storage, rollback, balances, logs, and creation;
- ABI admissibility, encoding, decoding, and dispatch; and
- versioned contract observations and EVM-revision policy.

Several later items require an Accepted semantic decision before code.

## Frozen frontend work

The published Surface v1 and Oracle v4 remain supported. The internal Multi
frontend remains usable as a reference for its fixed grammar. New work on the
following is paused:

- fast-parser completion and chart equivalence;
- grammar-specific token and location proof maintenance;
- structural syntax identity;
- module and lexical resolution over the current AST;
- source checking and Surface-to-Core elaboration; and
- publication of the Multi frontend.

## Completed Core vNext results

The first Core vNext vertical slice adds:

- a binary product type;
- pair construction;
- first and second projection;
- left-to-right pair evaluation;
- executable inference and detailed checking;
- CEK execution and big-step semantics;
- soundness, completeness, correspondence, and safety results; and
- regression tests for nesting, exact fuel, evaluation order, invalid
  projection, and old-wire rejection.

This internal extension will not reinterpret Semantic Core v1 or v2. Frozen
wire projections reject product types, values, expressions, and programs.

See the [Semantic Core roadmap](M1_PLAN.md) and
[ADR-0019](adr/0019-core-vnext-products.md).

The second vertical slice adds:

- explicitly typed unary functions;
- callee-before-argument application;
- immutable lexical closures;
- de Bruijn parameters and captured bindings;
- detailed function-checking diagnostics;
- CEK execution and big-step correspondence; and
- a logical-relations proof retaining total evaluation and sufficient fuel for
  non-recursive, well-typed programs.

Frozen wire projections reject function types, lambdas, applications,
closures, and programs containing them. See
[ADR-0020](adr/0020-core-vnext-non-recursive-functions.md).

The third vertical slice adds:

- nestable binary sum types;
- left and right injections;
- exhaustive case elimination with a payload binding;
- scrutinee-first, selected-branch-only evaluation;
- detailed sum diagnostics and branch paths; and
- logical-reducibility, CEK correspondence, safety, exact-fuel, interaction,
  and old-wire rejection coverage.

This binary-sum slice deliberately did not add named algebraic data. Named data
was added by the later ADR-0023 slice; source-level pattern syntax remains
deferred. See [ADR-0021](adr/0021-core-vnext-binary-sums.md).

## Completed Core vNext local-cell result

[ADR-0022](adr/0022-core-vnext-first-order-local-cells.md) defines first-order
local cells. Its Lean implementation and proof boundary are complete.

The accepted design adds typed cell references plus explicit allocation, load,
and store operations. Allocation occurs after its initializer; store resolves
its reference before evaluating the right-hand side; every operand is
evaluated exactly once; and store returns `unit`. Closures capture references
but never copy the local store, so two closures containing the same reference
share writes.

The local store is explicit, append-only for allocation, and separate from
future contract storage. Cell contents are restricted recursively to unit,
boolean, word, product, and sum data. Functions and cells are excluded as cell
contents so that mutation cannot encode recursion before the separate
recursion-and-divergence decision.

All Core layers now cover cells: syntax and values, declarative and executable
typing, store-threaded big-step evaluation, CEK execution, correspondence,
store-indexed safety, logical reducibility, sufficient fuel, diagnostics,
focused tests, and old-wire rejection. The internal stateful runner returns
the final local store; the existing `Program.run` and Oracle path erase it for
compatibility. No public schema or Oracle version was added.

## Completed Core vNext named-data result

[ADR-0023](adr/0023-core-vnext-named-algebraic-data.md) is Accepted, and its
Lean implementation and proof boundary are complete. It adds an immutable
data-definition table to each internal Core program. Data types use
program-local table indices; constructors use an owning data-type index plus a
constructor index. No source name or namespace becomes part of Core identity.

Every constructor has one payload. Nullary constructors use `unit`, while a
future adapter can combine multiple fields into a product. Definitions may be
recursive or mutually recursive. Payloads exclude functions but may contain
named data and admissible local-cell references.

Matching is exhaustive and already normalized: the branch list is in
constructor-table order, the chosen payload is de Bruijn index zero, and only
the selected branch runs. The match carries an explicit result type, so an
empty data type can have a typed eliminator with no branches. Wildcards,
nested source patterns, guards, overlap, and textual first-match ordering are
outside this Core slice.

All Core layers now cover this slice: whole-table validity, declarative and
executable typing, detailed diagnostics, store-threaded big-step evaluation,
CEK execution, evaluator/machine correspondence, runtime and machine-state
safety, recursive-data totality, sufficient fuel, and focused regressions.
Recursive, mutually recursive, empty, effectful, cell-reference, exact-fuel,
diagnostic, raw-fault, and version-boundary cases are covered.

Semantic Core v1 and v2 reject every named form and every nonempty definition
table, so no published Oracle behavior changes.

## Completed Core vNext boolean/word conversion slice

[ADR-0024](adr/0024-core-vnext-bool-word-conversions.md) is Accepted and its
implementation and proof boundary are complete. It fixes two total conversions:

- `boolToWord` maps `false` to word zero and `true` to word one;
- `wordToBool` maps word zero to `false` and every nonzero word to `true`.

Both are builders for ordinary existing Core expressions. The operand occurs
once in each expansion, so existing conditional and primitive evaluation give
exactly-once behavior and preserve the operand's resulting local store. No new
type, value, expression, CEK frame, machine rule, or fault is required.

This truthiness conversion is not ABI decoding. A future ABI boolean decoder
must separately decide and enforce strict zero-or-one admissibility; in
particular, it may reject word two even though `wordToBool` returns `true` for
that value.

Dedicated theorems cover typing, inference, exact evaluation, zero/nonzero
behavior, store threading, and weakening through the expansions. Focused tests
cover effects, exact fuel, type errors, word boundaries, and unchanged wire
projection. The full test, warning, kernel-trust, axiom, and whitespace audits
pass. Neither frozen wire schema nor any Oracle profile or capability changes.

## Completed Core vNext word zero-test slice

[ADR-0025](adr/0025-core-vnext-word-is-zero.md) fixes `wordIsZero : word -> word`:
zero maps to word one and every nonzero word maps to word zero. The builder
expands into existing `wordEq` and `boolToWord` expressions, so it adds no Core
tag and evaluates its operand exactly once. Wire v1 continues to reject the
needed primitive expansion, while wire v2 projects it through existing forms.
This word-valued predicate is separate from `wordToBool` truthiness and from
future strict ABI boolean decoding.
Dedicated theorems cover expansion, typing, inference, general and zero/nonzero
evaluation, store threading, and weakening. Tests cover word boundaries,
type errors, effects, exact fuel, the distinction from `wordToBool`, and frozen
wire behavior. The warning, kernel-trust, axiom, and whitespace audits pass.

## Completed Core vNext short-circuit boolean slice

[ADR-0026](adr/0026-core-vnext-short-circuit-booleans.md) fixes
`boolAnd(x, y) = ifE x y false` and `boolOr(x, y) = ifE x true y`. Both have
type `bool × bool -> bool`. The left operand is evaluated once and first; the
right operand is evaluated only when selected. Existing conditional semantics
therefore determine store threading, faults, and fuel without a new tag or
machine rule. Both frozen wires project the exact handwritten expansions.
The implementation proves the named expansions, typing, inference, and all
four store-threaded branch cases. Tests cover truth tables, left and right
types, skipped and selected faults, allocation and writes, left-to-right store
threading into the right operand, exact fuel, weakening, and exact v1/v2 wire
projection.

## Completed Core vNext word nonzero-test slice

[ADR-0027](adr/0027-core-vnext-word-is-nonzero.md) fixes
`wordIsNonzero(x) = boolToWord(wordToBool(x))`. It maps zero to word zero and
every nonzero word to word one, evaluates `x` exactly once, and preserves its
final store. It adds no tag and remains distinct from boolean truthiness,
inverted `wordIsZero`, and strict ABI decoding. Wire v1 rejects the expansion;
wire v2 projects it exactly.
Named expansion, typing, inference, general and zero/nonzero store theorems,
and weakening are proved. Tests cover 0/1/2/maximum, types and raw faults,
exact 9/10 fuel, exactly-once allocation and writes with store threading, its
semantic distinctions, and exact v1/v2 projection. All audits pass.

## Completed Core vNext word comparison flags

[ADR-0028](adr/0028-core-vnext-word-comparison-flags.md) derives word-valued
equality and unsigned greater-than flags from the existing boolean comparisons
and `boolToWord`. They return canonical word one or zero while preserving
left-to-right exactly-once evaluation, store threading, and fault order. The
existing boolean operations remain unchanged; no new tag or published API is
introduced. Wire v1 rejects and wire v2 projects each exact expansion.
Named expansions, typing, inference, general and eq/ne/gt/not-gt store theorems,
and weakening are proved. Tests cover values, boundaries, types, raw fault
order, two allocating/writing operands and final store, exact 7/8 and 31/32
fuel, existing boolean comparisons, and exact v1/v2 boundaries. Audits pass.

## Meaning of completion

A Core feature is complete only when its declarative rules, total executable
checker and evaluator, correspondence proofs, safety coverage, negative and
boundary tests, and version-isolation behavior agree. Publication is a later,
separate decision.
