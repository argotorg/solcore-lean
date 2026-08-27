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
ADR-0029 completes the renaming and environment-insertion proof foundation.
[ADR-0030](adr/0030-core-vnext-derived-word-comparisons.md) completes the proof
interfaces for the existing `wordNe`, `wordLt`, `wordLe`, and `wordGe`
builders. Core vNext remains active.
[ADR-0031](adr/0031-core-vnext-derived-word-comparison-flags.md) completes
word-valued flags for the four existing derived comparisons.
[ADR-0032](adr/0032-core-vnext-derived-builder-renaming-laws.md) completes the
arbitrary renaming-law backfill for eight older derived builders.
[ADR-0033](adr/0033-core-vnext-direct-unary-primitive-interface.md) completes
the focused interface for the existing direct unary primitives.
[ADR-0034](adr/0034-core-vnext-totalized-unsigned-division.md) completes the
focused interface for totalized unsigned division and modulo.
[ADR-0035](adr/0035-core-vnext-bounded-logical-shifts.md) completes the focused
interface for the existing bounded logical shifts.
[ADR-0036](adr/0036-core-vnext-modular-word-arithmetic.md) completes the focused
interface for modular addition, subtraction, and multiplication. Core vNext
remains active; the next feature is selected separately.
[ADR-0037](adr/0037-core-vnext-binary-bitwise-logic.md) completes the focused
interface for binary word and, or, and xor. Core vNext remains active; the next
feature is selected separately.
[ADR-0038](adr/0038-core-vnext-direct-word-comparisons.md) completes the focused
interface for direct boolean word equality and unsigned greater-than. Core
vNext remains active; the next feature is selected separately.
[ADR-0039](adr/0039-core-vnext-word-leading-zero-count.md) completes the
internal 256-bit word leading-zero count. Core vNext remains active; the next
feature is selected separately.
[ADR-0040](adr/0040-core-vnext-word-byte-selection.md) completes internal
big-endian 256-bit word byte selection. Core vNext remains active; the next
feature is selected separately.
[ADR-0041](adr/0041-core-vnext-arithmetic-right-shift.md) completes internal
256-bit arithmetic right shift. Core vNext remains active; the next feature is
selected separately.
[ADR-0042](adr/0042-core-vnext-modular-exponentiation.md) completes internal
modular word exponentiation. Core vNext remains active; the next feature is
selected by a separate ADR.
[ADR-0043](adr/0043-core-vnext-signed-word-greater-than.md) completes internal
boolean signed word greater-than with strict left-to-right evaluation and no
public Wire representation. Its independent audit found no P0-P3 issue.
[ADR-0044](adr/0044-core-vnext-derived-signed-word-less-than.md) completes
effect-safe derived signed less-than with no new tag or public representation.
Its independent audit found no P0-P3 issue.
[ADR-0045](adr/0045-core-vnext-signed-word-comparison-flags.md) accepts the
active internal slice: canonical word-valued signed strict comparison flags
with no new tag or public representation.

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
| Internal renaming and environment simulation | Complete | Complete | Not published |
| Internal derived boolean word comparisons | Complete | Complete | Not published |
| Internal derived word comparison flags | Complete | Complete | Not published |
| Internal derived-builder arbitrary renaming laws | Complete | Complete | Not published |
| Internal direct unary primitive interface | Complete | Complete | Not published |
| Internal totalized unsigned division and modulo interface | Complete | Complete | Not published |
| Internal bounded logical shift interface | Complete | Complete | Not published |
| Internal modular word arithmetic interface | Complete | Complete | Not published |
| Internal binary bitwise logic interface | Complete | Complete | Not published |
| Internal direct word comparison interface | Complete | Complete | Not published |
| Internal word leading-zero count | Complete | Complete | Explicitly excluded from Wire v1/v2 |
| Internal word byte selection | Complete | Complete | Explicitly excluded from Wire v1/v2 |
| Internal arithmetic right shift | Complete | Complete | Explicitly excluded from Wire v1/v2 |
| Internal modular exponentiation | Complete | Complete | Explicitly excluded from Wire v1/v2 |
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

## Completed Core vNext renaming foundation

[ADR-0029](adr/0029-core-vnext-renaming-simulation.md) implements binder-aware
syntax renaming, context-respecting typing preservation, structural
`ValuesRelated`, `EnvironmentsRelated`, and `StoresRelated` relations, and
`Evaluates.rename` for every evaluation rule. `CellPayload` exactness recovers
equal ground values and typed stores, while `Evaluates.weakenAt_zero_word`
returns the same word and final store after arbitrary environment-head
insertion. Static and dynamic tests cover binders, closures, application,
cells, named data, and store effects. This proof infrastructure changes no
observable semantics or wire behavior.

## Completed Core vNext derived word comparisons

[ADR-0030](adr/0030-core-vnext-derived-word-comparisons.md) retains the existing
ADR-0011 expansions of `wordNe`, `wordLt`, `wordLe`, and `wordGe`. All four now
have named expansion, typing, inference, renaming, and weakening theorems.
`wordNe` and `wordLe` have typing-independent store-threaded evaluations;
`wordLt` and `wordGe` have typed store-threaded evaluations backed by the
renaming foundation. Eight truth cases and focused value, type, fuel, fault,
effect, Wire v1 rejection, and exact Wire v2 projection and round-trip tests
pass. The nested-let forms preserve left-to-right exactly-once behavior. No new
syntax, semantic rule, tag, or public behavior is introduced. The next
primitive or conversion is chosen by its own ADR.

## Completed Core vNext derived word comparison flags

[ADR-0031](adr/0031-core-vnext-derived-word-comparison-flags.md) wraps the
existing boolean `wordNe`, `wordLt`, `wordLe`, and `wordGe` builders with
`boolToWord`. The four resulting flags return canonical word zero or one while
retaining left-to-right exactly-once operand evaluation, faults, effects,
stores, and fuel. Each has a builder, expansion, typing, inference, renaming,
weakening, general evaluation, and two value-case theorems. Tests cover values,
types, exact fuel, faults, effects, Wire v1 rejection, and exact Wire v2
projection and round trips. For `wordLtFlag` and `wordGeFlag`, a faulting right
variable is correctly lifted across the internal binding and observes the
completed left store. This work adds no Core or wire tag and changes no
published behavior. The next feature is selected by a separate ADR.

## Completed Core vNext derived-builder renaming backfill

[ADR-0032](adr/0032-core-vnext-derived-builder-renaming-laws.md) adds arbitrary
renaming laws for eight derived builders completed before ADR-0029: the four
boolean/word conversions, two short-circuit booleans, and two original word
comparison flags. It moves `rename_boolToWord` to the module that owns
`boolToWord`; every other law likewise lives with its builder. The `swap01`
goldens exchange free variables zero and one, and runtime witnesses evaluate
the conversion, short-circuit, and comparison-flag families in their
corresponding environments. Existing weakening laws and all semantic, fuel,
fault, effect, store, and wire behavior remain unchanged. The next feature is
selected by a separate ADR.

## Completed Core vNext direct unary primitive interface

[ADR-0033](adr/0033-core-vnext-direct-unary-primitive-interface.md) completes
the named proof and regression surface for the existing raw `boolNot` and
`wordNot` unary expressions. It adds no Expr alias or operation tag. The work
covers named typing, inference, general and value-case evaluation, arbitrary
renaming, and weakening. `Word.bitNot` has zero, maximum, and universal
involution theorems. Tests cover both boolean values, word boundaries, raw
faults, the effectful final store, exact 2/3 and 14/15 fuel, Wire v1 rejection,
and exact Wire v2 projection and round trips. Generic Safety is reused. No
alias, tag, meaning, or byte changes. The next feature is selected by a separate
ADR.

## Completed Core vNext totalized unsigned division

[ADR-0034](adr/0034-core-vnext-totalized-unsigned-division.md) completes focused
value, primitive-application, and store-threaded evaluation interfaces for the
existing raw `wordDiv` and `wordMod` operators. Zero divisors still return zero
only after numerator and divisor evaluate left to right exactly once. Four Word,
two apply, and six evaluation theorems are complete. Tests cover values including
`0 / 0` and `0 % 0`, result and operand types, raw and ordered faults, both
operand effects and final store, exact 4/5 and 28/29 fuel, Wire v1 rejection,
and exact Wire v2 projection and round trips. No alias, generic API duplicate,
tag, meaning, or byte changes. The next feature is selected by a separate ADR.

## Completed Core vNext bounded logical shift slice

[ADR-0035](adr/0035-core-vnext-bounded-logical-shifts.md) keeps raw `wordShl`
and `wordShr`, with value on the left and shift amount on the right. Six Word,
two application, and six evaluation theorems cover zero, below-256, and
at-least-256 shifts. Tests cover values 0/1/maximum, amounts 0/1/255/256/maximum,
fault and effect order, final stores, exact 4/5 and 28/29 fuel, Wire v1
rejection, and exact Wire v2 and JSON round trips. The P0-P3 audit found no
issue. No alias, tag, schema, Oracle, source, signed, or gas behavior changed.
The next feature is selected by a separate ADR.

## Completed Core vNext modular word arithmetic slice

[ADR-0036](adr/0036-core-vnext-modular-word-arithmetic.md) retains raw
`wordAdd`, `wordSub`, and `wordMul` with modulo-`2^256` results and strict
left-to-right evaluation. Eight Word facts, three application equations, and
three evaluations are complete. Tests cover normal arithmetic and all three
wrap cases, zero/one/maximum, subtraction order, types, raw and ordered faults,
effects and final stores, exact 4/5 and 28/29 fuel, Wire v1 rejection, and exact
Wire v2 Core and JSON round trips. The audit found no P0-P3 issue. No alias,
generic proof, tag, schema, or Oracle behavior changed. The next feature is
selected by a separate ADR.

## Completed Core vNext binary bitwise logic slice

[ADR-0037](adr/0037-core-vnext-binary-bitwise-logic.md) retains raw `wordAnd`,
`wordOr`, and `wordXor` with strict left-to-right, exactly-once evaluation. Nine
Word laws, three application equations, and three evaluations are complete.
Tests cover AA/CC masks and 88/EE/66 results, zero/maximum/self, types, raw and
ordered faults, effects and final stores, exact 4/5 and 28/29 fuel, Wire v1
rejection, and exact Wire v2 Core and JSON round trips. Commutativity applies
only to Word values; expressions are not swapped. The audit found no P0-P3
issue. No alias, generic proof, tag, schema, or Oracle behavior changed. The
next feature is selected by a separate ADR.

## Completed Core vNext direct word comparison slice

[ADR-0038](adr/0038-core-vnext-direct-word-comparisons.md) retains raw
`wordEq` and `wordGt`, their boolean results, and strict unsigned greater-than.
The exact eight-theorem interface—two application equations plus three
general/case evaluations per operation—is complete. Tests cover zero/one/maximum,
equal/unequal and greater/not-greater values, result and operand types, raw and
ordered faults, exactly-once effects and final stores, exact 4/5 and 28/29 fuel,
Wire v1 rejection, and exact Wire v2 Core and JSON round trips. Existing derived
helpers reuse the evaluations without semantic change. No expression alias,
Word or generic proof duplicate, tag, schema, or Oracle behavior changed. The
independent audit found no P0-P3 issue.

## Completed Core vNext word leading-zero-count slice

[ADR-0039](adr/0039-core-vnext-word-leading-zero-count.md) adds internal unary
`UnaryOp.wordClz` and `Word.clz`. The operation returns 256 for zero and
`255 - Nat.log2 value.val` otherwise. The exact eleven-theorem interface is five
Word laws, one application equation, and five store-threaded evaluations; all
are complete.
Tests cover 0, 1, 2, `2^255`, maximum, types, the raw fault, exactly-once effects
and final store, exact 2/3 and 14/15 fuel, and rejection by both frozen Wire
versions. The public Oracle and schemas remain unchanged. The independent audit
found no P0-P3 issue.

## Completed Core vNext word byte-selection slice

[ADR-0040](adr/0040-core-vnext-word-byte-selection.md) adds internal
`BinaryOp.wordByte` and `Word.byteAt(index, value)`. Left is index and right is
value; index zero is the most significant byte, 31 the least significant, and
indices at least 32 return zero. The exact nine-theorem interface is five Word
laws, one application equation, and three store-threaded evaluations; all are
complete. Tests
cover `0x1122` indices 0/29/30/31/32/maximum, zero/maximum values, types, raw
and ordered faults, both effects and final store, exact 4/5 and 28/29 fuel, and
frozen Wire v1/v2 plus v2-operation rejection. Public Oracle, schema, and JSON
formats remain unchanged. The independent audit found no P0-P3 issue.

## Completed Core vNext arithmetic-right-shift slice

[ADR-0041](adr/0041-core-vnext-arithmetic-right-shift.md) adds internal
`BinaryOp.wordSar` and `Word.shiftArithmeticRight(value, shift)`. Core evaluates
value then shift exactly once. The exact eleven-theorem interface—five Word
laws, one application equation, and five store-threaded evaluations—is complete.
Tests cover
positive, high-bit, maximum, negative, and oversized shifts; types; raw and
ordered faults; both effects and final store; exact 4/5 and 28/29 fuel; and
frozen Wire v1/v2 plus v2-operation rejection. Future source `(shift, value)`
elaboration must bind source-order evaluation before reordering bound values.
Public Oracle, schema, and JSON formats remain unchanged. The independent audit
found no P0-P3 issue.

## Completed Core vNext modular-exponentiation slice

[ADR-0042](adr/0042-core-vnext-modular-exponentiation.md) adds internal
`BinaryOp.wordPow` and `Word.pow(base, exponent)`. Core evaluates base then
exponent exactly once. A square-and-multiply helper halves the exponent and is
proved equal to exponentiation modulo `2^256`; `0^0 = 1`. Its iterations remain
inside one CEK primitive step. The exact fourteen-theorem interface—eight Word
laws, one application equation, and five evaluations—is complete. Tests cover
small, boundary, maximum, and huge exponents; types; raw and ordered faults;
effects and final store; exact 4/5 and 28/29 fuel; and frozen Wire v1/v2 plus
v2-op rejection. Public formats remain unchanged. The independent audit found
no remaining P0-P3 issue; the next primitive or conversion is selected by a
separate ADR.

## Completed Core vNext signed-greater-than slice

[ADR-0043](adr/0043-core-vnext-signed-word-greater-than.md) fixes a boolean
two's-complement comparison basis. Values below `2^255` are nonnegative and
values at or above it are negative. Same-sign operands use unsigned order;
cross-sign order places every nonnegative value above every negative value.
Core evaluates left then right exactly once. The exact eleven theorems and
value, type, raw and ordered-fault, effect, final-store, exact 4/5 and 28/29
fuel, and frozen-Wire rejection tests are complete. Public formats are
unchanged; the independent audit found no P0-P3 issue.

## Completed Core vNext derived signed-less-than slice

[ADR-0044](adr/0044-core-vnext-derived-signed-word-less-than.md) fixes the
nested-let `Expr.wordSlt` expansion. Source left evaluates before source right,
each exactly once; the computed values alone are reversed for `wordSgt`. The
five static and five evaluation theorems fix variable zero as the computed
right value and variable one as the computed left value. Values and types,
underlying invalid faults, ordered faults, effects and final store, 10/11 and
34/35 fuel, and frozen v1/v2 builder, handwritten expansion, and `wordSgt`
rejections are complete. Public formats are unchanged; independent audit is
clean with no P0-P3 issue.

## Active Core vNext signed comparison flag slice

[ADR-0045](adr/0045-core-vnext-signed-word-comparison-flags.md) derives
`wordSgtFlag` and `wordSltFlag` by applying `boolToWord` to the existing signed
boolean comparisons. True becomes word one and false becomes word zero. Source
left remains before source right, with only `wordSlt`'s bound values reversed.
The exact twenty-theorem and value/type, fault-order, effect/store, fuel, and
frozen-Wire regression scope is active. Public behavior remains unchanged.

## Meaning of completion

A Core feature is complete only when its declarative rules, total executable
checker and evaluator, correspondence proofs, safety coverage, negative and
boundary tests, and version-isolation behavior agree. Publication is a later,
separate decision.
