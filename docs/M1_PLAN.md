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
| 16 | Totalized unsigned division and modulo | Complete | Completes focused APIs and strict zero-divisor regressions |
| 17 | Bounded logical shifts | Complete | Completes focused APIs for existing wordShl and wordShr without new syntax |
| 18 | Modular word arithmetic | Complete | Completes focused APIs for existing wordAdd, wordSub, and wordMul |
| 19 | Binary bitwise logic | Complete | Completes focused APIs for existing wordAnd, wordOr, and wordXor |
| 20 | Direct word comparisons | Complete | Completes focused APIs for existing wordEq and wordGt |
| 21 | Word leading-zero count | Complete | Adds an internal-only total unary wordClz primitive |
| 22 | Word byte selection | Complete | Adds internal big-endian byte selection with index-left/value-right order |
| 23 | Arithmetic right shift | Complete | Adds internal two's-complement wordSar with value-left/shift-right order |
| 24 | Modular exponentiation | Complete | Adds internal bounded square-and-multiply wordPow |
| 25 | Signed word greater-than | Complete | Adds an internal boolean two's-complement comparison basis |
| 26 | Derived signed word less-than | Complete | Preserves source order while reusing signed greater-than |
| 27 | Signed word comparison flags | Complete | Derives canonical word results from signed boolean comparisons |
| 28 | Signed non-strict word comparisons | Complete | Derives boolean ≤ and ≥ while preserving source order |
| 29 | Word sign extension | Complete | Adds byte-indexed two's-complement extension with explicit operand order |
| 30 | Signed division and remainder | Complete | Fixes zero, rounding, sign, and minimum-value behavior |
| 31 | Signed non-strict comparison flags | Complete | Converts the completed boolean comparisons to canonical words |
| 32 | Ternary modular arithmetic | Complete | Reduces full-precision sums and products after three ordered operands |
| 33 | Canonical runtime scalar observations | Complete | Fixes byte, address, and word representation before contract state |
| 34 | Contract frame halt outcomes | Complete | Separates return data, revert data, and parametric trap reasons before state |
| 35 | Strict Address↔Word bridge | Complete | Adds lossless widening and a strict partial inverse before contract state |
| 36 | Strict 20-byte Address representation | Complete | Fixes exact big-endian bytes and strict width before contract state |
| 37 | Address text and byte coherence | Complete | Proves the completed strict representations agree without a new API |
| 38 | Minimal Account and WorldState carrier | Complete | Fixes explicit absence and canonical storage values before transitions |
| 39 | Frame-outcome WorldState resolution | Complete | Selects working/checkpoint state while leaving trap disposition open |
| 40 | WorldState observational update algebra | Complete | Proves extensionality and independent-update algebra without new operations |
| 41 | WorldState storage-write algebra | Complete | Lifts overwrite, commutation, and zero deletion through conditional writes |
| 42 | External-checkpoint frame run result | Complete | Pairs speculative working state with outcome under caller-owned checkpoint |
| 43 | Parametric frame effect journal policy | Complete | Separates rollback-scoped state from surviving opaque trace snapshots |
| 44 | Synchronized frame state/effect resolution | Complete | Resolves state and effects from one shared frame outcome |
| 45 | Synchronized child-frame composition | Complete | Proves child return/revert followed by parent rollback without a stack API |
| 46 | Unresolved trap propagation | Complete | Proves that trapped synchronized resolution remains `none` through any continuation |
| 47 | Resolved frame continuation laws | Complete | Passes returned/reverted synchronized pairs to arbitrary continuations without a new API |
| 48 | Caller-owned frame continuation | Complete | Names the resolver/bind seam while checkpoint and accumulated-trace inputs stay external |
| 49 | Caller-owned frame continuation context | Complete | Groups one completed frame's continuation inputs without defining a full frame |
| 50 | Total frame resolution result | Complete | Preserves payloads and trap reasons in a total first-order result |
| 51 | Ordered frame trace algebra | Complete | Defines opt-in finite chronological extension without fixing event kinds |
| 52 | Frame trace prefix relation | Complete | Makes ordered trace consistency an explicit proof obligation without claiming provenance |
| 53 | Trace-prefixed frame continuation context | Complete | Binds prefix evidence to one context's exact checkpoint/working traces |
| 54 | Indexed frame trace extension | Complete | Generates canonical prefix evidence through event-only incremental construction |
| 55 | Parent-indexed frame continuation context | Complete | Binds a completed context's checkpoints and trace prefix to an exact parent working pair |
| 56 | Parent-indexed frame continuation construction | Complete | Derives the indexed context and proofs from an event-only trace extension |
| 57 | Parent-indexed trapped-frame rollback selection | Complete | Selects a frame-local parent rollback pair for traps while leaving propagation and transactions open |
| 58 | Parent-indexed trap propagation payload selection | Complete | Constructs one opt-in caller-designated prospective enclosing payload while leaving handling and transactions open |
| 59 | Parent-indexed trap propagation payload coherence | Complete | Inverts successful selection and carries existing non-strict prefix evidence without adding execution |
| 60 | Heterogeneous frame-outcome trap-reason mapping | Complete | Maps only reason types while preserving return/revert payloads and leaving policy caller-owned |
| 61 | Heterogeneous frame-run-result trap-reason mapping | Complete | Preserves working state while lifting the completed outcome mapping, without adding runtime propagation |
| 62 | Heterogeneous frame-resolution-result trap-reason mapping | Active | Preserves selected state, effects, and bytes while mapping only the total result's trapped reason |
| 63 | Recursion and divergence | Blocked | Requires a deliberate change to termination and resource claims |
| 64 | Nested invocation, transaction, and external observations | Planned | Needs checkpoint creation, scheduling, diagnostics, and atomicity decisions after the current frame-local foundations |
| 65 | ABI and storage layout | Planned | Follows accepted layout and admissibility decisions |
| 66 | Resolved static semantics and elaboration adapters | Planned | Connects stabilized source syntax last |

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

## Completed Core vNext slice: totalized unsigned division

[ADR-0034](adr/0034-core-vnext-totalized-unsigned-division.md) keeps `wordDiv`
and `wordMod` as raw binary operators. Named zero and nonzero value, exact
primitive-application, and store-threaded evaluation results expose their
existing behavior. A zero divisor does not skip either operand: numerator and
divisor retain left-to-right effects, faults, final stores, and fuel. Four Word,
two apply, and six evaluation theorems are complete. Tests cover zero, one, and
maximum boundaries, `0 / 0` and `0 % 0`, types and raw faults, both operand
effects, exact 4/5 and 28/29 fuel, Wire v1 rejection, and exact Wire v2
projection and round trips. No alias, generic API duplicate, tag, Safety rule,
or Wire encoding changes. The next feature is selected by a separate ADR.

## Completed Core vNext slice: bounded logical shifts

[ADR-0035](adr/0035-core-vnext-bounded-logical-shifts.md) retains raw
`wordShl(value, shift)` and `wordShr(value, shift)`. Core evaluates value then
shift exactly once; amounts at least 256 return zero. Six Word, two application,
and six evaluation theorems are complete. Tests cover 0/1/maximum values,
0/1/255/256/maximum amounts, types, faults, effects, final stores, exact 4/5 and
28/29 fuel, Wire v1 rejection, and exact Wire v2 and JSON round trips. The final
audit found no P0-P3 issue. No alias, tag, generic proof duplicate, source rule,
arithmetic shift, opcode, or gas meaning was added. The next feature is selected
by a separate ADR.

## Completed Core vNext slice: modular word arithmetic

[ADR-0036](adr/0036-core-vnext-modular-word-arithmetic.md) retains raw
`wordAdd`, `wordSub`, and `wordMul` and their modulo-`2^256` results. Eight Word
identity and boundary facts, three application equations, and three
store-threaded evaluations form the exact fourteen-theorem interface. Core
evaluates left then right exactly once; commutative values never justify
swapping effectful expressions, and subtraction remains left minus right.
Normal arithmetic and three wrap cases, 0/1/maximum, types, raw and ordered
faults, effects, final stores, exact 4/5 and 28/29 fuel, and v1/v2 Core plus JSON
round trips pass. The audit found no P0-P3 issue. No alias, generic proof
duplicate, tag, schema, Oracle, checked/signed/source/opcode/gas rule changed.
The next feature is selected by a separate ADR.

## Completed Core vNext slice: binary bitwise logic

[ADR-0037](adr/0037-core-vnext-binary-bitwise-logic.md) retains raw `wordAnd`,
`wordOr`, and `wordXor`. Nine Word laws, three application equations, and three
store-threaded evaluations form the exact fifteen-theorem interface. Core
evaluates left then right exactly once; Word commutativity never swaps effectful
expressions. AA/CC masks and 88/EE/66 results, zero/maximum/self, types, raw and
ordered faults, effects, final stores, exact 4/5 and 28/29 fuel, and v1/v2 Core
plus JSON round trips pass. The audit found no P0-P3 issue. No alias, generic
proof duplicate, tag, schema, Oracle, source or standard-library API, opcode, or
gas rule changed. The next feature is selected by a separate ADR.

## Completed Core vNext slice: direct word comparisons

[ADR-0038](adr/0038-core-vnext-direct-word-comparisons.md) retains raw
`wordEq` and `wordGt`, boolean results, strict unsigned greater-than, and
left-to-right exactly-once evaluation. Two application equations and six
general/case evaluation theorems form the completed eight-theorem interface.
Zero/one/maximum values, equality and order cases, types, raw and ordered
faults, effects, final stores, exact 4/5 and 28/29 fuel, and v1/v2 Core plus
JSON round trips pass. Existing derived comparison proofs reuse the helpers.
No expression alias, Word duplicate, generic
typing/inference/renaming/weakening/Safety proof, tag, signed/source API,
opcode, or gas rule changed. The independent audit found no P0-P3 issue; the
next feature is selected by a separate ADR.

## Completed Core vNext slice: word leading-zero count

[ADR-0039](adr/0039-core-vnext-word-leading-zero-count.md) adds internal
`UnaryOp.wordClz` and total `Word.clz` with fixed 256-bit meaning. Zero returns
256; nonzero values return `255 - Nat.log2 value.val`. Five Word laws, one
application equation, and five store-threaded evaluations complete the exact
eleven-theorem interface. The 0/1/2/high-bit/maximum, typing, raw-fault,
exactly-once effect, final-store, exact 2/3 and 14/15 fuel, and frozen Wire v1/v2
rejection tests pass. No public Oracle or schema changed. The independent audit
found no P0-P3 issue; the next feature is selected by a separate ADR.

## Completed Core vNext slice: word byte selection

[ADR-0040](adr/0040-core-vnext-word-byte-selection.md) adds internal
`BinaryOp.wordByte` and `Word.byteAt(index, value)`. Index is left, value is
right, and Core evaluates them in that order exactly once. Big-endian indices
0 through 31 select bytes; larger indices return zero. Five Word laws, one
application equation, and three store-threaded evaluations complete the exact
nine-theorem interface. Value/type/fault/effect/store boundaries,
exact 4/5 and 28/29 fuel, and frozen Wire v1/v2 rejection including the v2
operation conversion pass. No public Oracle, schema, JSON, source, ABI, opcode,
or gas rule changed. The independent audit found no P0-P3 issue; the next
feature is selected by a separate ADR.

## Completed Core vNext slice: arithmetic right shift

[ADR-0041](adr/0041-core-vnext-arithmetic-right-shift.md) adds internal
`BinaryOp.wordSar` and `Word.shiftArithmeticRight(value, shift)`. Core evaluates
value then shift exactly once and preserves the final store. Five Word laws,
one application equation, and five store-threaded evaluations complete the exact
eleven-theorem interface. Positive/negative and bounded/oversized results,
types, raw and ordered faults, both effects, exact fuel, and frozen Wire plus
v2-operation rejection pass. A future source `(shift, value)` elaborator must
bind effects in source order before reordering bound values. Public formats
remain unchanged. The independent audit found no P0-P3 issue; the next feature
is a separate ADR.

## Completed Core vNext slice: modular exponentiation

[ADR-0042](adr/0042-core-vnext-modular-exponentiation.md) adds internal
`BinaryOp.wordPow` and `Word.pow(base, exponent)`, with base evaluated before
exponent exactly once. The bounded square-and-multiply helper halves exponent
at each recursion and is proved correct modulo `2^256`. Its work remains one
CEK primitive step. Eight Word laws, one application equation, and five
evaluations complete the exact fourteen-theorem interface. Value, type, raw and
ordered-fault, effect, store, exact-fuel, and frozen Wire plus v2-operation
rejection tests pass. Public Oracle, schema, JSON, source, ABI, opcode, and gas
rules remain unchanged. The independent audit found no remaining P0-P3 issue;
further primitives are planned one closed ADR at a time.

## Completed Core vNext slice: signed word greater-than

[ADR-0043](adr/0043-core-vnext-signed-word-greater-than.md) adds internal
boolean `BinaryOp.wordSgt`. Words at or above `2^255` are negative. Same-sign
operands use unsigned order; nonnegative words are above negative words. Raw
Core evaluates left then right exactly once. Signed less-than and word flags
remain separate future slices, and frozen Wire versions reject the new tag.
The exact eleven-theorem interface and value, type, raw and ordered-fault,
effect, store, exact 4/5 and 28/29 fuel, and frozen-Wire rejection tests are
complete. Public formats are unchanged; the independent audit found no P0-P3
issue.

## Completed Core vNext slice: derived signed word less-than

[ADR-0044](adr/0044-core-vnext-derived-signed-word-less-than.md) derives
boolean `Expr.wordSlt` from `wordSgt` with two nested bindings. Source left is
evaluated before source right, each exactly once; only their bound values are
reordered for comparison: variable zero is right and variable one is left. Five
static and five evaluation theorems, value/type boundaries, underlying invalid
and ordered faults, effects/final store, exact 10/11 and 34/35 fuel, and frozen
v1/v2 rejection are complete. No primitive or public Wire tag is added; public
behavior is unchanged; the independent audit found no P0-P3 issue.

## Completed Core vNext slice: signed word comparison flags

[ADR-0045](adr/0045-core-vnext-signed-word-comparison-flags.md) wraps boolean
signed greater-than and the effect-safe signed less-than builder with
`boolToWord`. True becomes word one and false becomes word zero. The exact
ten static and ten evaluation theorems cover conditional same-sign and constant
cross-sign results. Values/types, both-side invalid and ordered faults,
effects/final store, exact 7/8, 31/32, 13/14, and 37/38 fuel, and frozen v1/v2
builder, handwritten, and `wordSgt` rejection are complete. It adds no operation
tag or public behavior; the independent audit found no P0-P3 issue.

## Completed Core vNext slice: signed non-strict word comparisons

[ADR-0046](adr/0046-core-vnext-signed-word-nonstrict-comparisons.md) derives
boolean signed ≤ and ≥ by negating the existing strict comparisons. Source
left-to-right evaluation and the final store remain intact; only `wordSge`'s
computed bound values are reversed. Ten static and ten evaluation theorems,
value/type, invalid and ordered-fault, effect/final-store, exact 6/7, 30/31,
12/13, and 36/37 fuel, and frozen v1/v2 rejection regressions are complete.
Focused/full builds, tests, kernel policy, and metadata verification pass. No
new operation tag or public behavior is added; the independent audit found no
P0-P3 issue. The next feature is selected by a separate ADR.

## Completed Core vNext slice: word sign extension

[ADR-0047](adr/0047-core-vnext-word-sign-extension.md) adds internal
`BinaryOp.wordSignExtend(index, value)`. Index is evaluated before value.
Indices below 32 select an 8-, 16-, through 256-bit signed low-order width;
indices at least 32 preserve the original value. Five Word laws, one application
equation, and four evaluations form the completed exact ten-theorem interface.
Indices 0, 1, 31, 32, and maximum, values and types, raw and ordered faults,
effects/final store, exact 4/5 and 28/29 fuel, and frozen v1/v2 rejection are
covered. Focused/full builds, tests, kernel policy, and metadata verification
pass. Public formats, source syntax, ABI, opcode, and gas rules remain
unchanged; the independent audit found no P0-P3 issue. The next feature is
selected by a separate ADR.

## Completed Core vNext slice: signed division and remainder

[ADR-0048](adr/0048-core-vnext-signed-word-division.md) adds internal
`BinaryOp.wordSdiv(dividend, divisor)` and `BinaryOp.wordSmod(dividend,
divisor)`. Both operands evaluate left to right exactly once. Division uses
magnitudes and rounds toward zero; remainder takes the dividend's sign. Zero
divisors return zero after evaluation, while minimum divided by negative one
wraps to minimum with remainder zero. Six Word laws, two application equations,
and six evaluations form the completed exact fourteen-theorem interface. Four
sign combinations of 7 and 3, zero and minimum/negative-one boundaries, types,
raw and ordered faults, effects/final store, exact 4/5 and 28/29 fuel, and
frozen v1/v2 rejection are covered. Focused/full builds and tests, kernel
policy, and metadata verification pass. Public formats, source syntax, ABI,
opcode, and gas rules remain unchanged; the independent audit found no P0-P3
issue. The next feature is selected by a separate ADR.

## Completed Core vNext slice: signed non-strict comparison flags

[ADR-0049](adr/0049-core-vnext-signed-word-nonstrict-comparison-flags.md)
derives `wordSleFlag = boolToWord(wordSle)` and
`wordSgeFlag = boolToWord(wordSge)`. Each produces canonical word one or zero.
Source left remains before source right; only `wordSgeFlag`'s computed bound
values are swapped. Ten static and ten evaluation theorems form the completed
exact twenty-theorem interface. Canonical word one/zero, same-sign, cross-sign,
and equality values, types, underlying and ordered faults, effects/final store,
exact 9/10 and 33/34 `wordSleFlag` fuel, exact 15/16 and 39/40 `wordSgeFlag`
fuel, and frozen v1/v2 builder and handwritten-expansion rejection plus v2
`wordSgt` rejection are covered. Focused/full builds and tests, kernel policy,
and metadata verification pass. Public formats and source, ABI, opcode, and gas
rules remain unchanged; the independent audit found no P0-P3 issue. The next
feature is selected by a separate ADR.

## Completed Core vNext slice: ternary modular arithmetic

[ADR-0050](adr/0050-core-vnext-ternary-modular-arithmetic.md) adds dedicated
`TernaryOp.wordAddMod`, `TernaryOp.wordMulMod`, and `Expr.ternary`. Operands
evaluate first, second, then modulus, each exactly once. A zero modulus returns
zero after all three evaluations; a nonzero modulus reduces the full-precision
natural sum or product without pre-wrapping at 256 bits. Six Word laws, two
application equations, and six evaluations form the exact fourteen focused
theorems. Generic typing, checking, Safety, correspondence, renaming,
dedicated `invalidTernaryOperands`, ordered faults and effects/final store,
exact 6/7 and 42/43 fuel, no-prewrap values, and frozen v1/v2 rejection are
complete. Public formats and source, ABI, opcode, and gas rules remain
unchanged; the independent audit found no P0-P3 issue.

## Completed runtime-foundation slice: canonical scalar observations

[ADR-0051](adr/0051-canonical-runtime-scalars.md) adds internal `Bytes`,
160-bit `Address`, and existing-Word representations independently of source
syntax and contract state. Their strict lowercase `0x` text preserves exact
widths and byte order; Word also has an exact 32-byte big-endian form. Exactly
sixteen focused theorems establish lengths, round trips, canonicality,
injectivity, and agreement with `Word.byteAt`.

Executable tests cover empty and boundary values, leading and trailing zero
bytes, strict decoder rejection, accepted-input canonicalization, a complete
32-byte big-endian fixture and `Word.byteAt` checks, and
representative equality with frozen Wire v1/v2 Word text. Those Wire codecs
remain unchanged. The layer is available through the internal semantics
umbrella but adds no profile, Oracle behavior, contract state, ABI, hashing,
storage, or source rule. The independent audit found no P0-P3 issue.

## Completed runtime-foundation slice: contract frame outcomes

[ADR-0052](adr/0052-contract-frame-outcomes.md) defines an internal halt kind
and a `FrameOutcome TrapReason`. Return and revert carry canonical `Bytes`;
trap carries a reason whose type is deliberately left to later semantics.
Projections expose only the payload belonging to the selected kind, so empty
bytes remain different from an absent projection.

The completed implementation contains the carrier, four total observations,
exactly six focused laws, and 10 executable runtime assertions. Tests cover
empty and zero-padded return and revert data, all kinds, matching and
nonmatching projections, two distinct trap reasons, and constructor
distinction. Focused and full builds and tests, trust-zero, semantic-kernel,
metadata, axiom, document-link, and diff checks pass; the independent audit
found no P0-P3 issue. State, rollback, calls, entry and ABI rules, evaluator
limits, EVM revision, and every public format remain later decisions.

## Completed strict address and word bridge slice

[ADR-0053](adr/0053-strict-address-word-bridge.md) fixes the next small
syntax-independent conversion boundary. An address widens to a word with the
same natural-number value. A word narrows to an address only when it is below
`2^160`; larger words are rejected rather than truncated or reduced modulo the
address width.

The completed implementation contains two conversions, exactly six focused
axiom-free laws, and exactly 10 executable runtime assertions. Tests cover
zero, one, a nontrivial middle value, the maximum address, and rejection of
both `2^160` and the maximum Word. Focused and full builds and tests,
trust-zero, semantic-kernel, metadata, axiom, document-link, and diff checks
pass; the independent audit found no P0-P3 issue. Source casts, ABI behavior,
Core operations, contract state, rollback, and every public format remain
separate work.

## Completed strict address byte slice

[ADR-0054](adr/0054-strict-address-bytes.md) fixes exactly 20
most-significant-byte-first octets for Address. Decoding rejects every other
width rather than padding or truncating. The two conversions, exactly
six laws, and exactly 10 runtime assertions are complete. Tests cover leading
zeros, zero, one, a nontrivial middle value, the maximum address, 19- and
21-byte rejection, and all 20 widened-Word suffix indices for all four
representatives. Laws one through five report `propext` and `Quot.sound`; law
six additionally reports `Classical.choice`. There are no custom axioms or
`sorryAx`. Focused and full checks pass, and the independent audit found no
P0-P3 issue.

Address text, the numeric Address↔Word bridge, source casts, ABI behavior,
contract state, EVM rules, and every public format remain unchanged.

## Completed Address representation coherence slice

[ADR-0055](adr/0055-address-representation-coherence.md) adds no executable API.
It proves that canonical Address text is exactly the text of its 20-byte
big-endian encoding and that the direct and byte-mediated decoders agree for
all input strings. Fifteen private helpers, exactly four public laws, and eight
runtime assertions cover canonical boundaries, 19/20/21-byte inputs, and
malformed or noncanonical text.

The slice changes no codec, ABI or source rule, contract state, EVM behavior,
or public format. All four public laws report `propext`, `Classical.choice`, and
`Quot.sound`; no custom axiom or unchecked declaration is present. Trust-zero,
focused and full builds and tests, semantic-kernel, and metadata checks pass.
The independent audit found no P0-P3 issue.

## Completed minimal WorldState slice

[ADR-0056](adr/0056-minimal-world-state.md) introduces exactly two public
carriers backed by private semantic lookup functions and eight public
operations. Finite Word and Address domains retain finite partial-map meaning
without choosing a concrete map representation. WorldState preserves Account
absence. Account storage contains no zero entries: missing keys read as zero,
zero writes erase, and nonzero writes insert. A storage write to an absent
Account fails instead of creating it.

The exact twelve laws and twelve runtime assertions cover all same-key,
different-key, same-address, different-address, and absent-Account boundaries.
Rollback, transactions, ABI, balances, nonce, code, logs, calls, creation,
layout, ordering, serialization, and public formats remain outside the slice.

Account's private lookup and zero-free proposition and WorldState's private
lookup are the complete carrier data. Constructors and fields remain private;
there is no concrete map, `BEq`, `DecidableEq`, or `Repr`. Privacy, recursor,
trust-zero, build, test, metadata, and semantic-kernel checks pass. The final
independent audit found no P0-P3 issue.

## Completed frame-outcome state-resolution slice

[ADR-0057](adr/0057-frame-outcome-world-state-resolution.md) provides exactly one
internal selector with three constructor laws and three runtime assertions.
Return selects working state, revert selects the supplied checkpoint, and trap
remains unresolved. It owns neither snapshot creation nor nested rollback and
does not decide surviving logs, calls, creations, transaction atomicity, ABI,
Core-result adaptation, EVM behavior, or gas.

The operation, exact three laws, and exact three runtime assertions are
implemented. The 24-line definition, 32-line properties, and 53-line test
modules plus two runner lines pass focused and full validation. Each law reports
only `[propext]`, with no custom axiom or unchecked declaration.

## Completed WorldState observational update algebra

[ADR-0058](adr/0058-world-state-observational-update-algebra.md) adds no
operation, carrier, or instance. It provides exactly six public laws, two
compile-time theorem-use examples, and four runtime assertions for extensional
equality, overwrite, and distinct-key commutation. The commutation laws remain
outside the simp set. This is proof coverage for ADR-0056, not selection of the
next operational state-transition slice.

The 31-line extensionality and 66-line algebra modules add exactly six public
laws and no executable API, carrier, or instance. The 76-line test module plus
two runner lines supplies the exact two compile-time and four runtime checks.
All six laws report `[propext, Quot.sound]`; focused, full, trust-zero, kernel,
metadata, forbidden-declaration, and independent audit checks pass.

## Completed WorldState storage-write algebra

[ADR-0059](adr/0059-world-state-storage-write-algebra.md) adds no executable
operation, carrier, or instance. It provides one private helper, exactly four
laws, and four runtime assertions for overwrite, distinct-slot and
distinct-address commutation, and zero deletion with Account presence
preserved. `Option.none` retains only its absent-Account meaning. This derived
proof slice selects no operational transition, rollback, ABI, EVM, or gas
policy.

The 189-line properties module and one umbrella import contain the exact four
laws. Overwrite alone is simp; commutation and zero deletion are non-simp. The
94-line definition-only test module plus two runner lines supplies four runtime
assertions. Axiom, trust-zero, build, test, metadata, kernel, forbidden, and
independent audit checks pass.

## Completed external-checkpoint frame run result

[ADR-0060](adr/0060-external-checkpoint-frame-run-result.md) provides exactly one
public carrier with intentional `working` and `outcome` fields and one named
resolver. The external checkpoint is supplied only when resolving. Exactly
three constructor laws and three runtime assertions cover returned, reverted,
and trapped results. Nested frames, effects, transactions, ABI, Core adaptation,
trap taxonomy, EVM, and gas remain separate decisions.

The 28-line definition and 32-line properties modules are each connected by one
umbrella import. The carrier intentionally exposes two fields and generated
structure surface, while adding no instance, extensionality law, or helper. All
three simp/rfl laws and the resolver report `[propext]`. The 68-line
definition-only test module plus two runner lines supplies exactly three
projection-aware checks.

## Completed parametric frame effect policy

[ADR-0061](adr/0061-frame-effect-journal-policy.md) provides one public carrier with
opaque rollback and trace snapshots and one resolver. Exactly five laws and five
runtime assertions cover constructors and the two child/parent revert
compositions. This fixes trace survival without selecting concrete effects,
ordering, append behavior, nested invocation, or transaction semantics.

The 32-line definition and 57-line properties modules each have one umbrella
import. Exactly five axiom-free laws split into three simp constructor rules and
two non-simp nested rules. The 64-line definition-only test module plus two
runner lines supplies five runtime assertions. Full checks and independent
P0-P3 audits pass.

## Completed synchronized frame state/effect resolution

[ADR-0062](adr/0062-synchronized-frame-state-effect-resolution.md) provides one
resolver and no carrier, instance, or helper. Exactly five laws include three
constructor equations and two projection-coherence equations; three runtime
assertions exercise both projections with distinct WorldState and Nat fixtures.
Nested child composition, trace ownership, concrete effects, ordering, and
transaction semantics remain separate.

The 27-line definition and 78-line properties modules each have one umbrella
import. The resolver and all five laws report `[propext]`; the laws split into
three simp constructor and two non-simp projection rules. A 66-line
definition-only test module plus two runner lines supplies three checks. No
carrier, instance, helper, or next operational policy is introduced.

## Completed synchronized child-frame composition

[ADR-0063](adr/0063-synchronized-child-frame-composition.md) adds no carrier,
operation, instance, or helper. Exactly two non-simp laws and two runtime
assertions compose child return or revert with a later parent revert. The trace
is an already-accumulated snapshot containing the parent prefix; no append or
ordering rule is introduced. Concrete invocation and trap handling remain
separate decisions.

The 47-line properties module and one umbrella import provide two non-simp,
`rfl` laws with `[propext]`. The 74-line definition-only test module plus two
runner lines provides two intermediate-and-final projection checks. No carrier,
API, instance, helper, or next operational policy is introduced.

## Completed unresolved trap propagation

[ADR-0064](adr/0064-unresolved-trap-propagation.md) adds no carrier, executable
API, instance, or helper. Its proof-only scope is exactly one non-simp law:
binding an arbitrary continuation after trapped synchronized resolution still
produces `none`. A 26-line properties module plus one umbrella import provides
that `rfl` law with `[propext]`. One assertion in a 34-line definition-only
test module plus two runner lines uses a sentinel continuation and confirms
that it is not invoked.

The implementation commits contain 122, 27, and 36 changed lines; this
completion update is the fourth commit. Full validation and independent P0-P3
audits pass. No next operational slice is activated here.

This does not choose checkpoint or working state, effect rollback, trace
survival, fatal-error handling, or transaction behavior. Those operational
decisions remain separate.

## Completed resolved frame continuation laws

[ADR-0065](adr/0065-resolved-frame-continuation-laws.md) fixes exactly two
non-simp equations for binding arbitrary Option continuations after returned
and reverted synchronized resolution. The continuation receives the same
WorldState and effect journal selected by the existing resolver. With
ADR-0064, the proof boundary covers all three FrameOutcome constructors.

The slice adds no carrier, executable operation, instance, or helper. A 44-line
properties module plus one umbrella import contains exactly two non-simp `rfl`
laws with axiom sets `[propext]`. A 61-line definition-only test module plus two
runner lines supplies exactly two sentinel assertions. The three implementation
commits contain 147, 45, and 63 changed lines; this completion update is the
fourth commit. Full validation and independent P0-P3 audits pass.

It does not choose checkpoint creation, trace accumulation or order,
invocation ownership, transactions, or trap disposition.

## Completed caller-owned frame continuation

[ADR-0066](adr/0066-caller-owned-frame-continuation.md) adds exactly one
higher-order operation. It resolves a raw FrameRunResult with caller-supplied
state/effect checkpoints and an already-accumulated working trace, then binds
an arbitrary Option continuation to the selected pair.

A 25-line definition module plus one umbrella import supplies the operation. A
59-line properties module plus one umbrella import supplies exactly three simp
`rfl` laws, all with axiom set `[propext]`. A 71-line definition-only test
module plus two runner lines supplies exactly three runtime assertions. The
four implementation commits contain 149, 26, 60, and 73 changed lines; this
completion update is the fifth commit. Full validation and independent P0-P3
audits pass.

No parent-frame carrier, checkpoint creation, trace append/order, transaction
atomicity, or diagnostic failure carrier is selected.

## Completed caller-owned frame continuation context

[ADR-0067](adr/0067-caller-owned-frame-continuation-context.md) adds one nominal
carrier with four public fields: state checkpoint, effect checkpoint, working
journal, and the existing FrameRunResult. One operation delegates to ADR-0066,
so the carrier adds no new branch behavior.

A 35-line definition module plus one umbrella import contains the four-field
carrier and operation. A 23-line properties module plus one umbrella import
contains exactly one non-simp `rfl` coherence law. The carrier, operation, and
law report `[propext]`. An 87-line definition-only test module plus two runner
lines supplies exactly three runtime assertions.

The four implementation commits contain 171, 36, 24, and 89 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. Checkpoint lineage, trace-prefix proofs, full frame identity,
stack/depth, and transactions remain outside.

## Completed total frame resolution result

[ADR-0068](adr/0068-total-frame-resolution-result.md) adds one total
three-constructor carrier and one operation from FrameContinuationContext.
Return and revert preserve their bytes with the selected state/effect pair;
trap preserves its reason and selects no pair.

A 43-line definition module plus one umbrella import contains the carrier and
operation. A 50-line properties module plus one umbrella import contains
exactly three simp `rfl` laws. A 77-line definition-only test module plus two
runner lines supplies exactly three assertions. The carrier, operation, and
laws report `[propext]`.

The four implementation commits contain 198, 44, 51, and 79 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. Trap disposition, checkpoint lineage, trace construction,
nested scheduling, and transaction atomicity remain outside.

## Completed ordered frame trace algebra

[ADR-0069](adr/0069-ordered-frame-trace-algebra.md) adds one constructor-private
FrameTrace carrier with four operations: empty, chronological observation,
tail record, and earlier-before-later append. It specializes the existing
generic trace parameter only when a consumer opts in.

A 37-line definition module plus one umbrella import contains the carrier and
operations. A 65-line properties module plus one umbrella import contains
exactly seven axiom-free laws. An 87-line definition-only test module plus two
runner lines supplies exactly six assertions.

The four implementation commits contain 210, 38, 66, and 89 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. Concrete events, trace lineage, call scheduling, rollback
filtering, and transaction ownership remain separate.

## Completed frame trace prefix relation

[ADR-0070](adr/0070-frame-trace-prefix-relation.md) adds one non-strict
proposition: an earlier trace is a prefix of a later trace exactly when some
ordered fragment extends it to the later value.

A 16-line definition module plus one umbrella import contains the relation. A
37-line properties module plus one umbrella import contains exactly four
non-simp, axiom-free laws. A 41-line definition-only compile-regression module
plus one main test import contains exactly four examples and no runtime call.

The four implementation commits contain 165, 17, 38, and 42 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. The relation proves sequence factorization, not runtime
ancestry, checkpoint ownership, or child-frame identity.

## Completed trace-prefixed frame continuation context

[ADR-0071](adr/0071-trace-prefixed-frame-continuation-context.md) refines the
existing continuation context only when its trace state is `FrameTrace`. A
proposition-valued field binds the checkpoint-prefix proof to the exact two
journals inherited by that value. Existing continuation and total-resolution
operations remain usable through the inherited context, so this slice adds no
alias or duplicate branch law.

The proof is required when the refined context is constructed and is not
checked during execution. The 21-line carrier module plus one umbrella import
adds no operation or named theorem. A 52-line definition-only regression module
plus one main test import supplies exactly three private examples and no runtime
call. The three implementation commits contain 174, 22, and 53 changed lines;
full validation and independent P0-P3 audits pass.

This slice does not infer trace provenance, checkpoint ownership, parent/child
identity, nested scheduling, trap policy, or transaction rollback.

## Completed indexed frame trace extension

[ADR-0072](adr/0072-indexed-frame-trace-extension.md) introduces an indexed
builder from one fixed earlier trace. After `start`, the only extension input is
one event; callers cannot pass an arbitrary `FrameTrace` as a hidden fragment.
The complete trace and its canonical prefix evidence remain available for
constructing ADR-0071 contexts.

The completed surface is one constructor-private carrier, three executable
operations, one canonical prefix theorem, and two observation laws. The
definition and properties modules contain 43 and 34 lines with one umbrella
import each; all declarations are axiom-free. A 71-line definition-only test
module plus two runner lines covers start, chronological recording, duplicates,
and integration with the refined continuation context.

The four implementation commits contain 206, 44, 39, and 73 changed lines.
Full validation and independent P0-P3 audits pass. Provenance, checkpoint
ownership, child transitions, and transactions remain separate.

## Completed parent-indexed frame continuation context

[ADR-0073](adr/0073-parent-indexed-frame-continuation-context.md) packages a
completed ADR-0071 context with equality between its state/effect checkpoints
and one parent working pair used as a type index. It adds no resolver alias;
inherited total resolution remains the executable path.

The 22-line carrier module plus one umbrella import adds no operation. A
66-line properties module plus one umbrella import publishes exactly three
non-simp laws. The carrier and all three laws report exactly `[propext]`. A
101-line definition-only test module plus two runner lines uses ADR-0072's
canonical event-only construction path in exactly three branch assertions.

The four implementation commits contain 216, 23, 67, and 103 changed lines.
Full validation and independent P0-P3 audits pass. Invocation provenance,
stack scheduling, trap disposition, and transactions remain later.

## Completed parent-indexed frame continuation construction

[ADR-0074](adr/0074-trace-extension-parent-context-construction.md) adds one
constrained `fromTraceExtension` operation. The parent working pair, working
rollback value, ADR-0072 extension, and frame result determine the checkpoint
pair, complete working trace, prefix proof, and checkpoint equality.

The definition and properties modules contain 31 and 58 lines with one umbrella
import each. Exactly four simp `rfl` projection laws report `[propext]`. An
87-line definition-only test module plus two runner lines contains exactly
three construction assertions.

The four implementation commits contain 217, 32, 59, and 89 changed lines.
Full validation and independent P0-P3 audits pass. ADR-0073's prefix and
return/revert laws remain reusable without adapters. Invocation provenance,
stack scheduling, trap disposition, and transactions remain later.

## Completed parent-indexed trapped-frame rollback selection

[ADR-0075](adr/0075-parent-indexed-trap-rollback-selection.md) adds one
opt-in `trapRollback?` selector. It returns `none` for return and revert. For a
trap it selects parent checkpoint state and rollback while retaining the
accumulated internal working trace.

The definition and properties modules contain 30 and 56 lines with one umbrella
import each. Exactly three non-simp laws report `[propext]`. An 84-line
definition-only test module plus two runner lines contains exactly three branch
assertions.

The four implementation commits contain 226, 31, 57, and 86 changed lines.
Full validation and independent P0-P3 audits pass. This is a new narrow
frame-local trace-retention policy, not a reinterpretation of ADR-0061 or a
concrete-log rule. Generic resolvers remain unchanged; propagation, fatality,
resumption, and transactions remain later.

## Completed parent-indexed trap propagation payload selection

[ADR-0076](adr/0076-parent-indexed-trap-propagation-payload.md) adds one
opt-in `trapPropagationPayload?` operation. It maps ADR-0075's selected pair to
a `FrameRunResult` with the original trapped outcome plus the selected journal.

The definition and properties modules contain 24 and 56 lines with one umbrella
import each. Exactly three non-simp laws report `[propext]`, as do the selector
and its generated equation. A 91-line definition-only test module plus two
runner lines contains exactly three branch assertions. The trap assertion
distinguishes designated enclosing and working state and rollback values,
checks the exact parent-then-nested trace, and preserves one concrete reason.

The four implementation commits contain 224, 25, 57, and 93 changed lines.
Full validation and independent P0-P3 audits pass. The operation constructs one
caller-designated prospective enclosing payload but does not execute or prove
propagation, parent execution, ancestry, handling, repetition through
ancestors, or transaction behavior.

## Completed parent-indexed trap propagation payload coherence

[ADR-0077](adr/0077-parent-indexed-trap-propagation-payload-coherence.md) adds
no executable operation or carrier. It specifies one non-simp iff law for
recovering the reason and complete selected payload shape, plus one non-simp
law carrying ADR-0073's existing non-strict trace-prefix proof to the selected
journal.

The 58-line properties module plus one umbrella import contains both laws;
each reports `[propext]` and is not a simp rule. A 78-line compile-only test
module plus one runner import contains exactly two private examples covering
both iff directions, the complete payload shape, prefix recovery, and the exact
parent-then-nested trace.

The three implementation commits contain 209, 59, and 79 changed lines. Full
validation and independent P0-P3 audits pass. The laws characterize pure value
selection only; they do not prove propagation occurred, introduce runtime
ancestry, execute a parent, handle a trap, or choose transaction behavior.

## Completed heterogeneous frame-outcome trap-reason mapping

[ADR-0078](adr/0078-heterogeneous-frame-outcome-trap-reason-mapping.md) adds one
pure `mapTrapReason` operation below the payload layers. A caller-supplied
function changes trapped reasons between arbitrary types while return and
revert keep their exact byte payloads.

A 22-line definition module and a 51-line properties module each add one
umbrella import. Exactly five axiom-free simp laws cover all constructors,
identity, and composition. A 64-line definition-only test module plus two
runner lines contains exactly three runtime assertions.

The four implementation commits contain 227, 27, 52, and 66 changed lines.
Full validation and independent P0-P3 audits pass. No Functor instance,
observer coherence, frame-result or payload lifting, reason classification,
ancestry, propagation, or transaction behavior is included.

## Completed heterogeneous frame-run-result trap-reason mapping

[ADR-0079](adr/0079-heterogeneous-frame-run-result-trap-reason-mapping.md)
adds one `FrameRunResult.mapTrapReason` operation above ADR-0078. It copies the
result's working state unchanged and applies the caller's mapper only through
`FrameOutcome.mapTrapReason`.

The 20-line definition module and 57-line properties module add one umbrella
import each. Exactly five simp laws cover construction, both projections,
identity, and composition; all report `[propext]`. The 83-line definition-only
test module plus two runner lines contains exactly three branch assertions with
distinct working-state values, exact return/revert bytes, and one exact mapped
trap reason.

The four implementation commits contain 235, 21, 58, and 85 changed lines.
Full validation and independent P0-P3 audits pass. This slice does not resolve
state, map effects or traces, construct a payload, or claim runtime propagation.

## Active heterogeneous frame-resolution-result trap-reason mapping

[ADR-0080](adr/0080-heterogeneous-frame-resolution-result-trap-reason-mapping.md)
adds one planned `FrameResolutionResult.mapTrapReason` operation. It maps only
the trapped reason and preserves exact state, effects, and bytes in the return
and revert constructors.

The planned proof surface is exactly five simp laws: three constructor
equations, identity, and composition. Three definition-only runtime assertions
will observe distinct state, effect, byte, and reason witnesses. The slice does
not rerun resolution, map a context or payload, or choose propagation or
transaction behavior.

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
