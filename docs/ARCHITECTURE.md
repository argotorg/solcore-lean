# Architecture

solcore-lean separates source representation from language meaning. This lets
the syntax evolve without forcing the executable semantics to be rewritten.

## Layers

    source text
      -> versioned Surface parser
      -> Surface-to-Resolved adapter
      -> resolved and typed semantic input
      -> Semantic Core
      -> contract runtime
      -> canonical observation

Only some of these arrows exist today. The architecture treats each arrow as a
separate executable transformation with its own declarative relation and proof
boundary.

### Surface

Surface owns concrete spelling, tokens, comments, grouping, and source spans.
The published Surface v1 parser is stable. The larger Multi parser is an
internal reference for a frozen grammar.

Surface data is not semantic identity. A source span cannot stand in for a
declaration, scope, variable, function, or module identity.

### Resolved input

Resolved input will replace source spellings with structured identities and
will make scope ownership and module selection explicit. Its contract should
depend on abstract declarations and occurrences, not on a particular parser
implementation.

No executable Resolved language exists yet. During the semantics-first phase,
Core and runtime work must not depend on the unfinished Multi AST.

### Semantic Core

Semantic Core is the executable language definition. It owns:

- value and type algebras;
- declarative typing;
- big-step dynamic semantics;
- a deterministic CEK-style machine;
- executable inference, checking, and evaluation;
- correspondence between relations and executors; and
- progress, preservation, and fault-exclusion results.

The existing Core v2 fragment is closed and published. New features extend the
internal Core additively. Old wire languages remain projections and must
reject new constructors.

Core vNext includes local mutation through explicit typed cells. Cell
references are ordinary internal values, while the local store is a separate
component of evaluation and machine state. Closures capture references in
their lexical environments; they do not copy the store. This makes sharing
explicit and keeps the semantics independent of host-language mutation.

The completed initial cell slice stores only first-order data: unit, boolean,
word, and products or sums made recursively from those types. Function-valued
and cell-valued contents wait for the recursion-and-divergence decision because
higher-order cells can encode nontermination.

The completed named-data slice gives each internal Core program an immutable
definition table. A data type is identified by its position in that table; a
constructor is identified by its owning type and position within that type.
These are local semantic identities, not source names. Definitions may be
recursive or mutually recursive, while runtime values remain finite.

Named-data matching is a normalized Core operation. Its branch list is
exhaustive and follows constructor-table order, and the selected constructor's
single payload becomes de Bruijn index zero. An explicit result type also
supports elimination of an empty data type. Source wildcards, nested patterns,
guards, arm ordering, names, and field shapes belong to a later resolved
adapter, not this execution layer.

The completed boolean/word conversion slice is deliberately smaller than an
algebra extension. `boolToWord` expands to a conditional selecting word zero or
one, and `wordToBool` expands to a nonzero test built from existing primitives.
The operand occurs once in either expansion. Because there is no new expression
tag, the existing evaluator, CEK machine, safety results, and wire projections
remain the architectural boundary; the slice adds named builders, focused
theorems, and tests rather than parallel semantics. Dedicated typing, inference,
evaluation, store-threading, and weakening results, plus effect, exact-fuel, and
wire regressions, are complete.

This conversion layer is not an ABI layer. Total nonzero truthiness and strict
ABI zero-or-one admissibility are separate rules. ABI byte layout, validation,
decoding, and rejection remain in the future contract boundary.

The completed `wordIsZero` slice follows the same derived-expression boundary.
It has type `word -> word`, returning word one for zero and word zero for every
nonzero input, and expands to existing equality and `boolToWord` expressions.
It is distinct from `wordToBool` truthiness and from ABI decoding. No new Core,
CEK, wire, or Oracle tag is added: wire v1 rejects the required primitive form,
while wire v2 projects the ordinary existing expansion.
Dedicated typing, inference, evaluation, store-threading, expansion, and
weakening theorems, plus effect, exact-fuel, type-error, boundary, and wire
regressions, complete this proof boundary.

The completed short-circuit boolean slice is another derived-expression boundary.
`boolAnd(x, y)` expands to `ifE x y false`, while `boolOr(x, y)` expands to
`ifE x true y`. The left operand runs once and first; the right operand runs
only in the selected branch. This store, fault, and fuel behavior follows the
existing conditional semantics and adds no Core, CEK, wire, or Oracle tag.
Eager ordinary reference calls are comparison evidence, not authority over the
selected-branch-only decision fixed by ADR-0011 and ADR-0026.
Named expansion, typing, inference, and all four store-threaded branch theorems
are complete. Tests cover truth, operand types, skipped and selected faults,
allocation and writes, left-to-right store threading, exact fuel, weakening,
and exact wire v1 and v2 projection.

The completed `wordIsNonzero` slice composes the existing conversions as
`boolToWord(wordToBool(x))`. It maps zero to word zero and every nonzero word to
word one, evaluates `x` exactly once, and preserves its final store. It is a
word-valued predicate rather than boolean truthiness or strict ABI decoding,
and introduces no new semantic or wire tag.
Its canonical expansion, typing, inference, general and zero/nonzero
store-threaded evaluation, and weakening interfaces are complete. Value,
type/fault, 9/10 fuel, exactly-once allocation/write, distinction, and exact
v1/v2 wire tests pass with the repository audits.

The completed word-comparison-flags slice derives `wordEqFlag` and `wordGtFlag` by
converting the existing boolean equality and unsigned greater-than results to
canonical word one or zero. Operands retain left-to-right, exactly-once store
and fault behavior. Existing boolean comparisons remain unchanged, and no Core
or wire tag is added.
Named expansion, typing, inference, general and four case-specific
store-threaded evaluation, and weakening results are complete. Value, boundary,
type, fault-order, two-operand effect, exact-fuel, boolean-preservation, and
exact wire regressions pass with the repository audits.

The completed renaming foundation provides binder-aware `Expr.rename`,
context-respecting preservation of expression and branch typing, structural
relations for values, environments, and stores, and `Evaluates.rename` for all
evaluation forms. Renamed closures retain related bodies and captured
environments rather than requiring false raw equality. `CellPayload` exactness
recovers equal ground values and typed stores, and the word head-insertion
corollary preserves the exact word and final store. Static and dynamic tests
cover binders, closures, application, cells, named data, and effects. This
changes no Core execution or wire behavior.

The completed ADR-0030 slice retains the ADR-0011 definitions of `wordNe`,
`wordLt`, `wordLe`, and `wordGe`. All four provide named expansion, typing,
inference, renaming, weakening, store-threaded evaluation, and two truth-case
results. `wordNe` and `wordLe` evaluations need no typing assumptions;
`wordLt` and `wordGe` use typed store-threading. The nested-let
shape of `wordLt` and `wordGe`, including weakening the right operand under the
left binding, is part of the semantic boundary: it preserves left-to-right,
exactly-once effects and fault order. A syntax-level operand swap is not an
equivalent implementation for arbitrary expressions. This work adds proofs and
tests only; it does not add a Core form or change a wire or Oracle contract.
Tests cover values, types, exact fuel, faults, effects, Wire v1 rejection, and
exact Wire v2 projection and round trips.

The completed ADR-0031 slice applies `boolToWord` to the existing boolean
`wordNe`, `wordLt`, `wordLe`, and `wordGe` builders. These derived flags return
canonical word zero or one. They inherit left-to-right exactly-once evaluation,
fault order, effects, final stores, and fuel from the established expansions;
in particular, the nested-let less-than forms are not replaced by operand
swaps. Four general and eight case evaluations accompany expansion, typing,
inference, renaming, and weakening results. Tests cover values, types, exact
fuel, faults, effects, Wire v1 rejection, and exact Wire v2 projection and
round trips. A faulting right expression in the less-than forms is weakened
under the internal binding, so its variable index is lifted while the completed
left store is retained. No Core form, wire tag, or published behavior changes.
The next feature is selected by a separate ADR.

The completed ADR-0032 slice fills a static API gap left by the order of earlier
work. `boolToWord`, `wordToBool`, `wordIsZero`, `wordIsNonzero`, `boolAnd`,
`boolOr`, `wordEqFlag`, and `wordGtFlag` gain arbitrary renaming laws in their
owning modules. `rename_boolToWord` moves from the later derived-comparison-flag
module to `Conversions`. The non-insertion `swap01` golden exchanges free
variables zero and one; corresponding-environment evaluations cover conversion,
short-circuit, and comparison-flag witnesses. Existing weakening, evaluation,
store, fault, fuel, and wire behavior remain unchanged. The next feature is
selected by a separate ADR.

The completed ADR-0033 slice keeps boolean negation and word complement as direct
`.unary` expressions. Named typing, inference, store-threaded evaluation cases,
arbitrary renaming, and weakening theorems make the existing primitives easier
to use without adding aliases. Zero, maximum, and universal involution theorems
characterize word complement. Boundary and effect tests cover both boolean
values, exact 2/3 and 14/15 fuel, raw faults, final stores, Wire v1 rejection,
and exact Wire v2 projection and round trips. Generic Safety and machine
correspondence remain unchanged, as do semantics, tags, and bytes. The next
feature is selected by a separate ADR.

The completed ADR-0034 slice adds focused reasoning interfaces for direct unsigned
word division and modulo. The raw binary form keeps numerator on the left and
divisor on the right. A zero divisor produces zero only after both operands
evaluate exactly once in order, so effects, faults, and final stores remain
visible. Four Word, two apply, and six evaluation theorems cover normal and zero
divisors. Tests include `0 / 0`, types, raw and ordered faults, two effectful
operands, exact 4/5 and 28/29 fuel, Wire v1 rejection, and exact Wire v2
projection and round trips. Generic typing, renaming, weakening, Safety, machine
correspondence, tags, and bytes do not change. The next feature is selected by
a separate ADR.

The completed ADR-0035 slice gives the existing raw logical shifts six Word,
two application, and six store-threaded evaluation theorems. Core keeps the
value on the left and shift amount on the right, evaluates both exactly once in
that order, and returns zero for amounts of 256 or more. Boundary, fault,
effect, final-store, exact-fuel, and Wire regressions pass with no P0-P3 audit
finding. No alias, tag, duplicate generic proof, schema, or Oracle behavior
changed. Arithmetic shift, source spelling, opcode lowering, and gas remain
outside the slice; the next feature is selected by a separate ADR.

The completed ADR-0036 slice gives raw `wordAdd`, `wordSub`, and `wordMul` eight
Word, three application, and three store-threaded evaluation theorems. Results
wrap modulo `2^256`; Core evaluates left then right exactly once and retains the
right operand's final store. Subtraction is left minus right, and commutative
values do not authorize swapping expressions. Normal and wrapped values, types,
faults, effects, exact fuel, and Wire/Core/JSON round trips pass with no P0-P3
finding. No alias, generic proof duplicate, tag, schema, or Oracle behavior
changed. The next feature is selected by a separate ADR.

The completed ADR-0037 slice gives raw `wordAnd`, `wordOr`, and `wordXor` nine
Word, three application, and three store-threaded evaluation theorems. Core
evaluates left then right exactly once and retains the final store. Commutativity
is a Word-value theorem only and never swaps expressions. Mask, identity, fault,
effect, exact-fuel, and Wire/Core/JSON regressions pass with no P0-P3 finding.
No alias, generic proof duplicate, tag, schema, or Oracle behavior changed. The
next feature is selected by a separate ADR.

The completed ADR-0038 slice gives raw `wordEq` and `wordGt` two application
equations and six store-threaded general/case evaluation theorems. Both return
booleans; greater-than remains strict and unsigned. Operands evaluate left then
right exactly once, retaining the final store. Value, type, ordered-fault,
effect, exact-fuel, and Wire/Core/JSON regressions pass. Existing derived
comparison proofs reuse the helpers without semantic change. No expression
alias, Word or generic proof duplicate, tag, schema, or Oracle behavior changed.
The independent audit found no P0-P3 issue.

The completed ADR-0039 slice adds internal `UnaryOp.wordClz` and total
`Word.clz` for the 256-bit leading-zero count. Zero returns 256; nonzero values
return `255 - Nat.log2 value.val`. Five Word laws, one application equation,
and five evaluations are complete. Value, type, raw-fault, exactly-once effect,
final-store, and exact-fuel tests pass. Frozen Wire v1 and v2 both reject the
tag; public Oracle and schema formats remain unchanged. The independent audit
found no P0-P3 issue.

The completed ADR-0040 slice adds internal `BinaryOp.wordByte` and total
`Word.byteAt(index, value)`. Left is index and right is value; Core evaluates
them in that order exactly once. Five Word laws, one application equation, and
three store-threaded evaluations are complete. Value, type, raw and ordered
fault, effect, final-store, and exact-fuel tests pass. Frozen Wire v1/v2 and the
v2 operation conversion reject the tag; public Oracle/schema/JSON formats are
unchanged. The independent audit found no P0-P3 issue.

The completed ADR-0041 slice adds internal `BinaryOp.wordSar` and total
`Word.shiftArithmeticRight(value, shift)`. Raw Core evaluates value then shift
exactly once. Five Word laws, one application equation, and five evaluations
cover both signs and bounded/oversized shifts. Values, types, raw and ordered
faults, effects, final stores, and exact fuel pass. Future source
`(shift, value)` elaboration must bind source-order effects before reordering
bound values. Frozen Wire v1/v2 and the v2 operation conversion reject the tag;
public formats remain unchanged. The independent audit found no P0-P3 issue.

The completed ADR-0042 slice adds internal `BinaryOp.wordPow`, `Word.pow`, and
the proved square-and-multiply helper. Core evaluates base then exponent exactly
once. `Word.pow` supplies a 256-bit exponent, so repeated halving takes at most
256 iterations. The helper is proved equal to exponentiation modulo `2^256`,
while remaining one CEK primitive step. All fourteen focused theorems and value,
type, ordered-fault, effect, store, exact-fuel, and frozen-Wire rejection tests
pass. Public formats remain unchanged; the independent audit found no remaining
P0-P3 issue.

The completed ADR-0043 slice adds internal boolean `BinaryOp.wordSgt`. The sign
bit is bit 255. Same-sign operands retain unsigned order; nonnegative values
compare above negative values. Raw Core evaluates left then right exactly once.
Derived signed less-than and word flags are separate, and frozen public Wire
formats continue to reject the internal operation.
Its exact eleven-theorem interface and value, type, ordered-fault, effect,
store, and exact-fuel regressions are complete. Public formats are unchanged;
the independent audit found no P0-P3 issue.

The completed ADR-0044 slice derives boolean `Expr.wordSlt` with nested bindings.
Core evaluates the source left expression and then the source right expression,
weakening the latter under the first binding. Only the resulting values are
passed to `wordSgt` in right/left order. This avoids changing faults, effects,
stores, or fuel and adds no primitive or public Wire tag. Its five static and
five evaluation theorems fix variable zero as the computed right value and
variable one as the computed left value. Value/type, invalid and ordered-fault,
effect/store, exact 10/11 and 34/35 fuel, and frozen-Wire rejection regressions
are complete. Public behavior is unchanged; the independent audit found no
P0-P3 issue.

The completed ADR-0045 slice derives word-valued strict signed comparison flags.
`wordSgtFlag` wraps raw signed greater-than with `boolToWord`; `wordSltFlag`
wraps the effect-safe nested signed-less-than builder. Both preserve source
left-to-right evaluation and the final store, returning word one for true and
word zero for false. The slice adds no Word operation, Core tag, generic rule,
or public Wire representation. Ten static and ten evaluation theorems cover
same-sign conditional and cross-sign constant word-one/word-zero results.
Value/type, both-side invalid payload, ordered-fault, effect/store, exact
7/8, 31/32, 13/14, and 37/38 fuel, and frozen-Wire rejection regressions are
complete. Public behavior is unchanged; the independent audit found no P0-P3
issue.

The completed ADR-0046 slice derives boolean signed non-strict comparisons.
`wordSle` negates raw `wordSgt`; `wordSge` negates the nested, effect-safe
`wordSlt`. Both retain source left-to-right evaluation and the final store,
including equality as true. Only `wordSge` reverses already computed bound
values. Ten static and ten evaluation theorems cover same-sign order and both
cross-sign directions. Value/type, invalid and ordered-fault, effect/store,
exact 6/7, 30/31, 12/13, and 36/37 fuel, and frozen-Wire rejection regressions
pass. No Word operation, Core tag, generic rule, or public Wire form is added;
the independent audit found no P0-P3 issue.

The completed ADR-0047 slice adds internal `BinaryOp.wordSignExtend`, with the
byte index on the left and the value on the right. Its exact five Word laws,
one application equation, and four evaluation theorems cover indices 0, 1, 31,
32, and the maximum word, plus types, ordered faults, effects, final stores,
and fuel boundaries. Core evaluates index then value exactly once. Frozen
public Wire formats continue to reject the operation; the independent audit
found no P0-P3 issue.

The completed ADR-0048 slice adds internal signed division and remainder. The
dividend evaluates before the divisor. Division uses magnitude division,
rounds toward zero, and derives the quotient sign from both operands;
remainder keeps the dividend's sign. A zero divisor returns zero only after
both operands evaluate, and minimum signed word divided by negative one wraps
to the minimum word. Its exact fourteen theorems and sign, zero, type, fault,
effect/store, and fuel regressions pass. Frozen public Wire formats reject both
operations; the independent audit found no P0-P3 issue.

The completed ADR-0049 slice derives canonical word-valued signed non-strict
comparison flags. `wordSleFlag` and `wordSgeFlag` convert the existing boolean
builders to word one or zero. Source left still evaluates before source right;
only `wordSgeFlag`'s already computed bound values are swapped internally.
Its exact twenty theorems and truth, type, fault, effect/store, and fuel
regressions pass. Frozen public Wire formats reject both builders and their
expansions; the independent audit found no P0-P3 issue.

The active ADR-0050 slice introduces dedicated ternary modular arithmetic.
`wordAddMod` and `wordMulMod` evaluate first value, second value, then modulus,
and reduce the full-precision natural sum or product without an earlier
256-bit wrap. A zero modulus still evaluates all three operands before
returning zero. Frozen public Wire formats reject the ternary form.

### Contract runtime

The future runtime will make all external state explicit: storage, balances,
call frames, transaction inputs, logs, created contracts, and rollback state.
That world state is distinct from the Core-local cell store. The local store
uses transient locations for one Core execution; it does not define contract
storage keys, persistence, transaction boundaries, or rollback. Neither layer
may obtain meaning from compiler output or hidden host state.

### Observation

Observations are canonical, versioned semantic results. Contract observations
will record normative state effects rather than bytecode layout, optimizer
traces, generated names, or wall-clock behavior. Gas belongs to a separate
fork-pinned profile.

## Proof pattern

Each semantic feature follows the same vertical structure:

| Concern | Required artifact |
| --- | --- |
| Intended meaning | Independent typing and evaluation judgments |
| Execution | Total checker and explicitly state-threaded evaluator |
| Static correspondence | Checker soundness and completeness |
| Dynamic correspondence | Machine and big-step agreement |
| Safety | Progress, preservation, and typed result properties |
| Local state | Explicit store threading, typed allocation/update, and final-store agreement |
| Named definitions | Whole-table validity, stable constructor ownership, and recursive finite-value reasoning |
| Derived expressions | Expansion typing, exact result semantics, exactly-once use, and unchanged version boundaries |
| Resource behavior | Explicit fuel or a proved finite bound |
| Compatibility | Old wires reject new syntax; derived forms preserve existing projection behavior |
| Regression protection | Positive, negative, order, boundary, and version tests |

An executable function is not used as its own specification.

## Version boundaries

| Boundary | Role | Change policy |
| --- | --- | --- |
| Semantic Core v1 / Oracle v2 | Frozen historical Core | No reinterpretation |
| Semantic Core v2 / Oracle v3 | Current published Core | No reinterpretation |
| Surface v1 / Oracle v4 | Current published parser | No reinterpretation |
| Internal Multi frontend | Frozen grammar reference | No active grammar proof expansion |
| Core vNext | Active internal semantics | Additive and unpublished |

A future publication receives a new schema, profile, capability report, limits,
golden corpus, and Oracle version. Internal progress never changes an existing
profile.

## Dependency policy

Work is ordered by exposure to syntax churn:

1. Core values, typing, evaluation, and machine proofs.
2. Explicit contract state and observations.
3. Resolved static semantics over abstract identities.
4. Surface adapters and source diagnostics.
5. Concrete parser updates and grammar-specific proofs.

The first two groups can proceed while the concrete language syntax is under
revision. The final two resume only after a syntax version is deliberately
stabilized.

## Repository map

| Location | Responsibility |
| --- | --- |
| Solcore/Core | Semantic Core, its local value store, and current Core proofs |
| Solcore/Semantics | Future cross-feature and runtime semantics |
| Solcore/Surface | Published Surface v1 |
| Solcore/Surface/Multi | Frozen internal Multi frontend |
| Solcore/Workspace | Pure workspace identity and validation |
| Solcore/Oracle | Versioned external protocols |
| schema, profiles, Tests/golden | Published compatibility artifacts |
| docs/adr | Durable semantic and architectural decisions |
