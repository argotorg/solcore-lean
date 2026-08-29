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

The completed ADR-0050 slice introduces dedicated ternary modular arithmetic.
`wordAddMod` and `wordMulMod` evaluate first value, second value, then modulus,
and reduce the full-precision natural sum or product without an earlier
256-bit wrap. A zero modulus still evaluates all three operands before
returning zero. Typing, checking, correspondence, Safety, renaming, exact fuel,
and frozen-Wire rejection are complete; the independent audit found no P0-P3
issue.

### Contract runtime

Contract runtime semantics are being built as explicit, independent layers.
The current internal path can select checked Core code from a working
WorldState and read or update one separately selected working-storage Account.
Balances, calls, transaction inputs, logs, created contracts, authorization,
commit, and rollback remain outside that execution path.

WorldState is distinct from the Core-local cell store. Local cells use
transient locations owned by one Core execution; storage requests use 256-bit
slots in the selected Account. A storage write changes the returned working
context but does not by itself commit a transaction or modify the checkpoint.
Neither layer obtains meaning from compiler output or hidden host state.

ADR-0052 fixes the first contract-frame halt carrier before that state exists.
A frame returns bytes, reverts with bytes, or traps with a reason whose type is
supplied by later semantics. Kind and payload projections keep empty data
distinct from an absent payload. Exactly six laws characterize the kind and
successful payload projections. This completed carrier does not define an
evaluator, state transition, checkpoint, rollback policy, trap taxonomy, or
resource-limit result.

ADR-0053 specifies a strict bridge between the existing scalar types without
adding contract state. An address zero-extends to a word with the same numeric
value; a word becomes an address only when it is below `2^160`. Overflow is
explicit failure, never truncation or modulo reduction. This completed internal
bridge has two executable definitions and six axiom-free laws. It does not
define a source cast, ABI decoding, a Core operation, or a public observation.

ADR-0054 specifies the corresponding strict byte view. An address has exactly
20 most-significant-byte-first octets, and decoding rejects every other width.
Its bytes agree with indices 12 through 31 of the completed widened Word view.
The completed internal slice has two definitions and six proved laws. It adds
no ABI padding, source conversion, state, or published observation.

ADR-0055 connects the two completed Address representations without adding a
new codec. Canonical 40-digit text equals the text of exact 20-byte encoding,
and both decoder paths agree for arbitrary input text. This proof-only
layer is complete without a public executable API and changes no ABI, state, or
publication boundary. Its independent audit found no P0-P3 issue.

ADR-0056 completes the first explicit world-state foundation with two public
carriers. Their private data consists of semantic lookup functions over the
finite Word and Address domains.
WorldState distinguishes an absent Account from a present empty Account.
Account storage contains only nonzero entries: missing keys read as zero and a
zero write erases the entry without deleting the Account. This completed slice
has no transaction, rollback, balance, code, call, or serialization meaning.
Its final independent audit found no P0-P3 issue.

ADR-0057 adds the minimal seam between frame outcomes and explicit state. A
return selects the working WorldState, a revert selects the supplied checkpoint,
and a trap produces no resolved state until a later trap policy is chosen. The
completed operation has exactly three constructor laws and three runtime
assertions. It does not own checkpoints or define nested rollback.

ADR-0058 derives an observational update algebra from ADR-0056 without adding
an operation or carrier. Extensionality hides private lookup representation;
same-key updates overwrite, while distinct-key Account writes and WorldState
puts commute. The commutation laws deliberately are not simplification rules.
The completed proof-only layer adds no executable API, carrier, or instance;
its six laws and six compile-time/runtime regressions expose no representation.

ADR-0059 lifts that algebra through the partial `WorldState.writeStorage?`
operation. Sequential overwrite and independent writes are derived with
`Option.bind`; zero deletion keeps the Account present. An absent-address
`none` gains no halt, revert, trap, or rollback meaning.
The completed layer adds no executable API, carrier, or instance; its four laws
and four definition-only runtime assertions expose no private representation.

ADR-0060 adds a public semantic payload containing a frame's speculative
working WorldState and halt outcome. The caller continues to own the checkpoint;
one resolver delegates to ADR-0057. This adds no nested-frame, effect-journal,
transaction, ABI, or EVM meaning.
The completed carrier intentionally exposes only its working state and outcome;
the generated constructor, projections, and recursor add no hidden payload.

ADR-0061 separates rollback-scoped frame effects from an opaque accumulated
trace that survives revert. Return keeps the working journal; revert combines
checkpoint rollback state with working trace; trap remains unresolved. Nested
laws describe composition without introducing a frame stack or event order.
The completed carrier and resolver have five axiom-free laws and five runtime
assertions; rollback and trace contents remain fully parametric.

ADR-0062 synchronizes WorldState and effect-journal resolution by matching one
FrameOutcome once. Its projection laws recover the existing independent state
and effect resolvers. It adds no result carrier, child composition, event order,
or transaction meaning.
The completed resolver and all five laws report only `propext`; three runtime
assertions exercise both synchronized projections.

ADR-0063 proves two-stage child/parent composition without an execution stack.
Whether the child returns or reverts, a later parent revert restores parent
WorldState and rollback effects while preserving the child's already-accumulated
trace snapshot. No trace append or event order is chosen.
The completed proof-only layer adds no carrier or operation; its two rfl laws
and two runtime assertions preserve the same opaque trace convention.

ADR-0064 completes the next proof boundary: once synchronized resolution yields
`none` for a trapped frame, binding any continuation still yields `none`. The
proof-only slice adds no carrier or operation. Its one non-simp `rfl` law
reports `[propext]`, and one sentinel runtime assertion covers the same path.
It deliberately leaves rollback,
trace, fatal-error, and transaction handling undecided.

ADR-0065 completes the matching continuation equations for returned and reverted
frames. Each equation passes the pair already selected by synchronized
resolution to an arbitrary Option continuation. The proof-only slice adds no
operation and leaves checkpoint creation, trace accumulation, and invocation
ownership undecided.

ADR-0066 completes the first executable caller-owned continuation boundary. It
resolves one raw frame result with caller-supplied checkpoints and an
already-accumulated working trace, then invokes an arbitrary Option
continuation only for return or revert. It adds no parent-frame carrier,
checkpoint creation, trace append, or transaction policy.

ADR-0067 completes a nominal `FrameContinuationContext` that groups the four
ADR-0066 inputs belonging to one completed frame. It reuses `FrameRunResult`
rather than duplicating working WorldState or outcome, and delegates
continuation behavior unchanged. The bundle proves no checkpoint lineage or
trace-prefix relation and is not a complete execution frame.

ADR-0068 completes a total `FrameResolutionResult`. Return and revert retain
their payloads together with the selected WorldState and effects; trap retains
its reason without selecting state or effects. This avoids the Option
continuation's diagnostic ambiguity while leaving trap disposition and
transaction policy unresolved.

ADR-0069 completes an opt-in `FrameTrace Event` extension algebra. It observes a
finite chronological event sequence, records at the tail, and appends an
earlier trace before a later fragment. Event kinds remain parametric and the
generic `FrameEffectJournal` remains unchanged; trace lineage, call scheduling,
and transaction ownership are still separate.

ADR-0070 completes a non-strict `FrameTrace.IsPrefixOf` relation. It records that
a later trace factors into an earlier trace followed by some fragment. This is
a value-level proof obligation for future frame transitions, not evidence of
runtime ancestry, checkpoint ownership, or parent/child identity.

ADR-0071 completes the refined continuation boundary. It attaches prefix
evidence to the exact checkpoint and working traces stored in one inherited
`FrameContinuationContext`. Existing continuation and total-resolution
operations remain reusable without aliases. The proof is a construction-time
invariant, not a runtime provenance check; nested invocation and checkpoint
ownership remain undecided.

ADR-0072 completes the indexed trace-extension boundary. It holds one
earlier trace fixed and accepts only individual events after construction, so a
new same-typed fragment API cannot accidentally append an accumulated prefix
twice. Its canonical proof remains algebraic rather than runtime provenance.

ADR-0073 completes the parent-indexed continuation boundary. It packages a
completed trace-prefixed context with proof that its state/effect checkpoints
equal one exact parent working pair. Existing total resolution is reused;
the return and revert laws characterize that inherited resolution while
retaining trace-prefix evidence at the same index, without claiming an
invocation actually occurred.

ADR-0074 completes the restricted construction boundary for that carrier. It
accepts a parent working pair, a working rollback value, an ADR-0072 indexed
extension, and a frame result, then derives both stored proofs without proof
arguments or an ambiguous complete trace. It does not claim those inputs came
from one runtime invocation.

ADR-0075 completes the opt-in trapped-frame rollback selector. Only for a
trapped parent-indexed context, it selects checkpoint state and rollback with
the accumulated internal working trace. Existing generic resolvers remain
unchanged; propagation, fatality, resumption, and transaction disposition are
still separate.

ADR-0076 completes the parent-indexed trap-propagation payload boundary. It
maps ADR-0075's selected pair into a prospective enclosing `FrameRunResult` and
selected journal while preserving the same trapped outcome. This constructs a
value only; it neither executes nor proves runtime propagation or ancestry.

ADR-0077 completes the proof boundary for successful payload selection. It
recovers the exact trapped payload shape from a `some` equality and carries the
existing non-strict parent trace-prefix fact to that selected journal. It adds
no execution operation or runtime provenance.

ADR-0078 completes the heterogeneous trap-reason mapping boundary directly
on `FrameOutcome`. A caller-supplied pure function changes only trapped reasons;
return and revert bytes are preserved. No payload, state, effect, trace, or
runtime propagation behavior is added.

ADR-0079 completes the lift of that caller-supplied mapping to
`FrameRunResult`. The result's working state is preserved exactly and only its
outcome is delegated to ADR-0078. This remains a pure value transformation,
not state resolution, rollback, ancestry, or runtime propagation.

ADR-0080 completes the corresponding mapping boundary on the total
`FrameResolutionResult`. Return and revert preserve their selected state,
effects, and bytes; only a trapped reason changes. Resolution is not rerun.

ADR-0081 completes the lift to `FrameContinuationContext`. Its checkpoint and
working inputs remain exact, while only the contained frame result uses
ADR-0079's mapping. Continuation and resolution are not executed.

ADR-0082 completes the proof that context mapping commutes with total
resolution. It adds no operation and changes no resolution policy; both pure
routes produce the same mapped resolution result.

ADR-0083 completes the proof that the `Option Next` value produced by
`FrameContinuationContext.continue?` is unchanged by context reason mapping.
It adds no operation and makes no claim about evaluation cost, step count, or
exactly-once invocation.

ADR-0084 completes the lift of reason mapping to the trace-prefix refined
context. The base context changes through ADR-0081 while both traces and the
existing prefix evidence remain exact.

ADR-0085 completes the final lift to the parent-indexed context. Its refined
base changes through ADR-0084 while the `parentWorking` index and checkpoint
equality remain exact. This is an adapter, not a nested-runtime transition.

ADR-0086 completes the nominal checkpoint-snapshot boundary. One
caller-supplied synchronized state/effect pair can be represented by a
distinct type without claiming entry time, ownership, provenance, or a
runtime transition. Existing raw-pair resolution APIs remain unchanged.

ADR-0087 completes the structural pairing boundary. One ADR-0086 snapshot
is stored beside an independent synchronized working pair without a relation
proof, custom operation, lifecycle claim, or execution transition.

ADR-0088 completes the pure adapter from that pair plus a caller-supplied
outcome into the existing continuation context. It assembles values without
claiming that a frame ran or that the outcome arose from its working state.

ADR-0089 completes the bytes-aware continuation seam on total resolution
results. Separate return and revert callbacks receive the exact selected
state/effects and bytes; traps remain unresolved as `none`.

ADR-0090 completes the proof that this richer result-level continuation reduces
to the existing context continuation when both callbacks are identical and
explicitly ignore return and revert bytes.

ADR-0091 completes the proof that heterogeneous trap-reason mapping is
unobservable to the same bytes-aware result callbacks. It adds no operation or
runtime transition.

ADR-0092 completes the conditional lift of strict WorldState storage writes to
only the working state in a checkpointed pair. The checkpoint and working
journal stay exact; the address remains caller-selected.

ADR-0093 completes the next storage-scope boundary: one caller-designated
storage address is retained beside checkpointed working values and supplies
delegated writes without becoming a current-contract or authorization claim.

ADR-0094 completes the corresponding WorldState read boundary. Account absence
is `none`; every slot in a present Account is `some value`, with missing or
deleted slots observed as `some zero`.

ADR-0095 completes the lift of that read through the retained storage address
and the working WorldState. The checkpoint remains outside the read path.

ADR-0096 completes the proof that conditional storage writes and subsequent
reads agree at the selected slot and preserve independent slots and addresses.

ADR-0097 completes the proof-only lift of the same-slot and different-slot cases
through the retained-address working carrier. No new operation or address role
is introduced.

ADR-0098 completes a pure parent-indexed initialization recipe. The caller
supplies initial WorldState and rollback values; the recipe derives a trace
extension at the parent trace and a checkpointed working pair whose checkpoint
is the exact parent pair.

ADR-0099 completes canonical wiring from that initialization recipe to the
existing retained-storage-address carrier. The supplied address remains only a
selector for the established working-storage operations.

ADR-0100 completes a proof-only sequential algebra at the address-parameterized
checkpointed working-write layer. Overwrite reduces to the final write, while
independent slot and address writes commute as pure optional-value equations;
this makes no runtime action-order or transaction claim.

ADR-0101 completes the fixed-selector specialization of same-slot overwrite and
distinct-slot commutation. It reuses the generic algebra and adds no new
address input, identity, authority, or runtime-order meaning.

ADR-0102 proves stage-preserving structural observations of that conditional
write. Successful results retain the exact selector, checkpoint, and working
effect journal; Account absence remains `none` rather than becoming a default.

ADR-0103 proves the coherence boundary between that retained-address writer
and its underlying address-parameterized values writer. Projecting successful
results to their values removes only the wrapper and preserves failure exactly.

ADR-0104 proves whole-context coherence between the two pure construction
routes out of parent-indexed initialization. Forgetting the proof-refined
parent context yields the same plain continuation context as the checkpointed-
working-pair adapter when both receive the same caller-supplied outcome.

ADR-0105 accepts a snapshot-local refinement of an address-bound working pair
whose retained Account is present. It stores the exact original context,
selected Account, and working-lookup evidence without creating an Account or
assigning authority to the retained address.

ADR-0106 accepts a total slot read on that refinement. It reads the stored
Account directly and proves agreement with the earlier conditional context
read, without another WorldState lookup or absence branch.

ADR-0107 accepts a total slot write on the same refinement. It synchronously
updates the stored Account, selected working-state entry, and presence evidence
while retaining the selector, checkpoint, and working journal.

ADR-0108 accepts the direct observations of that total write: the written slot
reads back the new value, while every distinct slot keeps its prior total read.

ADR-0109 accepts the total-write algebra on the refined carrier: a later write
to the same slot supersedes an earlier one, and writes to distinct slots commute.

ADR-0110 accepts non-selected Account isolation: a total write through the
refined carrier preserves the working WorldState lookup at every other address.

ADR-0111 accepts the total-write data projections: selector, checkpoint, and
working journal are preserved, while the stored Account receives the exact
lower-level storage update.

ADR-0112 accepts sparse storage presence after a total write: zero deletes the
slot entry, while a nonzero word produces the corresponding present value.

ADR-0113 accepts sparse storage preservation at every other slot. The base
Account law and its proven-present carrier lift complete the representation
truth table for one write without changing the automatic simplification policy.

ADR-0114 accepts canonical re-refinement after an optional write. Binding the
failure-aware write into present-Account refinement returns the same complete
carrier as the total writer, and the equality composes across later
optional-write/refinement stages.

ADR-0115 accepts canonical initialization-to-presence wiring for storage. It
checks the caller-supplied selector in `initialWorld`, which becomes the derived
working WorldState, and returns the existing proven-present carrier only when
that Account exists.

Completed ADR-0116 established optional closed checked code and exact WorldState
Address selection. ADR-0118 later supersedes that Account carrier with
host-checked code; the pure carrier and its completion theorem remain separate.

Completed ADR-0117 established the first typed Core host suspension with
storage read. ADR-0119 extends that same runtime-only capability table without
adding Core expression syntax:

- `storageRead : word -> word` returns a Word;
- `storageWrite : (word × word) -> unit` receives slot and value as one product;
- dependent `HostRequest.Response` selects Word for a read and Unit for a write;
- resumption preserves the saved CEK continuation and Core-local store.

Core owns request typing, suspension, resumption, machine safety, and fuelled
execution. It does not import Account, WorldState, Address, or frame semantics.
The frozen Core Wire v1/v2 formats reject both internal host-function values.

ADR-0118's read-only loop is now a historical foundation. ADR-0119 separates a
request-generic `HostDriver` from the combined storage handler. A read returns
the current working-storage value without changing the context. A write uses
the existing proven-present total writer, immediately updates the returned
working context, and resumes Core with Unit. Checked runs remain typed and
cannot expose a machine fault.

Address-selected execution keeps two roles explicit: `codeAddress` selects
checked code from the working WorldState, while `storageAddress` selects the
Account used by reads and writes. Handling preserves checked code, checkpoint,
working effects, the storage selector, and every non-selected working Account.

Every ordinary Core step and request emission costs one unit of Core fuel.
Handling, working-state update, and response injection cost no additional Core
fuel, and execution resumes with exactly the remaining budget. Therefore an
out-of-fuel result can legitimately contain an already-applied working write.
The returned context is the latest working state, not a committed transaction
result. ABI, source syntax, gas, authorization, calls, transaction atomicity,
and rollback policy remain separate decisions.

ADR-0120 closes the proof boundary around this execution model. The generic
handled-step relation can be reconstructed from every executable driver result,
and any valid relational witness replays to the exact result. Replay follows
each ordinary Core segment, request emission, dependent handler response, and
context update; it never assumes that a handler leaves its context unchanged.

A done result or raw fault is stable when more Core fuel is supplied. This is
full-result stability, so it retains the exact final context as well as the
value, local store, fault, or fault state. The combined storage driver and its
checked and successful address-selected done entry points expose the same exact
final-context guarantee, including contexts changed by writes. Out-of-fuel has
no stability theorem because a larger budget can continue execution and apply
more effects. These additions are proofs and regressions only: the driver,
runtime behavior, and read/write request kinds are unchanged.

ADR-0121 adds one read-only observation to that existing driver. The append-only
Core capability table now ends with `storageAddress : unit -> word` at index 2;
the established storage read and write capabilities remain at indexes 0 and 1.
Core still knows only Unit and Word. The combined Semantics handler losslessly
widens the retained 160-bit Address to a 256-bit Word and returns it without
changing the handler context. This request is read-only, but the driver as a
whole is not: later or earlier storage-write requests may still update its
returned working context.

The observed value means only “the retained selector used for working storage.”
It is not defined as the code address, current contract, `self`, caller, owner,
origin, or an authorized principal. Those roles may differ and require their
own lifetime and authority decisions. Additional fuel can still move an
out-of-fuel execution forward, so ADR-0121 adds no out-of-fuel stability claim.
The capability remains internal: Wire and runtime-publication formats still
reject host values, and Oracle, Surface, Parser, and public runtime schemas are
unchanged.

ADR-0126 specifies the next observation from an existing input rather than
inventing a call-frame role. The selected `codeAddress` becomes a static
parameter of the combined handler and is returned by a fourth internal
`unit -> word` capability. The high-level selected runner uses that same
Address for checked-code lookup and handler execution, so observation cannot
drift from selection. It remains distinct from the storage selector and does
not imply current-contract, caller, callee, or authority identity.

The implementation keeps that selector out of mutable WorldState. It is fixed
for one handled run, indexes the run's fuel evidence, and is threaded through
the existing continuation layers without changing their public optional
shapes. Focused tests distinguish code and storage selectors and verify exact
fuel boundaries, strict Address recovery, and completed-result stability.

ADR-0127 connects two existing consumers of a completed parent-indexed frame.
`resolveWithTrapRollback` returns the ordinary total resolution together with
the optional rollback pair already selected for traps. It is a read-only view:
the generic resolver remains reason-only on trap, no rollback is applied, and
no parent machine or transaction boundary is introduced.

Four exact branch laws characterize return, revert, trap, and successful
rollback selection. Compile consumers connect the first component to existing
bytes-aware callbacks and preserve ADR-0125's whole-context and fuel-stability
boundaries. The view introduces no new execution path or runtime fixture.

ADR-0128 completes the algebraic closure for that view. It adds no operation;
one naturality law moves heterogeneous trap-reason mapping through the first
component while proving that the rollback-selection component is unchanged.
Identity and heterogeneous composition normalize through the same rule.

ADR-0129 completes the pure elimination boundary. A total generic fold selects
one caller-owned function for return, revert, or trap and supplies the exact
values fixed by ADR-0127. The returned value has caller-selected type; the fold
does not mutate a parent or interpret rollback, bytes, or traps. Its coherence
law reconstructs the complete resolution view for all three branches.

ADR-0130 completes the algebraic closure for that fold. Its single naturality
law moves heterogeneous trap-reason mapping through the fold by precomposing
only the trap function. Return and revert functions, all resolved values, and
the caller-selected result type remain unchanged. This is a proof interface
only and introduces no execution or lifecycle layer.

ADR-0131 completes the execution-input extension. It keeps `codeAddress` and a
caller-supplied `callValue` Word in one immutable input outside the mutable
storage context. Checked Core code observes the exact Word through the
append-only `callValue : unit -> word` capability at index 4. The same input is
threaded through request handling, fuel evidence, selected completion, and
parent-indexed continuation construction. Tests carry its value-derived
working state and terminal bytes into the existing resolution fold. The
capability remains internal, frozen Wire v1 and v2 reject its host value, and
the Word does not mean that any balance transfer occurred.

ADR-0132 completes one equally narrow extension. `callerAddress : Address` is
an explicit, immutable execution input, and internal Core observes its lossless
Word through append-only `callerAddress : unit -> word` at index 5. Host tables
therefore contain six entries. The exact handler and completed-driver laws show
that caller observation does not change the complete mutable host context; it
also performs no Account lookup. Tests vary only this input, cover caller
Account absence and fuel 4/5/23/29/30/32, and carry a caller-derived write
through parent-indexed completion and the resolution fold. The supplied Address
does not identify a parent frame, authenticate a principal, define origin or
current/callee identity, or determine how a nested call supplies its caller.

ADR-0133 completes the bounded optional input-byte observation. One bounded
`InputData` value is fixed for the whole handled run, separately from mutable
storage.
Internal Core receives append-only
`inputDataByte? : word -> sum unit word` at index 6. The result uses Unit for an
absent index and Word for a present byte, so a present input byte whose value is
zero cannot be mistaken for absence. ADR-0133 itself adds no size observation,
multi-byte or Word load, endianness, padding, ABI, calldata, parser, Wire, or
public-runtime rule.

ADR-0134 completes exact-size observation over that same immutable input.
`InputData.sizeWord` uses the retained strict bound to represent the
natural byte length without truncation, and internal
`inputDataSize : unit -> word` is appended at index 7. Exact coherence makes
`inputDataByte?` present precisely below `sizeWord` and absent at or above it.
This adds no ABI or calldata meaning, multi-byte decoding, nested-call input
derivation, parser dependency, Wire tag, or public interface.

ADR-0135 is active over the same immutable input. Semantics will expose
`InputData.wordBE?` only for a complete 32-byte window, decoded with the
existing big-endian Word codec; incomplete windows are absent without padding
or offset wrap. Core will own only the optional
`inputDataWordBE? : word -> sum unit word` capability at append-only index 8,
with table length 9 and first-unbound index 9. Handler context identity,
safety, direct, storage, parent, fuel, and frozen-Wire boundaries remain proof
obligations; ABI, calldata, memory, nested calls, parser work, and publication
remain outside the slice.

ADR-0122 completes the optional selection boundary above that driver. A
successful address-selected result is equivalent to the exact selected checked
code and its fuel-indexed handled-step evidence; the evidence also replays to
the same result. Optional failure is exactly `WorldState.code? = none`. Because
selection happens before execution, an out-of-fuel outcome after successful
selection remains `some`, not a lookup failure. This is a proof interface only:
the lookup, driver, handler, address roles, and lifecycle remain unchanged.

ADR-0123 makes the generic relation usable without first converting every proof
back into an executable equality. Ordinary host paths and context-threading
handled paths compose, and handled paths preserve Core typing across dependent
responses. Sound evidence at one fuel identifies one exact full driver result.
Done and raw-fault evidence agrees across sufficient budgets, including the
exact final handler context; out-of-fuel does not, because another budget may
continue the same state and handle more requests. No new execution or lifecycle
layer is introduced.

### Observation

Observations are canonical, versioned semantic results. Contract observations
will record normative state effects rather than bytecode layout, optimizer
traces, generated names, or wall-clock behavior. Gas belongs to a separate
fork-pinned profile.

ADR-0051 provides the completed initial internal observation foundation without
publishing a profile. `Bytes`, 160-bit addresses, and existing 256-bit words
receive strict lowercase `0x` text; words also receive an exact 32-byte
big-endian view that agrees with Core byte selection. Exactly sixteen focused
theorems and executable boundary, rejection, canonicality, and compatibility
tests fix this representation behavior. The frozen Wire codecs remain separate
and unchanged. This layer defines representation only, not contract state, ABI
conversion, hashing, rollback, or EVM behavior.

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
| Solcore/Semantics | Cross-feature and internal runtime semantics |
| Solcore/Surface | Published Surface v1 |
| Solcore/Surface/Multi | Frozen internal Multi frontend |
| Solcore/Workspace | Pure workspace identity and validation |
| Solcore/Oracle | Versioned external protocols |
| schema, profiles, Tests/golden | Published compatibility artifacts |
| docs/adr | Durable semantic and architectural decisions |
