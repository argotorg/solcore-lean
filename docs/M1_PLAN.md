# Semantic Core roadmap

The active goal is a syntax-independent executable semantics rich enough to
represent Solcore programs after resolution and typing. The existing published
Core remains frozen while the internal Core grows additively.

ADR-0119 completes the first address-selected execution path that can both
read and update working contract storage under one typed, fuel-preserving
driver. [ADR-0120](adr/0120-handled-execution-completeness-and-fuel-stability.md)
now completes the proof boundary around that driver: its handled-step relation
and executable result determine each other, and completed or faulted runs remain
identical when given more fuel.
[ADR-0121](adr/0121-retained-storage-address-observation.md) now completes the
retained storage-selector observation. The append-only `unit -> word`
capability at index 2 returns the existing selector losslessly and leaves its
handler context unchanged, without treating it as a current, self, code, or
caller address.
[ADR-0122](adr/0122-address-selected-handled-execution-exact-specification.md)
completes the proof-only boundary. It makes both optional branches of the current
address-selected entry point exact: successful execution is equivalent to
selected-code fuel evidence, while `none` is equivalent to the existing code
lookup returning `none`. Concrete grammar and parser proof work stays paused
until source syntax stabilizes.
[ADR-0123](adr/0123-handled-execution-relational-metatheory.md) completes the
follow-on proof slice: handled paths are compositional and directly type-safe.
All fuel-sound results are unique at one budget; done and raw-fault results are
also unique across budgets. It does not claim that out-of-fuel is stable or that
checked host code always terminates.
[ADR-0124](adr/0124-completed-handled-execution-frame-continuation.md) completes
the first lifecycle connection. It adapts only normal handled completion
through a caller-owned policy, preserves terminal frame values, and retains
nested options so code absence and selected out-of-fuel cannot be confused.
[ADR-0125](adr/0125-parent-indexed-selected-execution-continuation.md) completes
the parent-indexed lift. It also preserves storage-Account absence and
constructs the existing proof-bearing parent continuation only after normal
selected completion.
[ADR-0126](adr/0126-selected-code-address-observation.md) completes the
code-selector observation. It appends `codeAddress : unit -> word` without
moving the three existing capabilities, and uses one Address for both selected
lookup and the handler response.
[ADR-0127](adr/0127-parent-indexed-resolution-view.md) completes the
frame-local composition. It pairs existing total resolution with existing
opt-in trap rollback without claiming parent resumption or transaction commit.
[ADR-0128](adr/0128-parent-indexed-resolution-view-trap-reason-mapping-naturality.md)
completes the proof-only naturality slice for that view. It maps only trapped
reasons and preserves the exact rollback-selection component.
[ADR-0129](adr/0129-parent-indexed-trap-aware-resolution-fold.md) completes the
pure fold over the same context. Caller-owned functions receive one exact
return, revert, or trap branch without parent or transaction execution.
[ADR-0130](adr/0130-parent-indexed-resolution-fold-trap-reason-mapping-naturality.md)
completes the proof-only algebra. Heterogeneous trap-reason mapping commutes
with that fold by changing only the trap function.
[ADR-0131](adr/0131-end-to-end-call-value-observation.md) completes the
invocation-value observation. One immutable execution input now carries the
selected code Address and a caller-supplied Word through handled execution,
fuel evidence, selected completion, and parent-indexed continuation
construction. Its value-derived result reaches the existing resolution fold.
The Word is observable by internal Core code without defining a balance
transfer.
[ADR-0132](adr/0132-run-fixed-caller-address-observation.md) completes the
run-fixed caller-address observation. One explicitly supplied Address travels
unchanged with the same immutable input and is observed losslessly through
internal `callerAddress : unit -> word` at index 5. The request needs no caller
Account and leaves the complete host context unchanged. It defines no parent
identity, authentication, origin, current/callee identity, or nested-call rule.
[ADR-0133](adr/0133-bounded-optional-input-byte-observation.md) completes the
bounded optional input-byte observation. One bounded `InputData` value is part
of the immutable run input, and internal Core observes one optional byte
through `inputDataByte? : word -> sum unit word` at index 6. The Unit branch
means an absent index; the Word branch includes a present zero byte. ADR-0133
itself leaves size, wider loads, endianness, padding, ABI, calldata, syntax,
and publication separate.

[ADR-0134](adr/0134-run-fixed-input-size-observation.md) completes exact
run-fixed input-size observation. It derives the exact input length as
`sizeWord` from ADR-0133's strict bound and exposes it through internal
`inputDataSize : unit -> word` at index 7. Byte lookup is present exactly below
that size and absent at or above it. ABI, calldata, multi-byte loads,
nested-call derivation, syntax, and publication remain separate.

[ADR-0135](adr/0135-strict-optional-input-word-be-observation.md) is complete.
It adds a strict optional 32-byte big-endian window over the same run-fixed input.
Only a complete window decodes; incomplete windows return absence without
padding or Word-offset wrap. The internal host capability appends at index 8,
with table length 9 and first-unbound index 9. ABI, calldata, memory, nested
input derivation, syntax, and publication stay separate.

[ADR-0136](adr/0136-resumable-handled-fuel-slices.md) is complete. It makes an
exhausted handled run resumable from its exact returned context and Core state.
Using the same handler and, for storage execution, the same `ExecutionInputs`,
a split budget agrees with one run using the summed budget. Done and fault
remain terminal. Sequential addition is required for arbitrary result values;
zero is an identity only for actual run results, not arbitrary forged
`outOfFuel` values.

[ADR-0137](adr/0137-canonical-host-capability-registry.md) is complete. The
then-existing nine-capability order became canonical without adding a
capability or changing execution. Both tables and arbitrary-list safety derive
from the one registry. ADR-0139 has since appended index 9 while preserving the
historical indexes 0 through 8 and all public boundaries.

[ADR-0138](adr/0138-branch-complete-resumable-parent-indexed-selected-execution.md)
is complete. It introduces a branch-complete internal parent
result and resumes only retained exhaustion. The existing nested-`Option` API
stays unchanged through an explicit compatibility erasure. Parser and syntax
proofs remain paused.

[ADR-0139](adr/0139-run-fixed-current-address-observation.md) is complete. One
explicit `currentAddress` is fixed for a handled run and its same-input
resumptions, observed losslessly by Core at append-only host index 9, and kept
independent from storage, code, caller, and future callee or call-kind roles.
The canonical host tables now have length 10 and index 10 is first unbound.

[ADR-0140](adr/0140-proof-refined-parent-indexed-selected-execution-session.md)
is accepted and active, with implementation planned. It will bind the existing
selected-run configuration to a branch-complete result and certify that result
against one run at the session's cumulative provided-fuel budget. Resumption
will accept only more fuel, preventing accidental input or completion-policy
replacement. It adds no nested invocation, ABI, parser, or public boundary.

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
| 62 | Heterogeneous frame-resolution-result trap-reason mapping | Complete | Preserves selected state, effects, and bytes while mapping only the total result's trapped reason |
| 63 | Heterogeneous frame-continuation-context trap-reason mapping | Complete | Preserves all caller-owned inputs while mapping only the contained frame result |
| 64 | Frame trap-reason mapping resolution naturality | Complete | Proves that context mapping commutes with total resolution without adding execution |
| 65 | Frame trap-reason mapping continuation-result invariance | Complete | Proves equality of `continue?` result values under reason mapping without adding execution |
| 66 | Heterogeneous trace-prefixed continuation-context trap-reason mapping | Complete | Preserves the base mapper and exact trace-prefix evidence without adding provenance or execution |
| 67 | Heterogeneous parent-indexed continuation-context trap-reason mapping | Complete | Preserves the exact parent index and checkpoint equality while mapping only the refined context |
| 68 | Nominal frame checkpoint snapshot | Complete | Names a caller-supplied synchronized checkpoint pair without claiming capture, ownership, or execution |
| 69 | Frame checkpointed working pair | Complete | Stores a checkpoint snapshot beside an independent working pair without adding an operation or relation proof |
| 70 | Continuation context from checkpointed working pair | Complete | Canonically assembles every stored value plus an opaque outcome into the existing continuation context |
| 71 | Bytes-aware frame resolution continuation | Complete | Passes selected state/effects and bytes to distinct caller-owned return/revert callbacks while leaving traps unresolved |
| 72 | Frame continuation branch/byte erasure coherence | Complete | Proves the richer result route conservatively recovers bytes-insensitive context continuation |
| 73 | Frame-resolution continuation trap-reason mapping invariance | Complete | Proves heterogeneous reason mapping is invisible to the same bytes-aware callbacks |
| 74 | Checkpointed working-pair storage write | Complete | Lifts strict storage writes to only the working WorldState while retaining checkpoint and journal |
| 75 | Checkpointed working-pair storage address | Complete | Binds one caller-designated storage target to checkpointed working values and subsequent writes |
| 76 | Conditional WorldState storage read | Complete | Preserves Account absence while lifting zero-default slot reads to WorldState |
| 77 | Address-bound working storage read | Complete | Uses the retained storage address to read only the working WorldState |
| 78 | WorldState storage read/write coherence | Complete | Normalizes reads after conditional writes and preserves independent observations |
| 79 | Address-bound working storage read/write coherence | Complete | Lifts same-slot and different-slot observations through the retained selector |
| 80 | Parent-indexed frame initialization | Complete | Builds a canonical trace start and checkpointed working pair from caller-supplied initial state values |
| 81 | Initialization storage-address adapter | Complete | Connects the only input role with existing consumers to the parent-indexed initialization path |
| 82 | Checkpointed working-pair storage-write algebra | Complete | Lifts overwrite and independent-write commutation through the existing working-write operation |
| 83 | Address-bound working storage-write algebra | Complete | Specializes overwrite and distinct-slot commutation through the retained storage selector |
| 84 | Address-bound working storage-write preservation | Complete | Exposes selector, checkpoint, and working-journal preservation without collapsing write failure |
| 85 | Address-bound working storage-write values coherence | Complete | Relates wrapper write results to the existing address-parameterized values writer |
| 86 | Parent-indexed initialization continuation-context coherence | Complete | Equates the refined trace-extension route with the plain checkpointed-values route |
| 87 | Present working storage Account refinement | Complete | Bundles the exact retained-address working Account and its lookup evidence for total consumers |
| 88 | Present working storage Account total read | Complete | Reads the proven-present selected Account without another lookup or failure branch |
| 89 | Present working storage Account total write | Complete | Synchronizes the selected Account, working-state entry, and evidence without another lookup |
| 90 | Present working storage Account total read/write coherence | Complete | Normalizes same-slot and distinct-slot reads after total writes |
| 91 | Present working storage Account total-write algebra | Complete | Normalizes overwrite and commutes writes to distinct slots |
| 92 | Present working storage Account total-write isolation | Complete | Preserves every non-selected working Account across a total write |
| 93 | Present working storage Account total-write projections | Complete | Exposes the exact selector, checkpoint, journal, and updated Account projections |
| 94 | Present working storage Account total-write presence | Complete | Exposes zero deletion and nonzero sparse-entry presence |
| 95 | Present working storage Account total-write sparse preservation | Complete | Completes one-write sparse representation behavior at Account and proven-present carrier boundaries |
| 96 | Present working storage Account optional/total re-refinement coherence | Complete | Makes the failure-aware write/refine path equal the total writer and reusable across refined optional-write sequences |
| 97 | Parent-indexed initialization present storage Account refinement | Complete | Checks Account presence for the initialization-bound selector and reaches existing total storage consumers without a new carrier |
| 98 | Address-selected closed Core code | Complete, superseded at Account boundary | ADR-0116 established the pure carrier and selection laws retained as historical foundations for ADR-0118 |
| 99 | Typed Core storage-read suspension | Complete foundation | Introduces typed request/resume, exact CEK suspension, finite-run safety, and the read capability retained by ADR-0119 |
| 100 | Working-storage read handler | Complete foundation | Interprets reads through the proven-present Account; its laws are reused by the combined handler |
| 101 | Address-selected host-code driver | Complete foundation | Establishes separate code/storage selection and exact remaining-fuel reuse; its read-specific API is superseded by ADR-0119 |
| 102 | Typed storage-write and combined storage driver | Complete | Appends `(word × word) -> unit`, uses a generic driver and combined handler, and proves address-selected safety, fuel, and context invariants |
| 103 | Handled-execution completeness and terminal fuel stability | Complete | Makes the generic handled-step relation executable in both directions and proves exact done/fault stability under additional fuel |
| 104 | Retained storage-selector observation | Complete | Returns the existing storage selector as a lossless Word at index 2, with exact handler-context identity and no current, self, code, caller, or other call-frame identity |
| 105 | Address-selected handled execution exact specification | Complete | Characterizes `some` by selected-code fuel evidence and `none` by code lookup failure without changing execution |
| 106 | Handled-execution relational metatheory | Complete | Composes handled paths, proves direct type safety and fixed-fuel uniqueness, and compares only terminal results across budgets |
| 107 | Completed handled execution to frame continuation | Complete | Adapts only normal completion through a caller-owned outcome policy while preserving code absence and selected exhaustion as distinct results |
| 108 | Parent-indexed selected execution continuation | Complete | Preserves storage absence, code absence, selected exhaustion, and completion while refining only completion to the existing parent-indexed context |
| 109 | Selected code-address observation | Complete | Returns the existing code selector as a lossless Word at index 3, uses it for both lookup and execution, and keeps it distinct from the storage selector |
| 110 | Parent-indexed resolution view | Complete | Pairs total return/revert/trap resolution with opt-in trap rollback selection without applying either result |
| 111 | Resolution-view trap-reason mapping naturality | Complete | Maps only the total-resolution component and preserves exact optional rollback selection without adding an operation |
| 112 | Parent-indexed trap-aware resolution fold | Complete | Selects one pure caller-owned function for each resolved branch without applying the supplied values |
| 113 | Resolution-fold trap-reason mapping naturality | Complete | Moves heterogeneous reason mapping through the existing fold without adding execution |
| 114 | End-to-end call-value observation | Complete | Carries one explicit run-fixed Word through the internal Core request, handled execution, selected completion, and parent-indexed continuation; the value-derived result reaches the existing resolution fold without a balance-transfer claim |
| 115 | Run-fixed caller-address observation | Complete | Carries one explicit caller-supplied Address through `ExecutionInputs` and exposes its exact lossless Word at Core host index 5 without broader caller semantics |
| 116 | Bounded optional input-byte observation | Complete | Carries one bounded run-fixed `InputData` value and exposes one present byte or explicit absence at Core host index 6 |
| 117 | Run-fixed input-size observation | Complete | Derives the exact bounded input length as a Word, exposes it at Core host index 7, and proves its boundary agrees with optional byte lookup |
| 118 | Strict optional input-word BE observation | Complete | Reuses the run-fixed input, exact size boundary, and canonical Word codec for full 32-byte windows at Core host index 8 without padding |
| 119 | Resumable handled fuel slices | Complete | Resumes retained exhaustion under the same handler and exact inputs, with proved split/summed-budget equality, typed-result safety, and storage-preservation regressions |
| 120 | Canonical host capability registry | Complete | Derives both host tables and arbitrary-list safety from one extensible order, with exact finite laws and compatibility/runtime regressions |
| 121 | Branch-complete resumable parent-indexed selected execution | Complete | Retains all five exact branches, resumes only exhaustion with split/zero/add laws, and preserves the unchanged nested-`Option` and fold APIs |
| 122 | Run-fixed current-address observation | Complete | Adds the identified Core consumer and one-run lifetime without deriving storage, code, caller, callee, or call-kind relationships |
| 123 | Proof-refined parent-indexed selected-execution session | Accepted, active | Binds fixed run configuration to each result and maintains exact one-shot equality at cumulative provided fuel; implementation and proofs are planned |
| 124 | Recursion and divergence | Blocked | Requires a deliberate change to termination and resource claims |
| 125 | Nested invocation, transaction, and external observations | Planned | Needs ownership/lifetime, further active-frame transitions, scheduling, diagnostics, and transaction atomicity decisions |
| 126 | ABI and storage layout | Planned | Follows accepted layout and admissibility decisions |
| 127 | Resolved static semantics and elaboration adapters | Planned | Connects stabilized source syntax last |

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

## Completed heterogeneous frame-resolution-result trap-reason mapping

[ADR-0080](adr/0080-heterogeneous-frame-resolution-result-trap-reason-mapping.md)
adds one `FrameResolutionResult.mapTrapReason` operation. It maps only the
trapped reason and preserves exact state, effects, and bytes in the return and
revert constructors.

The 24-line definition module and 68-line properties module add one umbrella
import each. Exactly five simp laws cover the three constructors, identity,
and composition; all report `[propext]`. The 92-line definition-only test
module plus two runner lines contains exactly three assertions with distinct
state, effect, byte, and reason witnesses.

The four implementation commits contain 249, 25, 69, and 94 changed lines.
Full validation and independent P0-P3 audits pass. The slice does not rerun
resolution, map a context or payload, or choose propagation or transaction
behavior.

## Completed heterogeneous frame-continuation-context trap-reason mapping

[ADR-0081](adr/0081-heterogeneous-frame-continuation-context-trap-reason-mapping.md)
adds one context lift of ADR-0079. It copies the state checkpoint, effect
checkpoint, and working effects unchanged, then maps only the `FrameRunResult`
field.

The 27-line definition module and 87-line properties module add one umbrella
import each. Exactly seven simp laws cover construction, four projections,
identity, and composition; all report `[propext]`. The 118-line definition-only
test module plus two runner lines contains exactly three assertions observing
every field with distinct witnesses.

The four implementation commits contain 250, 32, 88, and 120 changed lines.
Full validation and independent P0-P3 audits pass. This slice does not run a
continuation or resolver, map an indexed context or payload, or choose
propagation or transaction behavior.

## Completed frame trap-reason mapping resolution naturality

[ADR-0082](adr/0082-frame-trap-reason-mapping-resolution-naturality.md) adds no
operation. Its single `[propext]` simp theorem moves a trap-reason mapper
through `FrameContinuationContext.resolve` to the ADR-0080 result mapper.

The 26-line properties module adds one umbrella import. A 34-line test module
plus one runner import contains exactly two private compile regressions for an
abstract heterogeneous mapper and two mappings reduced in the correct order to
one composed result mapping. The three implementation commits contain 175,
27, and 35 changed lines; this completion update is the fourth commit. Full
validation and independent P0-P3 audits pass. This proof-only slice does not
invoke a continuation, map an indexed context or payload, or choose runtime
propagation or transaction behavior.

## Completed frame trap-reason mapping continuation-result invariance

[ADR-0083](adr/0083-frame-trap-reason-mapping-continuation-invariance.md) adds
no operation. Its single `[propext]` simp theorem removes context reason mapping
from the `Option Next` value computed by `FrameContinuationContext.continue?`.

The 30-line properties module adds one umbrella import. A 38-line test module
plus one runner import contains exactly two private compile regressions for one
abstract heterogeneous mapper and two successive mappings converging to the
original continuation result. The three implementation commits contain 187,
31, and 39 changed lines; this completion update is the fourth commit. Full
validation and independent P0-P3 audits pass. This proof-only slice makes no
mapper-evaluation, cost, step-count, or exactly-once invocation claim and does
not map an indexed context or payload or choose runtime propagation or
transaction behavior.

## Completed heterogeneous trace-prefixed context trap-reason mapping

[ADR-0084](adr/0084-heterogeneous-trace-prefixed-frame-continuation-context-trap-reason-mapping.md)
adds one lift of ADR-0081. It maps the generated base context and directly
reuses the existing proof that the checkpoint trace prefixes the working trace.

The 27-line definition and 61-line properties modules each add one umbrella
import. Exactly four `[propext]` simp laws cover the refined constructor, base
projection, identity, and composition. A 95-line definition-only test module
plus one runner import contains exactly three private compile regressions and
no runtime call.

The four implementation commits contain 246, 28, 62, and 96 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. This slice does not map traces, parent indexing, payloads,
or choose provenance, propagation, or transaction behavior.

## Completed heterogeneous parent-indexed context trap-reason mapping

[ADR-0085](adr/0085-heterogeneous-parent-indexed-frame-continuation-context-trap-reason-mapping.md)
adds one lift of ADR-0084. It maps the trace-prefix context and directly
reuses the `parentWorking` type index and checkpoint-equality evidence.

The 29-line definition and 67-line properties modules each add one umbrella
import. Exactly four `[propext]` simp laws cover the parent-indexed constructor,
refined projection, identity, and composition. A 109-line definition-only test
module plus one runner import contains exactly three private compile regressions
and no runtime call.

The four implementation commits contain 259, 30, 68, and 110 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. This final mapper slice does not select rollback, construct
a payload, or choose provenance, propagation, nested execution, or transaction
behavior.

## Completed nominal frame checkpoint snapshot

[ADR-0086](adr/0086-nominal-frame-checkpoint-snapshot.md) adds one
`FrameCheckpointSnapshot` carrier and one `fromWorkingPair` adapter. They name
one caller-supplied synchronized state/effect pair without asserting when,
where, or by whom it was captured.

The 29-line definition and 25-line properties modules each add one umbrella
import. Exactly two `[propext]` simp laws expose the retained fields. A 47-line
definition-only test module plus one runner import contains exactly three
private compile regressions and no runtime call.

The four implementation commits contain 237, 30, 26, and 48 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. The following slice must consume this snapshot beside an
independent working pair, without assuming checkpoint/working equality or
choosing initialization order.

## Completed frame checkpointed working pair

[ADR-0087](adr/0087-frame-checkpointed-working-pair.md) adds one
carrier with an ADR-0086 checkpoint snapshot and a separate synchronized
working pair. Generated construction and projection form its complete API;
custom operations and laws are deliberately absent.

The 17-line definition module adds one umbrella import. A 53-line
definition-only test module plus one runner import contains exactly three
private compile regressions with visibly distinct checkpoint and working
state, rollback, and trace values. There is no runtime call.

The three implementation commits contain 186, 18, and 54 changed lines; this
completion update is the fourth commit. Full validation and independent P0-P3
audits pass. The following slice must consume every field through
`FrameContinuationContext.fromCheckpointedWorkingPair` plus an outcome,
without asserting execution or initialization history.

## Completed continuation-context construction from checkpointed working values

[ADR-0088](adr/0088-continuation-context-from-checkpointed-working-pair.md)
adds one pure adapter into `FrameContinuationContext`. Checkpoint state
and effects, working effects, and working state plus the caller-supplied
outcome populate the existing four fields exactly.

The 25-line definition and 47-line properties modules each add one umbrella
import. Exactly four `[propext]` simp laws expose those fields. A 68-line
definition-only test module plus one runner import contains exactly three
private compile regressions and no runtime call.

The four implementation commits contain 225, 26, 48, and 69 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. The adapter does not resolve, continue, or execute the
context.

## Completed bytes-aware frame resolution continuation

[ADR-0089](adr/0089-bytes-aware-frame-resolution-continuation.md) adds one
`FrameResolutionResult.continue?` partial dispatcher. Return and revert
use separate caller callbacks, each receiving the complete selected
state/effect pair and bytes. Trap remains `none`.

The 28-line definition and 54-line properties modules each add one umbrella
import. Exactly three generated equations and three `rfl` simp laws report
exactly `[propext]`. An 83-line definition-only test module plus one runner
import and call contains exactly three runtime assertions.

The four implementation commits contain 244, 29, 55, and 85 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. This seam preserves branch and bytes but performs no
delivery, parent update, scheduling, trap handling, or transaction transition.

## Completed frame continuation branch/byte erasure coherence

[ADR-0090](adr/0090-frame-continuation-branch-byte-erasure-coherence.md) adds
one proof-only non-simp law. When both callbacks supplied after total
resolution are the same and ignore bytes, their `Option` result equals the
existing bytes-insensitive context `continue?` result.

The 29-line properties module adds one umbrella import and reports exactly
`[propext]`. A 45-line test module plus one runner import contains exactly two
private compile regressions and no runtime call.

The three implementation commits contain 199, 30, and 46 changed lines; this
completion update is the fourth commit. Full validation and independent P0-P3
audits pass. This slice adds no operation, callback-count claim, delivery,
parent update, scheduling, trap handling, or transaction transition.

## Completed frame-resolution continuation trap-reason mapping invariance

[ADR-0091](adr/0091-frame-resolution-continuation-trap-reason-mapping-invariance.md)
adds one proof-only simp law. It removes heterogeneous trap-reason
mapping around a total result before bytes-aware continuation while retaining
the same arbitrary return and revert callbacks.

The 27-line properties module adds one umbrella import and reports exactly
`[propext]`. A 42-line test module plus one runner import contains exactly two
private compile regressions and no runtime call.

The three implementation commits contain 187, 28, and 43 changed lines; this
completion update is the fourth commit. Full validation and independent P0-P3
audits pass. This slice adds no operation, callback-count claim, delivery,
parent update, scheduling, trap handling, or transaction transition. ADR-0090
remains non-simp.

## Completed checkpointed working-pair storage write

[ADR-0092](adr/0092-checkpointed-working-pair-storage-write.md) adds one
`FrameCheckpointedWorkingPair.writeWorkingStorage?` operation. It conditionally
updates only the working WorldState through the existing strict storage rule
and retains the exact checkpoint and working effect journal.

The 20-line definition and 33-line properties modules each add one umbrella
import. The operation, generated equation, and exactly two simp laws report
exactly `[propext]`. A 98-line definition-only test module plus one runner
import and call contains exactly three runtime assertions.

The four implementation commits contain 230, 21, 34, and 100 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. The caller supplies the address. The slice adds no
authorization, account creation, checkpoint lifecycle, outcome, parent
mutation, scheduling, trap, gas, or transaction policy.

## Completed checkpointed working-pair storage address

[ADR-0093](adr/0093-checkpointed-working-pair-storage-address.md) adds one
`FrameCheckpointedWorkingPairWithStorageAddress` carrier and one
`writeStorage?` operation. The carrier stores a caller-designated storage
address beside ADR-0087 values; the operation delegates to ADR-0092 without an
address argument and retains the same selector on success.

The 34-line definition and 44-line properties modules add one umbrella import
each. Exactly two simp laws and three definition-only runtime assertions pass,
as do the full validation and independent P0-P3 audits. The address is not a
current contract, callee, code address, owner, or authorized principal. Entry,
account creation, scheduling, trap, gas, ABI, and transaction policy remain
outside the slice.

## Completed conditional WorldState storage read

[ADR-0094](adr/0094-world-state-storage-read.md) adds one
`WorldState.readStorage?` operation. It composes explicit Account lookup with
the existing zero-default Account storage read, returning `none` only when the
Account itself is absent.

The 17-line definition and 28-line properties modules each add one umbrella
import. Exactly two simp laws and three definition-only runtime assertions
pass, as do full validation and independent P0-P3 audits. The following slice
may lift this operation through the stored-address carrier; no frame, mutation,
gas, ABI, or transaction rule is added here.

## Completed address-bound working storage read

[ADR-0095](adr/0095-address-bound-working-storage-read.md) adds one
carrier-level `readStorage?` operation. It uses the retained address and the
working WorldState, then delegates account absence and zero-default slot
behavior to ADR-0094.

The 20-line definition and 37-line properties modules each add one umbrella
import. Exactly two simp laws and three definition-only runtime assertions
pass, as do full validation and independent P0-P3 audits. The checkpoint does
not participate in the read. Address authority, mutation, frame entry, gas,
ABI, and transaction policy remain outside the slice.

## Completed WorldState storage read/write coherence

[ADR-0096](adr/0096-world-state-storage-read-write-coherence.md) adds exactly
three simp laws. They characterize a read of the written slot
and preservation of a different slot or a different address.

All three theorems preserve write-stage failure through an outer `Option.map`;
the other-address case can therefore distinguish outer `none` from
`some none`. Exactly three private compile examples are present, with no
runtime declaration, assertion, or call. No executable operation is added. All
three declarations report exactly `[propext]`, and full validation plus
independent P0-P3 audits pass.

## Completed address-bound working storage read/write coherence

[ADR-0097](adr/0097-address-bound-working-storage-read-write-coherence.md)
adds exactly two simp laws. They lift ADR-0096 through the existing
retained-address carrier for the written slot and a distinct slot.

The proof keeps write failure as outer `none`; it adds no executable API,
other-address overload, checkpoint policy, or address authority. Exactly two
private compile examples and no runtime call are present. Both laws report
exactly `[propext]`, and full validation plus independent P0-P3 audits pass.

The contract-entry boundary review selected ADR-0098's payload-free
initialization layer. Address roles, invocation inputs, and outcome provenance
remain later decisions before an entry carrier is added.

## Completed parent-indexed frame initialization

[ADR-0098](adr/0098-parent-indexed-frame-initialization.md) adds one
payload-free initialization carrier. The exact parent working pair is its type
index; initial WorldState and rollback values remain explicit caller inputs.

One operation starts an indexed trace extension at the parent trace. A second
constructs the existing checkpointed working pair with the parent snapshot,
the caller's initial values, and that exact initial trace. The slice adds no
address role, call data, value, kind, event, scheduling, or execution policy.
Exactly two simp laws and three private compile regressions pass, as do the full
validation and independent P0-P3 audits.

## Completed initialization storage-address adapter

[ADR-0099](adr/0099-parent-indexed-frame-initialization-storage-address.md)
adds one operation that combines ADR-0098 initialization with a
caller-supplied storage address and returns the existing ADR-0093 carrier.

Exactly two projection laws expose the address and checkpointed working values.
No new carrier, storage behavior, authority, current-contract identity, or
other invocation input is added. Three private compile regressions cover both
projections and the existing storage-write consumer; full validation and
independent P0-P3 audits pass.

## Completed checkpointed working-pair storage-write algebra

[ADR-0100](adr/0100-checkpointed-working-pair-storage-write-algebra.md) lifts
the existing WorldState overwrite and independent-write equations through the
ADR-0092 checkpointed working-write operation.

It adds exactly three named non-simp proof laws and no executable operation.
Overwrite remains non-simp because present-Account branch reduction can visit
its first write before the surrounding bind. The equations do not claim
runtime, transaction, or external-effect reordering. Three private compile
regressions, full validation, and independent P0-P3 audits pass.

## Completed address-bound working storage-write algebra

[ADR-0101](adr/0101-address-bound-working-storage-write-algebra.md) lifts the
ADR-0100 same-slot overwrite and distinct-slot commutation laws through the
single retained storage selector.

It adds exactly two named non-simp proof laws and no executable operation.
Overwrite avoids a critical overlap with present-Account branch reduction, and
slot commutation has no canonical orientation. No distinct-address law or
runtime-order claim is added at this fixed-selector boundary. Two private
compile regressions, full validation, and independent P0-P3 audits pass.

## Completed address-bound working storage-write preservation

[ADR-0102](adr/0102-address-bound-working-storage-write-preservation.md)
lifts three immutable-field observations through the retained-address
conditional write.

The selector, checkpoint, and complete working effect journal are returned
unchanged on success, while Account absence remains the outer `none`. The
slice adds exactly three simp laws and three private compile regressions, with
no executable operation or whole-state preservation claim. All laws report
`[propext]`; full validation and independent P0-P3 audits pass.

## Completed address-bound working storage-write values coherence

[ADR-0103](adr/0103-address-bound-working-storage-write-values-coherence.md)
relates the retained-address optional write to the existing generic values
write after projecting away only the wrapper.

The single simp law keeps success and failure stages exact, enabling generic
values consumers without a new operation, carrier, address role, or runtime
claim. Two private compile regressions cover direct simplification and an
arbitrary pure consumer; the law reports `[propext]`, and full validation and
independent P0-P3 audits pass.

## Completed parent-indexed initialization continuation-context coherence

[ADR-0104](adr/0104-parent-indexed-initialization-continuation-context-coherence.md)
equates the plain base contexts produced by the existing trace-extension and
checkpointed-working-pair construction routes.

The single named non-simp law adds no constructor, frame transition, outcome
generation, or runtime policy. Two compile-only regressions cover the whole
equality and the existing `continue?` consumer. The law reports `[propext]`;
full validation and independent P0-P3 audits pass.

## Completed present working storage Account refinement

[ADR-0105](adr/0105-present-working-storage-account-refinement.md) adds one
snapshot-local carrier and one partial producer at the retained working address.

The refinement keeps Account absence explicit as `none` and stores exact
presence evidence on success. Its two simp branch laws report `[propext]`;
three runtime assertions and three private compile regressions cover exact
failure, success, preservation, and reuse by existing read and write laws.
Full validation and independent P0-P3 audits pass. No Account creation,
authority, or lifetime policy is introduced here.

## Completed present working storage Account total read

[ADR-0106](adr/0106-present-working-storage-account-total-read.md) adds one
total slot read to the ADR-0105 refinement and proves that the existing
conditional context read returns that value in `some`.

The operation reads the stored Account without another WorldState lookup.
Three runtime assertions cover zero-default and exact two-address/two-slot
reads; two private compile regressions cover direct and `Option.getD`
consumers. The operation, generated equation, and coherence law report
`[propext]`; full validation and independent P0-P3 audits pass. Account absence
remains handled only by refinement; address-role, lifetime, and transition
policies remain later work.

## Completed present working storage Account total write

[ADR-0107](adr/0107-present-working-storage-account-total-write.md) adds one
total write that synchronizes the selected Account, working-state entry, and
new presence evidence without another lookup or failure branch.

The first law relates its context projection to the existing optional write.
Three runtime assertions cover nonzero synchronization, zero deletion, and
sequential overwrite; three private compile regressions cover context
coherence, arbitrary observation, and canonical re-refinement. The operation,
generated equation, and law report `[propext]`; full validation and independent
P0-P3 audits pass. Address authority, lifetime, and transition policies remain
later work.

## Completed present working storage Account total read/write coherence

[ADR-0108](adr/0108-present-working-storage-account-total-read-write-coherence.md)
adds same-slot read-after-write and distinct-slot read preservation for the
total refined operations.

The laws delegate directly to Account semantics and add no new operation.
Both report `[propext]`; three private compile regressions cover direct use and
named composition with ADR-0106 conditional-read coherence. Full validation
and independent P0-P3 audits pass. Address authority, lifetime, and transition
policies remain later work.

## Completed present working storage Account total-write algebra

[ADR-0109](adr/0109-present-working-storage-account-total-write-algebra.md)
adds same-slot overwrite and distinct-slot commutation for sequential total
writes on the refined carrier.

The overwrite law is the only new simp rule; commutation remains caller-directed.
Both report `[propext, Quot.sound]`, and two private compile regressions apply
the laws by name. Full validation and independent P0-P3 audit pass. The slice
adds no operation. Address authority, lifetime, and transition policies remain
later work.

## Completed present working storage Account total-write isolation

[ADR-0110](adr/0110-present-working-storage-account-total-write-isolation.md)
adds one law preserving the complete optional Account lookup at every working
address different from the selected storage address.

The simp law reports `[propext]`; two private compile regressions apply it
directly and across two writes. Full validation and independent P0-P3 audit
pass. The slice adds no operation or runtime fixture. Address roles, lifetime,
and transition policies remain later work.

## Completed present working storage Account total-write projections

[ADR-0111](adr/0111-present-working-storage-account-total-write-projections.md)
adds four simp laws for the retained selector, checkpoint, working journal, and
updated stored Account.

The selector law completes nested simp composition with ADR-0110 isolation.
All four laws report `[propext]`; five private compile regressions apply the
projections directly and exercise that integration. Full validation and
independent P0-P3 audit pass. Address roles, lifetime, and transition policies
remain later work.

## Completed present working storage Account total-write presence

[ADR-0112](adr/0112-present-working-storage-account-total-write-presence.md)
adds named zero-deletion and nonzero-presence observations for the stored
Account returned by a total write.

Both laws report `[propext]`; two private compile regressions apply them
directly. Full validation and independent P0-P3 audit pass. The laws keep the
existing Account simp policy unchanged and add no operation or runtime fixture.
Other-slot representation, address roles, lifetime, and transition policies
remain later work.

## Completed present working storage Account total-write sparse preservation

[ADR-0113](adr/0113-present-working-storage-account-total-write-sparse-preservation.md)
completes the single-write sparse representation boundary. One base Account
law preserves `storageValue?` at a distinct slot; one refined law exposes the
same fact through the proven-present total writer.

The laws remain named and non-simp so automatic projection rewriting does not
silently broaden the older Account observation policy. The slice contains
exactly two direct compile regressions and no new executable behavior. Full
validation and independent P0-P3 audits pass.

## Completed present working storage Account optional/total re-refinement coherence

[ADR-0114](adr/0114-present-working-storage-account-optional-total-re-refinement-coherence.md)
closes the boundary between the existing failure-aware writer and the
proven-present total writer. Binding a successful optional result into canonical
Account refinement produces the complete total result, including its
snapshot-specific evidence.

One named non-simp law is sufficient: callers can apply it at each bind stage,
so no fixed-depth theorem or batch-write operation is needed. Two compile-only
regressions cover the declaration and its two-write composition; full
validation and independent P0-P3 audits pass.

## Completed parent-indexed initialization present storage Account refinement

[ADR-0115](adr/0115-parent-indexed-initialization-present-storage-account-refinement.md)
names the canonical composition from ADR-0098/0099 initialization into
ADR-0105 Account presence refinement. The result remains optional: an absent
selected Account stays absent, while success returns the existing carrier used
by total storage reads and writes.

The slice adds one partial adapter and two branch laws. Three compile-only
regressions cover both branches and an end-to-end total write/read consumer.
Full validation and independent P0-P3 audits pass; no additional carrier or
contract-entry identity claim was added.

## Historical address-selected closed Core code

[ADR-0116](adr/0116-address-selected-checked-core-code.md) established the
closed checked-code carrier, optional Account association, exact Address
lookup, and stateful pure execution. Its pure carrier and completion theorem
remain available, but ADR-0118 supersedes its Account field and selected runner.

Four checked-code laws, four Account laws, seven WorldState laws, and two
focused regression modules remain historical proof foundations.

## Completed address-selected host-code driver foundation

[ADR-0118](adr/0118-address-selected-host-code-driver.md) migrates Account code
to `CheckedHostCoreProgram`, promotes closed checked programs without changing
their bodies, selects code from the working WorldState, and handles storage
reads through a separately selected proven-present Account.

The original read-specific driver uses the exact remaining fuel returned at
every suspension. Its handled-step relation proves bounded completion and
exact exhaustion; typed checked runs cannot fault. Exact 11/12-fuel regressions
cover two dependent reads, zero-fuel final observation, distinct
code/storage/checkpoint Accounts, working-storage sensitivity, and Core-local
store preservation. ADR-0119 keeps these foundations while replacing the
read-specific execution API.

## Completed typed storage-write capability and combined storage driver

[ADR-0119](adr/0119-storage-write-capability-and-driver.md) appends a typed
`storageWrite : (word × word) -> unit` capability at index one while keeping
storage read at index zero. Core emits first-order read and write requests,
resumes each with its dependent response type, and preserves the suspended
continuation and Core-local store. Product inversion, progress, preservation,
machine/runner correspondence, typed outcomes, and no-fault safety cover the
write path.

The request loop is now a generic `HostDriver` parameterized by a dependent
handler. The combined storage handler reads the proven-present Account and
delegates writes to the existing total working-storage operation. The checked
and address-selected entry points are `runWithStorage` and
`runCodeWithStorage?`; code selection and storage selection remain independent.

Fuel is never restored when a request is handled. The generic and specialized
proofs account for every Core transition and request emission, preserve zero
fuel's final-state observation, and exclude faults for checked code. Whole-run
invariants retain the storage address, checkpoint, working effects, checked
code, and every non-selected working Account without making a false
whole-context equality claim.

Runtime coverage fixes the mixed read/write boundaries at fuel 21, 22, 27, and
28 and the sparse-zero write boundaries at 15 and 16. It checks the returned
value, selected working-storage update, zero deletion, unrelated Accounts,
checkpoint, effects, address selection, and Core-local store. Transaction
commit/rollback, nested invocation, further entry inputs, ABI, source syntax,
and publication remain later decisions.

## Completed handled-execution completeness and terminal fuel stability

[ADR-0120](adr/0120-handled-execution-completeness-and-fuel-stability.md)
closes the reverse proof direction for host execution. A generic
`HostDriver` result produces its handled-step and fuel evidence, and valid
evidence replays to that exact executable result. The relation is therefore a
two-way executable specification, including handlers that update their context.

Supplying more fuel preserves a completed result or a raw fault, including the
exact final context rather than only its value. The combined storage driver,
checked storage execution, and successful address-selected execution inherit
this guarantee; writes already recorded in the final working context remain
exactly the same. Out-of-fuel is intentionally different: additional fuel can
continue the run, so no out-of-fuel stability theorem is provided.

The mixed read/write/read and repeated-write regressions exercise the same
programs at larger budgets and retain their values, local stores, selected
storage updates, and every exposed frame projection. ADR-0120 adds proofs and
regressions only. It changes neither runtime execution nor the existing read
and write request kinds.

## Completed retained storage-selector observation

[ADR-0121](adr/0121-retained-storage-address-observation.md) appends
`storageAddress : unit -> word` at index 2. The combined driver already retains
one selector for every working-storage read and write; the new handler returns
that same selector through the lossless Address-to-Word bridge and leaves its
exact context unchanged.

Address-selected coverage keeps `codeAddress` distinct and observes the same
selector before and after a real storage write. The completed result and its
post-write context remain exact with more fuel through ADR-0120; out-of-fuel is
not stable. Full validation and an independent P0-P3 audit passed.

This remains an observation of an existing role, not a new contract-entry
identity. ADR-0122 next completes the optional selected-execution proof
boundary. Further inputs, call lifecycle, ABI, source syntax, and parser proofs
remain outside this slice; parser work stays paused while syntax remains
unstable.

## Completed address-selected handled execution exact specification

[ADR-0122](adr/0122-address-selected-handled-execution-exact-specification.md)
completes both optional branches of `runCodeWithStorage?`. A successful result
is equivalent to exact selected-code fuel evidence and can be reconstructed
from that evidence. Failure is equivalent to the working-WorldState code lookup
returning `none`; a selected run that exhausts fuel remains `some`.

The slice adds two proofs and direct compile-time consumers only. It changes no
runner, lookup, request, address role, lifecycle decision, parser, or public
format. Full validation and independent P0-P3 audits pass.

## Completed handled-execution relational metatheory

[ADR-0123](adr/0123-handled-execution-relational-metatheory.md) makes ordinary
host paths and context-threading handled paths compositional. The handled
relation now preserves Core typing directly, including across dependent
request responses. At one exact fuel budget, two sound witnesses identify the
same complete result.

Done and raw-fault witnesses remain valid with more fuel and agree exactly
across any two sufficient budgets, including their final handler contexts.
Out-of-fuel remains deliberately budget-relative: the regression fixture stops
after its context-changing request at fuel 1 and completes at fuel 3. Full
validation and independent P0-P3 audits pass; no runtime or public format
changed.

## Completed handled execution to frame continuation

[ADR-0124](adr/0124-completed-handled-execution-frame-continuation.md) connects
normal address-selected handled completion to the existing frame continuation
and resolution model. The caller supplies both the terminal frame-value
projection and the policy that interprets the final Core value and local store
as returned, reverted, or trapped.

Code absence, selected out-of-fuel, and completion remain distinct nested
options. Out-of-fuel and raw faults receive no implicit trap meaning. Exact
laws retain terminal checkpoint and working values, resolve all three
caller-selected outcomes, sharpen checked inner failure to out-of-fuel, and
keep completed continuations unchanged under additional fuel.

The existing read/write/read fixture exercises return, revert, and policy trap
resolution after a real storage update. It also fixes outer failure, fuel-22
inner exhaustion, and fuel-28-to-64 completed stability. Full validation and
independent P0-P3 audits pass. ABI encoding, normalization, parent delivery,
scheduling, transaction disposition, and source syntax remain later work.

## Completed parent-indexed selected execution continuation

[ADR-0125](adr/0125-parent-indexed-selected-execution-continuation.md) lifts
the completed storage execution path from a parent-indexed initialization.
Three nested optional boundaries keep storage absence, code absence, selected
out-of-fuel, and completion separate. Completion reconstructs the existing
parent-indexed context and proves that forgetting its relationship evidence
recovers the exact ADR-0124 continuation.

The slice reuses existing return, revert, trap rollback, and trap propagation
consumers. It adds no parent machine, callback delivery, scheduler, stack,
transaction policy, ABI, host input, or syntax.

All six public laws have direct compile consumers. The full 627-job build and
1,142-job test suite, strict trust-zero compilation, metadata checks, and
semantic-kernel policy checks pass. Independent final audits found no P0-P3
issue.

## Completed selected code-address observation

[ADR-0126](adr/0126-selected-code-address-observation.md) appends a fourth
internal host capability. `codeAddress : unit -> word` observes the Address
already supplied to select checked code; the high-level selected runner keeps
one argument for both lookup and handler execution.

The selector is a static run parameter rather than a duplicate field in the
mutable storage context. It is not a current contract, `self`, callee, caller,
authority, or storage selector. Core sees only Unit and Word, and frozen Wire
formats continue to reject host functions.

The request protocol, machine transitions, progress, preservation, checked
no-fault path, exact handler projections, strict Address recovery, remaining
fuel, and completed stability are all proved. Regressions distinguish code
address `0x10` from storage address `0x20`, stop at fuel 4, complete at fuel 5,
and retain the same completed result at fuel 32. Full build, test, strict
compilation, metadata, and kernel checks pass.

## Completed parent-indexed resolution view

[ADR-0127](adr/0127-parent-indexed-resolution-view.md) pairs the existing total
resolution of a completed parent-indexed frame with its existing opt-in trap
rollback selection. Return and revert retain their resolved state, effects, and
bytes with no trap rollback; trap retains its reason and the exact parent
rollback pair.

This is a value-level view only. It does not apply rollback, execute or resume
a parent, select callbacks across ADR-0125's optional layers, or define a root
frame or transaction checkpoint. Four non-simp laws use only `[propext]` and
compile consumers cover exact callbacks, trap rollback, parent-context
coherence, and larger-fuel completion. The 630-job build, 1,148-job test suite,
strict compilation, metadata, kernel-policy, and independent audits pass.

## Completed resolution-view trap-reason mapping naturality

[ADR-0128](adr/0128-parent-indexed-resolution-view-trap-reason-mapping-naturality.md)
closes the mapping algebra opened by ADR-0127. Mapping a parent-indexed
context's trap-reason type must map only the ordinary resolution result while
leaving the exact optional rollback pair unchanged.

This is one proof-only simplification law with no new mapper or runtime
operation. Its regressions cover direct use, identity, heterogeneous
composition, bytes-aware continuation invariance, and simp critical-pair
convergence. The 632-job build, 1,152-job test suite, trust-zero checks,
metadata, kernel policy, and independent audits pass.

## Completed parent-indexed trap-aware resolution fold

[ADR-0129](adr/0129-parent-indexed-trap-aware-resolution-fold.md) replaces the
manual coordination of ADR-0127's two observations with one total, generic
fold. Return and revert callbacks receive exact resolved pairs and bytes; the
trap callback receives the exact parent rollback pair and reason.

The caller chooses the result type, including whether it is optional. The fold
itself applies no rollback, executes no callback policy beyond branch
selection, resumes no parent, and defines no transaction boundary. Four exact
non-simp laws, three runtime assertions, and six compile consumers pass the
636-job build, 1,160-job test suite, trust-zero, metadata, kernel-policy, and
independent audits.

## Completed resolution-fold trap-reason mapping naturality

[ADR-0130](adr/0130-parent-indexed-resolution-fold-trap-reason-mapping-naturality.md)
adds no operation. Its single simp law moves heterogeneous trap-reason mapping
through the ADR-0129 fold by composing the mapper into only the trap function.
Return and revert functions, resolved values, rollback selection, and the fold
result type remain unchanged.

Four compile consumers cover direct theorem use, identity mapping, two-stage
heterogeneous composition, and a commuting square with ADR-0128's
resolution-view naturality. The 638-job build, 1,164-job test suite,
trust-zero, metadata, semantic-kernel, and independent audits pass. No runtime
fixture, branch duplicate, rollback application, parent resumption,
transaction policy, or parser dependency was added.

## Completed end-to-end call-value observation

[ADR-0131](adr/0131-end-to-end-call-value-observation.md) introduced one
immutable execution-input carrier containing the existing selected code
Address and one caller-supplied invocation-value Word. The input remains fixed
while the mutable storage context changes.

The append-only internal `callValue : unit -> word` Core capability at index 4
returns that exact Word. The same input now parameterizes handler recursion,
fuel evidence, selected lookup, continuation construction, and parent-indexed
completion. The handler leaves the mutable context unchanged and resumption
preserves the saved continuation, local Store, and remaining fuel.

Tests distinguish storage address, code address, and call value. Direct
observation reaches its request boundary with fuel 4, completes with fuel 5,
and has the same completed result with fuel 32. A second program observes,
writes, and observes the same Word before its parent-indexed result is consumed
by the existing resolution fold. Frozen Wire v1 and v2 reject the internal
host value. Balance movement, caller/current identity, ABI, parser work, and
publication remain outside this completed slice.

## Completed run-fixed caller-address observation

[ADR-0132](adr/0132-run-fixed-caller-address-observation.md) appends one
explicit caller Address to the immutable execution input and
`callerAddress : unit -> word` to internal Core at index 5. The host context
and environment now have six append-only entries; frozen Wire v1 and v2 still
reject every host-function value.

The handler returns the losslessly widened Address exactly, performs no Account
lookup, and leaves its complete context unchanged. The driver keeps the same
full input and remaining fuel. Direct observation stops at fuel 4, completes at
fuel 5, and is identical at fuel 32 even when no caller Account exists. Varying
only the caller changes only the observed result, not the completed context.

The observe/write/observe fixture completes at fuel 30 and stores and returns
the same caller-derived Word; its result survives all parent-continuation
options and the existing resolution fold. Caller provenance, authentication,
call kind, balances, nested invocation, ABI, parser rules, and publication are
not defined by this completed internal feature.

## Completed bounded optional input-byte observation

[ADR-0133](adr/0133-bounded-optional-input-byte-observation.md) adds a required,
bounded `InputData` value to the immutable execution input and appends internal
`inputDataByte? : word -> sum unit word` at index 6. Exact natural indexing
preserves every present octet, including zero, while the Unit branch represents
only absence.

The Core boundary, safety proofs, exact handler and driver laws, input-only
variation, byte-derived storage use, fuel boundaries, nested parent completion,
ADR-0129 fold consumption, and frozen-Wire rejection are complete. The full
649-job build and 1,186-job executable test suite pass together with trust-zero,
metadata, semantic-kernel, axiom, compatibility, and independent audits.

Input size, wider loads, endianness, padding, ABI and calldata meaning,
nested-input derivation, source syntax, and publication remain separate future
decisions.

## Completed run-fixed input-size observation

[ADR-0134](adr/0134-run-fixed-input-size-observation.md) derives exact
`InputData.sizeWord` from the retained strict bound and appends internal
`inputDataSize : unit -> word` at index 7. Exact byte-boundary coherence,
Core request and safety proofs, handler and driver context identity, and frozen
Wire rejection are complete.

Direct selected execution covers zero and nonzero sizes, input-only variation,
and fuel 4/5. Size-derived storage and parent-indexed completion cover measured
23/29/30/32 boundaries, all three option layers, larger-fuel stability, and
ADR-0129 fold consumption of the stored size and terminal bytes.

The full 652-job build and 1,192-job executable test suite pass together with
trust-zero over all 21 changed Lean roots, metadata, semantic-kernel, axiom,
compatibility, and independent audits. Multi-byte interpretation, ABI and
calldata meaning, nested-input derivation, syntax, and publication remain
separate future decisions.

## Completed strict optional input-word BE observation

[ADR-0135](adr/0135-strict-optional-input-word-be-observation.md) accepts
`InputData.wordBE?` as a strict full-window operation over the existing bounded
input. It extracts `[offset, offset + 32)` with natural-number bounds and uses
the canonical big-endian Word decoder. A complete all-zero window returns
`some Word.zero`; an incomplete window returns `none` without padding.

Core appends `inputDataWordBE? : word -> sum unit word` at index 8, extending
both host tables to length 9 and leaving index 9 first unbound. Its
`Option Word` response and Core safety boundary are complete. The handler
preserves its whole mutable context while returning the exact input-derived
result.

Direct regressions cover present nonzero, present zero, and absent windows.
The observe-write-observe storage path measures fuel 23/31/32 and is stable at
64. Parent regressions measure present fuel 29/30 and absent fuel 11/12 while
preserving the three optional layers, resolution fold result, terminal bytes,
and completion at fuel 64. Frozen Wire rejects the internal capability.

The 655-job build, 1,198-job test run, trust-zero and warning-as-error checks
for all 21 changed Lean roots, metadata, semantic-kernel, and diff checks pass.
Axiom reports contain `propext` and `Quot.sound`; only the per-byte coherence
proof additionally contains `Classical.choice` through the existing codec
proof path. No custom axiom or `sorry` remains. ABI, calldata, partial loads,
memory, nested calls, parser work, and publication remain outside this
completed slice. The independent completion audit found no P0-P3 issue.

## Completed resumable handled fuel slices

[ADR-0136](adr/0136-resumable-handled-fuel-slices.md) adds a total
`resumeWithFuel` consumer above the existing handled driver. Only an
`outOfFuel` result runs again, beginning at its exact retained handler context
and Core state. A `done` or `fault` result remains byte-for-byte unchanged.

The central law equates a same-handler split run with one run using
`fuel + additional`. Sequential additions associate for every result value,
while zero-additional identity is deliberately limited to actual run
results: a forged exhausted value can contain a state that zero fuel already
recognizes as terminal. Resumption preserves the type of any typed result and
cannot expose a raw machine fault. The storage specialization keeps the exact
same `ExecutionInputs` on both sides.

Generic regressions cover request-ready, fault, exhausted, completed, and
terminal cases. The storage regression retains a write across exhaustion,
matches the one-shot run, preserves checkpoint/effects/unrelated Account, and
uses a separate changed-input fixture to make the theorem boundary visible.
The 659-job build, 1,206-job test executable build, full test run, seven-root
trust-zero and warning-as-error checks, metadata, semantic-kernel, diff, axiom,
and independent audits pass; the audit found no P0-P3 issue. Gas, persistence,
handler/input replacement, nested calls, transactions, syntax, and publication
are excluded.

## Completed canonical host capability registry

[ADR-0137](adr/0137-canonical-host-capability-registry.md) replaced three
hand-maintained copies of the then-existing host-capability order with one
explicit extensible registry. It remains the only production order literal.
Both fixed tables are maps over it, and one list induction provides their
runtime typing proof. Exact finite laws tie registry position to each
independently explicit numeric index.

All eighteen old lookup facts, both length facts, nine `index_*` facts, and
`hostEnvironment_hasTypes` retain their statements and simplifier attributes:
all thirty declarations remain registered. The mapped tables are definitionally
equal to the old literals. At that milestone, numeric and runtime regressions
preserved all nine capabilities at indexes 0 through 8, length 9,
first-unbound index 9, and checked results.

The 51-job focused build, 659-job full build, 1,206-job test executable build,
full test run, four-root trust-zero and warning-as-error checks, metadata,
semantic-kernel, diff, and axiom checks pass; theorem reports are axiom-free,
use `propext`, or use `propext` with `Quot.sound`. The independent trust-zero audit
confirmed the thirty simplifier registrations, old-table definitional
equality, and single production literal, with no P0-P3 issue. These counts and
length-9 boundaries describe the ADR-0137 milestone; ADR-0139 now appends a
tenth entry while retaining indexes 0 through 8. No custom axiom or `sorry`
remains, and no registry, Wire, Oracle, source, or ABI format is published.

## Completed branch-complete parent execution result

[ADR-0138](adr/0138-branch-complete-resumable-parent-indexed-selected-execution.md)
adds a total internal result for storage absence, code absence, exhaustion,
raw fault, and completion. Only exhaustion invokes the driver again, using its
exact retained context and state under the same immutable inputs and completion
policy. Split and summed budgets must agree exactly.

An explicit lossy erasure recovers the existing nested-`Option` result, whose
operation and theorems remain unchanged. The new boundary gives no resolution
meaning to absence, exhaustion, or fault and adds no gas, persistence, nested
invocation, transaction, parser, syntax, ABI, Wire, Oracle, or publication
policy.

The proof interface includes five exact branch equivalences, checked no-fault,
whole legacy equality, split/zero/add resumption and completion inversion, plus
exact plain-continuation, legacy, return/revert/trap fold, and completed-fold
identity laws. Fuel 9/10/15/16 regressions cover absence, retained write
effects, request non-replay, exhaustion, completion, synthetic fault, and every
fold branch.

The 673-job build, 1,234-job test executable build, full test run, 16-root
trust-zero and warning-as-error checks, metadata, semantic-kernel, and diff
checks pass. Twenty-one theorem reports use only `propext` and `Quot.sound`;
the independent audit found no P0-P3 issue. The old three files and root README
remain unchanged.

## Completed run-fixed current-address observation

[ADR-0139](adr/0139-run-fixed-current-address-observation.md) requires one
explicit `currentAddress` in immutable execution inputs and appends its
Unit-to-Word observation at stable host index 9. Both canonical host tables now
have length 10 and index 10 is first unbound. Exact handler and driver laws
make the observation read-only, recover the supplied Address by strict
narrowing, and preserve the complete mutable context, continuation, and
Core-local Store.

Direct execution measures the exact 4/5 fuel boundary. The end-to-end
observe/write/observe path measures 16/17/23/29/30; split resumptions at 17+13
and 23+7 equal one-shot fuel 30. Regressions keep current Accounts absent,
vary only `currentAddress` with exact context identity, preserve the derived
storage write and equal returned pair, and exercise return/revert/trap folds.

The 676-job build, 1,240-job test executable build, full test run, 33-root
trust-zero and warning-as-error sweep, metadata, semantic-kernel, diff, axiom,
compatibility, and independent P0-P3 audits pass. No call kind, nested call,
authority, parser, public format, or root README change was added.

## Active proof-refined selected-execution session

[ADR-0140](adr/0140-proof-refined-parent-indexed-selected-execution-session.md)
is accepted; implementation is the next active slice. A session will store one
parent-indexed selected run's initialization, storage selector, complete
execution inputs, completion policy, total supplied budget, and exact result.
Its refinement certificate will equate that result to the fixed configuration
run once with the stored cumulative budget.

`start` will construct the certificate directly. `resumeWithFuel` will accept
only an additional budget, reuse the retained ADR-0138 result state, and update
the total by addition. Planned proofs cover every projection, invariant
preservation, whole-session zero and addition, checked no-fault, legacy
nested-`Option` erasure, and completed continuation and resolution-fold
coherence. Measured ADR-0138 and ADR-0139 regressions will ensure resumption
does not replay earlier work or permit changed immutable inputs.

The budget is provided fuel, not a consumption or gas measure. This carrier is
not a nested-call frame, scheduler, transaction, ABI conversion, parser
adapter, Wire or Oracle version, or public interface.

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
one Core execution. Contract storage is separately explicit in the working
WorldState and is threaded by ADR-0119's combined driver. Later slices must
connect it to complete call frames, transaction inputs, and commit/rollback
lifecycle rules; they must not conflate it with the Core-local store.

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
