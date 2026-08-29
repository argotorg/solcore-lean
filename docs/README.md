# Documentation guide

The root README explains what can be run. The documents in this directory
explain what the implementation means, what is proved, and what remains.

## Where to start

| Question | Document |
| --- | --- |
| What works today? | [Current status](CURRENT_STATUS.md) |
| What is the active development direction? | [Semantic Core roadmap](M1_PLAN.md) |
| Why is parser work paused? | [Frontend freeze and resumption plan](M2_PLAN.md) |
| How are the layers separated? | [Architecture](ARCHITECTURE.md) |
| Which features exist? | [Feature matrix](FEATURE_MATRIX.md) |
| What makes a rule normative? | [Specification charter](SPEC_CHARTER.md) |
| How do I build and review changes? | [Development guide](DEVELOPMENT.md) |
| What can be compared with other compilers? | [Compatibility matrix](COMPATIBILITY_MATRIX.md) |

## Current development policy

Concrete Solcore syntax may change substantially. The published parsers remain
available as versioned reference implementations, but new grammar-dependent
proof work is paused. Active work is directed toward a syntax-independent
Semantic Core and explicit runtime semantics.

The current internal contract boundary can execute checker-accepted Core code
selected by `codeAddress` from a working WorldState. Core supplies typed
runtime-only storage read and write capabilities; each request suspends with
its exact continuation, local cell store, and remaining fuel. A generic host
driver delegates requests to a combined handler over the Account selected by a
separate `storageAddress`; the two address roles are never equated.
Reads leave the host context unchanged, while writes update the returned
working context and resume with Unit. This boundary is proved and tested but
unpublished: frozen Wire formats reject the host values, and source syntax,
ABI, gas, calls, authorization, transaction commit, and rollback remain future
work.

[ADR-0120](adr/0120-handled-execution-completeness-and-fuel-stability.md)
completes the proof interface for this driver without changing its behavior.
Executable results and the readable handled-step relation now determine one
another. Done and fault results are unchanged when more fuel is supplied; the
storage, checked, and successful address-selected done interfaces retain the
exact final context. Out-of-fuel is deliberately not called stable because more
fuel can continue the run. No host request kind or runtime API behavior changed.

First-order local cells from
ADR-0022 and the program-local named algebraic data and normalized constructor
matching from [ADR-0023](adr/0023-core-vnext-named-algebraic-data.md) are
complete internal slices. The derived boolean and word conversions from
[ADR-0024](adr/0024-core-vnext-bool-word-conversions.md) are complete as ordinary
existing Core expressions. The derived word-valued zero test from
[ADR-0025](adr/0025-core-vnext-word-is-zero.md) is also complete.
The [ADR-0026](adr/0026-core-vnext-short-circuit-booleans.md) slice completes
selected-branch-only boolean conjunction and disjunction using existing
conditionals without adding a Core tag. Its expansion, typing, inference, four
store-threaded branches, effects, faults, exact fuel, weakening, and exact wire
v1/v2 projection are proved and tested. Core vNext remains active, with
the completed `wordIsNonzero` from
[ADR-0027](adr/0027-core-vnext-word-is-nonzero.md) as its ninth slice.
It composes `boolToWord(wordToBool(x))`, maps zero to word zero and nonzero words
to word one, evaluates its operand exactly once, and preserves its final store.
It adds no tag and is separate from boolean truthiness and ABI decoding.
Its named expansion, typing, inference, store-preserving evaluations, weakening,
effects, exact fuel, distinctions, and exact v1/v2 boundaries are proved and
tested, and the audits pass.
The strict address-and-word bridge and strict 20-byte address encoding are
complete, including Address text-and-byte coherence. Further Core conversions
and primitives remain planned. The completed runtime-state foundation covers
explicit Account absence, canonical storage values, and outcome-directed
selection between checkpoint and working state.
The completed seventeenth slice,
[ADR-0035](adr/0035-core-vnext-bounded-logical-shifts.md), completes focused
proof and regression interfaces for the existing raw `wordShl` and `wordShr`
operators. Its fourteen theorems and boundary, order, effect, fuel, Wire, and
JSON tests pass. Core keeps value before shift, uses zero for amounts of 256 or
more, and adds no alias, tag, source rule, or Wire change. The next feature is
selected by a separate ADR.
The completed eighteenth slice,
[ADR-0036](adr/0036-core-vnext-modular-word-arithmetic.md), completes fourteen
focused Word, application, and evaluation results for existing raw addition,
subtraction, and multiplication. Normal and wrapped values, strict order,
effects, exact fuel, and Wire/Core/JSON round trips pass. Results remain modulo
`2^256` and expressions evaluate left to right exactly once. No alias, generic
proof duplicate, tag, schema, or Oracle behavior changed. The next feature is
selected by a separate ADR.
The completed nineteenth slice,
[ADR-0037](adr/0037-core-vnext-binary-bitwise-logic.md), completes fifteen
focused Word, application, and evaluation results for existing raw word and,
or, and xor. Mask, identity, order, effect, exact-fuel, and Wire/Core/JSON tests
pass. Word values commute, but expressions remain left-to-right and exactly
once. No alias, generic proof duplicate, tag, schema, or Oracle behavior
changed. The next feature is selected by a separate ADR.
The completed twentieth slice,
[ADR-0038](adr/0038-core-vnext-direct-word-comparisons.md), completes eight
focused application and evaluation results for existing raw boolean word
equality and strict unsigned greater-than. Operands remain left-to-right and
exactly once. Value, type, ordered-fault, effect, exact-fuel, and Wire/Core/JSON
regressions pass, and older derived comparisons reuse the helpers. No expression
alias, Word or generic proof duplicate, tag, schema, or Oracle behavior changed.
The independent audit found no P0-P3 issue; further primitives remain planned.
The completed twenty-first slice,
[ADR-0039](adr/0039-core-vnext-word-leading-zero-count.md), adds internal
`UnaryOp.wordClz` and total `Word.clz` for 256-bit words. It maps zero to 256
and nonzero values to `255 - Nat.log2 value.val`, evaluates its operand exactly
once, and retains the final store. All eleven focused theorems and value, type,
raw-fault, effect, exact-fuel, and frozen Wire v1/v2 rejection tests pass. The
public Oracle and schemas remain unchanged. The independent audit found no
P0-P3 issue.
The completed twenty-second slice,
[ADR-0040](adr/0040-core-vnext-word-byte-selection.md), adds internal big-endian
byte selection for 256-bit words. Left is index and right is value; Core
evaluates both exactly once in that order, and indices at least 32 return zero.
All nine focused theorems and value, type, raw and ordered-fault, effect, store,
exact-fuel, and frozen Wire v1/v2 plus v2-operation rejection tests pass. Public
Oracle, schema, and JSON formats remain unchanged. The independent audit found
no P0-P3 issue.
The completed twenty-third slice,
[ADR-0041](adr/0041-core-vnext-arithmetic-right-shift.md), adds internal
two's-complement arithmetic right shift. Raw Core is value-left/shift-right and
evaluates in that order exactly once. All eleven focused theorems and signed
range, type, raw and ordered-fault, effect, store, exact-fuel, and frozen Wire
plus v2-operation rejection tests pass. Future source argument reordering must
preserve source evaluation through prior bindings. Public Oracle, schema, and
JSON formats remain unchanged. The independent audit found no P0-P3 issue.
The completed twenty-fourth slice,
[ADR-0042](adr/0042-core-vnext-modular-exponentiation.md), adds internal modular
word exponentiation. Core evaluates base then exponent exactly once. A bounded
square-and-multiply helper computes modulo `2^256`, with its loop contained in
one CEK primitive step. All fourteen focused theorems and value, type, raw and
ordered-fault, effect, store, exact-fuel, and frozen Wire plus v2-operation
rejection tests pass. Public Oracle, schema, and JSON formats remain unchanged.
The independent audit found no remaining P0-P3 issue; further primitives use
separate ADRs.
The completed twenty-fifth slice,
[ADR-0043](adr/0043-core-vnext-signed-word-greater-than.md), fixes an internal
boolean signed-greater basis over 256-bit two's-complement words. Core evaluates
left then right exactly once. Signed less-than and word-valued flags remain
separate, and frozen public Wire formats reject the new internal operation.
All eleven focused theorems and value, type, ordered-fault, effect, store,
exact-fuel, and Wire-rejection tests are complete. Public formats are unchanged;
the independent audit found no P0-P3 issue.
The completed twenty-sixth slice,
[ADR-0044](adr/0044-core-vnext-derived-signed-word-less-than.md), derives
boolean signed less-than through two bindings. Source left remains before source
right; only their bound values are reordered for signed greater-than. The exact
five static and five evaluation theorems and the value/type, fault-order,
effect/store, fuel, and frozen-Wire regressions add no primitive or public Wire
tag. Public behavior is unchanged; the independent audit found no P0-P3 issue.
The completed twenty-seventh slice,
[ADR-0045](adr/0045-core-vnext-signed-word-comparison-flags.md), derives
canonical word-valued signed greater-than and less-than flags. Both preserve
source left-to-right evaluation and return word one or zero. The exact
ten static and ten evaluation theorems cover canonical word-one/word-zero
results, values/types, ordered faults, effects/store, exact fuel, and frozen
Wire rejection. It adds no operation tag or public behavior; the independent
audit found no P0-P3 issue.
The completed twenty-eighth slice,
[ADR-0046](adr/0046-core-vnext-signed-word-nonstrict-comparisons.md), derives
boolean signed ≤ and ≥ by negating the existing strict comparisons. Both keep
source left-to-right evaluation and equality returns true. Its exact ten static
and ten evaluation theorems and value/type, fault/effect/store, exact-fuel, and
frozen-Wire regressions are complete. It adds no operation tag or public Wire
behavior; the independent audit found no P0-P3 issue.
The completed twenty-ninth slice,
[ADR-0047](adr/0047-core-vnext-word-sign-extension.md), adds internal word sign
extension. The left operand selects a low-order byte width and the right operand
is the value. In-range indices copy the selected sign bit through the upper
word; indices at least 32 leave the value unchanged. Its exact ten theorems and
regressions cover indices 0, 1, 31, 32, and maximum, types, faults, effects,
final stores, exact fuel, and frozen-Wire rejection. Focused/full builds, tests,
kernel policy, and metadata verification pass. The slice is internal and does
not change frozen Wire formats or public behavior; the independent audit found
no P0-P3 issue.
The completed thirtieth slice,
[ADR-0048](adr/0048-core-vnext-signed-word-division.md), adds internal signed
division and remainder. The left operand is the dividend and the right is the
divisor. Division rounds toward zero, remainder follows the dividend's sign,
zero divisors return zero after both operands evaluate, and the minimum-value
overflow case wraps. Its exact fourteen theorems and focused sign, zero,
minimum/negative-one, type, raw and ordered fault, effect/final-store, exact
fuel, and frozen-Wire regressions are complete. Focused/full builds and tests,
kernel policy, and metadata verification pass. Public formats and behavior are
unchanged; the independent audit found no P0-P3 issue.
The completed thirty-first slice,
[ADR-0049](adr/0049-core-vnext-signed-word-nonstrict-comparison-flags.md),
derives canonical word-valued signed ≤ and ≥ flags from the existing boolean
builders. Both keep source left-to-right evaluation and return word one or
zero; only the ≥ builder swaps already computed bound values internally. Its
exact twenty theorems and focused same/cross/equal truth, type, underlying and
ordered fault, effect/final-store, exact-fuel, and frozen builder,
handwritten-expansion, and v2-`wordSgt` rejection regressions are complete.
Focused/full builds and tests, kernel policy, and metadata verification pass.
It adds no tag or public behavior; the independent audit found no P0-P3 issue.
The completed thirty-second slice,
[ADR-0050](adr/0050-core-vnext-ternary-modular-arithmetic.md), adds dedicated
three-operand modular addition and multiplication. It evaluates both values
and then the modulus, uses the full-precision sum or product before reduction,
and returns zero for modulus zero only after every operand evaluates. The new
form, its dedicated raw fault, generic static/safety support, exact fourteen
focused theorems, and value/order/effect/fuel/Wire regressions are complete and
remain internal. The independent audit found no P0-P3 issue.

The completed runtime-foundation slice,
[ADR-0051](adr/0051-canonical-runtime-scalars.md), defines canonical byte,
address, and word observations independently of source syntax and contract
state. It fixes strict lowercase `0x` text and a 32-byte big-endian word view
without changing any published Wire or Oracle profile. Exactly sixteen focused
theorems establish lengths, round trips, canonicality, injectivity, and
agreement with Core byte selection. Executable tests cover strict decoder
rejection, boundary values, a complete 32-byte big-endian fixture, indexed byte
agreement, and accepted-input canonicalization. The frozen Wire codecs were not
refactored; representative Word text is checked for output compatibility. The
independent audit found no P0-P3 issue.

The completed contract-outcome slice,
[ADR-0052](adr/0052-contract-frame-outcomes.md), adds only the internal halt
vocabulary needed before contract state: return data, revert data, or a trap
reason supplied by later semantics. Empty bytes remain a present payload rather
than an absent one. The carrier, four total observations, exactly six laws, and
10 executable runtime assertions are complete. They add no rollback, evaluator,
ABI behavior, resource-limit meaning, or published Wire or Oracle format. The
independent audit found no P0-P3 issue.

The completed strict address-and-word bridge,
[ADR-0053](adr/0053-strict-address-word-bridge.md), keeps an address's numeric
value when widening it to a word and accepts a word as an address only below
`2^160`. Larger words fail explicitly instead of losing their upper bits. The
two definitions, exactly six axiom-free laws, and 10 runtime assertions are
complete. They add no source cast, ABI behavior, contract state, or public
format. The independent audit found no P0-P3 issue.

The completed strict address-byte slice,
[ADR-0054](adr/0054-strict-address-bytes.md), fixes an exact 20-byte
most-significant-byte-first representation. Its two definitions, exactly six
laws, and 10 runtime assertions cover leading zeros, strict width, round trips,
injectivity, and all 20 bytes aligned with indices 12 through 31 of a widened
Word. It adds no ABI rule, source cast, contract state, or public format. The
independent audit found no P0-P3 issue.

The completed Address representation coherence slice,
[ADR-0055](adr/0055-address-representation-coherence.md), adds no executable
API. Fifteen private helpers support exactly four public laws and eight runtime
assertions connecting canonical 40-digit Address text with exact 20-byte
big-endian encoding, including complete decoder agreement for arbitrary text.
It adds no ABI, state, or public format. The independent audit found no P0-P3
issue.

The completed minimal world-state slice,
[ADR-0056](adr/0056-minimal-world-state.md), adds finite Account and WorldState
carriers whose private data is limited to semantic lookup functions and
zero-free evidence. Missing storage reads as zero, zero writes delete the entry,
and an absent Account is never created by a storage write. Rollback, balances,
code, calls, ABI behavior, ordering, and publication remain outside this slice.
Exactly twelve laws and twelve runtime assertions cover its eight operations.
The carriers expose no concrete map, comparison, or printable representation;
privacy and recursor checks limit observation to the same semantic lookup
behavior as the public queries. The final independent audit found no P0-P3
issue.

The completed outcome-resolution slice,
[ADR-0057](adr/0057-frame-outcome-world-state-resolution.md), adds one internal
operation that selects working state after return, checkpoint state after
revert, and leaves trap disposition unresolved. It does not define transaction
rollback, nested frames, surviving effects, ABI behavior, or EVM rules.
Exactly three constructor laws and three runtime assertions cover the operation;
all three laws report only `propext`.

The completed proof-only update-algebra slice,
[ADR-0058](adr/0058-world-state-observational-update-algebra.md), adds no
executable API. It provides six extensionality, overwrite, and distinct-key
commutation laws plus two compile-time examples and four runtime assertions for
the already-completed Account and WorldState operations.

The completed proof-only storage-write slice,
[ADR-0059](adr/0059-world-state-storage-write-algebra.md), adds no executable
API. It provides four laws and four runtime assertions for conditional
overwrite, independent updates, and canonical zero deletion through
`writeStorage?`.

The completed external-checkpoint frame-result slice,
[ADR-0060](adr/0060-external-checkpoint-frame-run-result.md), pairs a speculative
working WorldState with a parametric FrameOutcome. Its single named resolver
uses a caller-owned checkpoint and leaves trap disposition unresolved.
Its carrier, one named resolver, three constructor laws, and three runtime
assertions covering both projections add no instance or private representation.

The completed effect-policy slice,
[ADR-0061](adr/0061-frame-effect-journal-policy.md), separates an opaque
rollback-scoped snapshot from an opaque surviving trace snapshot. It fixes
return/revert/trap resolution and two nested rollback laws without choosing an
event taxonomy, ordering, append algebra, or transaction model.
Its one carrier, one resolver, five laws, and five runtime assertions introduce
no axioms or concrete effect representation.

The completed synchronized-resolution slice,
[ADR-0062](adr/0062-synchronized-frame-state-effect-resolution.md), adds one
internal operation that resolves WorldState and the parametric effect journal
from one outcome branch. It adds no carrier or nested execution policy.
Its one resolver, five laws, and three projection-aware runtime assertions all
retain the existing parametric and unpublished boundaries.

The completed proof-only child-composition slice,
[ADR-0063](adr/0063-synchronized-child-frame-composition.md), proves child
return and child revert followed by parent revert using the synchronized
resolver. It adds no operation, frame stack, or trace-order rule.
Its two non-simp laws and two definition-only runtime assertions cover both
intermediate child resolution and final parent rollback.

The completed proof-only trap-propagation slice,
[ADR-0064](adr/0064-unresolved-trap-propagation.md), adds no carrier or
operation. It proves one generic fact: a trapped synchronized resolution stays
`none` when bound to any continuation. One definition-only sentinel test
confirms that the continuation is not invoked. Trap disposition, rollback,
trace survival, fatal handling, and transaction behavior remain undecided.

The completed proof-only continuation slice,
[ADR-0065](adr/0065-resolved-frame-continuation-laws.md), adds no carrier or
operation. It records the two matching facts for returned and reverted
synchronized results: any Option continuation receives exactly the pair
selected by the existing resolver. Its two non-simp laws and two
definition-only sentinel assertions pass full validation. Checkpoint creation,
trace accumulation, invocation ownership, and transaction behavior remain
undecided.

The completed caller-owned continuation slice,
[ADR-0066](adr/0066-caller-owned-frame-continuation.md), names one executable
resolver/bind boundary. The caller supplies checkpoints and an opaque
already-accumulated trace; return and revert invoke the continuation, while a
trap does not. Its one operation, three simp laws, and three definition-only
assertions pass full validation. It adds no frame stack, trace append rule, or
transaction policy.

The completed continuation-context slice,
[ADR-0067](adr/0067-caller-owned-frame-continuation-context.md), groups the four
inputs for one completed frame into a nominal carrier and delegates to ADR-0066.
Its one carrier, one operation, one coherence law, and three definition-only
assertions pass full validation. It is not a full execution frame and proves no
checkpoint lineage or trace-prefix relation.

The completed total-resolution slice,
[ADR-0068](adr/0068-total-frame-resolution-result.md), adds a first-order result
that preserves return/revert payloads and trap reasons. State and effects are
selected only for return and revert, so trap and transaction disposition remain
open.

The completed trace slice,
[ADR-0069](adr/0069-ordered-frame-trace-algebra.md), adds an opt-in finite
chronological event sequence with tail recording and ordered append. Event
kinds remain parametric, and existing generic effect journals are unchanged.

The completed trace-prefix slice,
[ADR-0070](adr/0070-frame-trace-prefix-relation.md), makes ordered prefix
consistency an explicit proof obligation. It describes value factorization,
not runtime lineage or parent/child identity.

The completed trace-prefixed continuation-context slice,
[ADR-0071](adr/0071-trace-prefixed-frame-continuation-context.md), binds that
proof to the exact checkpoint and working traces stored in one context. It
does not turn prefix factorization into evidence of runtime ancestry.

The completed indexed trace-extension slice,
[ADR-0072](adr/0072-indexed-frame-trace-extension.md), fixes an earlier trace
once and then accepts only individual events. It generates prefix evidence
without adding another public operation that accepts an ambiguous trace
fragment.

The completed parent-indexed continuation-context slice,
[ADR-0073](adr/0073-parent-indexed-frame-continuation-context.md), requires one
completed context's checkpoints to equal an exact parent working pair. It
reuses existing resolution and does not claim a runtime invocation occurred.

The completed parent-indexed continuation-construction slice,
[ADR-0074](adr/0074-trace-extension-parent-context-construction.md), derives
that carrier and both relationship proofs from an indexed trace extension. It
does not turn the selected inputs into evidence of an actual invocation.

The completed parent-indexed trapped-frame rollback slice,
[ADR-0075](adr/0075-parent-indexed-trap-rollback-selection.md), selects a local
parent rollback pair only when explicitly asked about a trap. Propagation,
fatality, parent resumption, and transaction handling remain separate.

The completed parent-indexed trap-propagation payload slice,
[ADR-0076](adr/0076-parent-indexed-trap-propagation-payload.md), packages that
rollback pair with the original trapped outcome for one caller-designated
prospective enclosing boundary. It does not execute or prove propagation.

The completed payload-coherence slice,
[ADR-0077](adr/0077-parent-indexed-trap-propagation-payload-coherence.md),
characterizes successful selection and carries existing non-strict trace-prefix
evidence to the selected journal without adding an execution operation.

The completed heterogeneous trap-reason mapping slice,
[ADR-0078](adr/0078-heterogeneous-frame-outcome-trap-reason-mapping.md), lets a
caller translate only trapped reasons while keeping return and revert bytes
unchanged. It adds no taxonomy or propagation policy.

The completed frame-result mapping slice,
[ADR-0079](adr/0079-heterogeneous-frame-run-result-trap-reason-mapping.md),
lifts that translation while keeping the result's working state unchanged. It
does not resolve state or imply that a trap was propagated at runtime.

The completed total-resolution mapping slice,
[ADR-0080](adr/0080-heterogeneous-frame-resolution-result-trap-reason-mapping.md),
keeps return/revert state, effects, and bytes unchanged while translating only
trapped reasons. It does not rerun the resolver.

The completed continuation-context mapping slice,
[ADR-0081](adr/0081-heterogeneous-frame-continuation-context-trap-reason-mapping.md),
keeps caller-owned checkpoints and working inputs unchanged while mapping only
the contained frame result.

The completed resolution-naturality slice,
[ADR-0082](adr/0082-frame-trap-reason-mapping-resolution-naturality.md), proves
that mapping before total resolution agrees with mapping the resolved value.
It adds no execution operation.

The completed continuation-result slice,
[ADR-0083](adr/0083-frame-trap-reason-mapping-continuation-invariance.md),
proves that context reason mapping leaves the `Option` value produced by
`FrameContinuationContext.continue?` unchanged. It adds no execution operation.

The completed trace-prefix context mapping slice,
[ADR-0084](adr/0084-heterogeneous-trace-prefixed-frame-continuation-context-trap-reason-mapping.md),
maps only the inherited continuation context while retaining the same trace
prefix evidence.

The completed parent-indexed context mapping slice,
[ADR-0085](adr/0085-heterogeneous-parent-indexed-frame-continuation-context-trap-reason-mapping.md),
maps only the trace-prefix context while retaining the same parent index and
checkpoint equality.

The completed checkpoint-snapshot slice,
[ADR-0086](adr/0086-nominal-frame-checkpoint-snapshot.md), names one
caller-supplied synchronized state/effect pair without claiming capture time,
ownership, or execution.

The completed checkpoint-and-working slice,
[ADR-0087](adr/0087-frame-checkpointed-working-pair.md), stores one checkpoint
snapshot beside an independent working pair without adding lifecycle meaning.

The completed continuation-context construction slice,
[ADR-0088](adr/0088-continuation-context-from-checkpointed-working-pair.md),
assembles those values and an opaque outcome into the existing context without
claiming execution.

The completed bytes-aware continuation slice,
[ADR-0089](adr/0089-bytes-aware-frame-resolution-continuation.md), passes
resolved return/revert state, effects, and bytes to separate caller callbacks
while leaving traps unresolved.

The completed continuation-erasure slice,
[ADR-0090](adr/0090-frame-continuation-branch-byte-erasure-coherence.md),
proves that identical bytes-ignoring branch callbacks recover the existing
bytes-insensitive context continuation.

The completed result-mapping continuation slice,
[ADR-0091](adr/0091-frame-resolution-continuation-trap-reason-mapping-invariance.md),
proves that bytes-aware continuation is invariant under heterogeneous
trap-reason mapping.

The completed checkpointed storage slice,
[ADR-0092](adr/0092-checkpointed-working-pair-storage-write.md), conditionally
updates only a pair's working WorldState while retaining its checkpoint and
working journal.

Working storage now uses one retained address. Writes use that address through
[ADR-0093](adr/0093-checkpointed-working-pair-storage-address.md), while
[ADR-0094](adr/0094-world-state-storage-read.md) and
[ADR-0095](adr/0095-address-bound-working-storage-read.md) make reads return
`none` for an absent Account and zero for a missing slot in a present Account.

[ADR-0096](adr/0096-world-state-storage-read-write-coherence.md) proves that a
successful write is visible to a later read and leaves unrelated slots and
addresses unchanged. The completed
[ADR-0097](adr/0097-address-bound-working-storage-read-write-coherence.md)
makes the same-slot and different-slot results directly available through the
retained address.

The completed [ADR-0098](adr/0098-parent-indexed-frame-initialization.md) adds a
small frame-initialization value. A caller supplies the initial WorldState and
rollback value; the implementation reuses the designated parent values as the
checkpoint and trace starting point. It does not run or schedule a frame.

The completed
[ADR-0099](adr/0099-parent-indexed-frame-initialization-storage-address.md)
adds a small adapter that attaches a caller-supplied storage address to those
initialized values. It reuses the existing storage reader and writer and does
not treat the address as an owner or current contract.

The completed
[ADR-0100](adr/0100-checkpointed-working-pair-storage-write-algebra.md) adds
proofs that repeated writes keep their expected overwrite and independent-
write behavior after they are lifted into checkpointed working values. It adds
no new write operation or runtime-order claim.

The completed
[ADR-0101](adr/0101-address-bound-working-storage-write-algebra.md) adds the
same-slot overwrite and distinct-slot exchange rules for the retained-address
writer. It does not add another address input or treat the stored address as an
authority.

The completed
[ADR-0102](adr/0102-address-bound-working-storage-write-preservation.md) adds
proofs that a successful retained-address write keeps the same selector,
checkpoint, and working effect journal, while an unavailable write remains
`none`.

The completed
[ADR-0103](adr/0103-address-bound-working-storage-write-values-coherence.md)
adds one proof that removing the address wrapper from a write result recovers
the existing underlying values write without changing success or failure.

The completed
[ADR-0104](adr/0104-parent-indexed-initialization-continuation-context-coherence.md)
adds one proof that the two existing initialization routes build the same
plain continuation context when given the same outcome.

The completed
[ADR-0105](adr/0105-present-working-storage-account-refinement.md) adds a
checked form of an address-bound working context that carries the exact
selected Account when that Account exists.

The completed
[ADR-0106](adr/0106-present-working-storage-account-total-read.md) adds a
total slot read from that checked Account, together with agreement with the
existing conditional read.

The completed
[ADR-0107](adr/0107-present-working-storage-account-total-write.md) adds a
total slot write that keeps the checked Account and its working-state entry in
sync.

The completed
[ADR-0108](adr/0108-present-working-storage-account-total-read-write-coherence.md)
adds same-slot and distinct-slot read-after-write laws for those total
operations.

The completed
[ADR-0109](adr/0109-present-working-storage-account-total-write-algebra.md)
adds overwrite normalization and distinct-slot commutation for total writes.

The completed
[ADR-0110](adr/0110-present-working-storage-account-total-write-isolation.md)
proves preservation of every non-selected working Account across a total write.

The completed
[ADR-0111](adr/0111-present-working-storage-account-total-write-projections.md)
adds direct selector, checkpoint, journal, and stored-Account projections.

The completed
[ADR-0112](adr/0112-present-working-storage-account-total-write-presence.md)
adds named zero-deletion and nonzero-presence observations after total writes.

The completed
[ADR-0113](adr/0113-present-working-storage-account-total-write-sparse-preservation.md)
preserves the optional sparse entry at every distinct slot, both directly on
Account and through the proven-present total writer.

The completed
[ADR-0114](adr/0114-present-working-storage-account-optional-total-re-refinement-coherence.md)
makes optional write plus canonical Account refinement equal the total writer,
including the complete proof-carrying result.

The completed
[ADR-0115](adr/0115-parent-indexed-initialization-present-storage-account-refinement.md)
checks a storage selector against caller-supplied `initialWorld` and returns the
proven-present carrier used by total storage operations on success.

The completed
[ADR-0116](adr/0116-address-selected-checked-core-code.md) adds checker-accepted
closed Core code to Account state and establishes the pure selection foundation
later superseded at the Account boundary by ADR-0118.

The completed [ADR-0117](adr/0117-typed-core-storage-read-suspension.md)
established typed storage-read suspension and resumption. The completed
[ADR-0118](adr/0118-address-selected-host-code-driver.md) connected that
read-only foundation to independently selected code and storage addresses.

The completed
[ADR-0119](adr/0119-storage-write-capability-and-driver.md) supersedes the
read-only execution API with a request-generic driver and combined storage
handler. Core now exposes typed read and write requests with Word and Unit
responses respectively. The driver reuses the exact remaining fuel across
every request; a handled write updates only the working context and survives a
later out-of-fuel result. Code, checkpoint, effects, the storage selector, and
non-selected Accounts are preserved. No commit or rollback behavior is implied.

The completed
[ADR-0120](adr/0120-handled-execution-completeness-and-fuel-stability.md) makes
the generic handled relation executable in both directions and proves that
done and fault results retain their exact final context under additional fuel.
The combined storage, checked, and successful address-selected done APIs reuse
that guarantee. There is intentionally no corresponding out-of-fuel stability
claim, and the slice adds no runtime behavior or request constructor.

The completed tenth slice, [ADR-0028](adr/0028-core-vnext-word-comparison-flags.md),
derives canonical word-valued equality and unsigned greater-than flags from
the existing boolean comparisons. It preserves left-to-right evaluation and
adds no tag or source, standard-library, ABI, opcode, or gas commitment.
Its named expansions, typing, inference, store-threaded cases, weakening,
effects and fault order, exact fuel, boolean preservation, and exact v1/v2
boundaries are proved and tested; the audits pass. Core vNext remains active.
The completed eleventh slice,
[ADR-0029](adr/0029-core-vnext-renaming-simulation.md), provides binder-aware
syntax renaming, typing preservation, structural value/environment/store
relations, simulation for every evaluation form, ground-value and typed-store
exactness, and an exact word-result head-insertion theorem. Static and dynamic
tests cover the foundation. It changes no execution, source, or wire meaning.
The completed twelfth slice,
[ADR-0030](adr/0030-core-vnext-derived-word-comparisons.md), completes the proof
interfaces for the existing `wordNe`, `wordLt`, `wordLe`, and `wordGe`
builders. All four have expansion, typing, inference, renaming, weakening,
store-threaded evaluation, and two truth-case results. Value, type, fuel, fault,
effect, Wire v1 rejection, and exact Wire v2 projection and round-trip tests
pass. Their expansions remain unchanged; the nested-let comparisons keep
left-to-right exactly-once evaluation for arbitrary effectful expressions. No
new syntax, tag, or public behavior is added.
The completed thirteenth slice,
[ADR-0031](adr/0031-core-vnext-derived-word-comparison-flags.md), derives
canonical word-zero-or-one flags for the existing boolean `wordNe`, `wordLt`,
`wordLe`, and `wordGe` builders. Their expansion, typing, inference, renaming,
weakening, four general evaluations, eight value cases, and value, type, fuel,
fault, effect, and wire tests are complete. Right-side fault tests include the
weakening boundary under the less-than binders. The builders preserve evaluation
order, stores, and fuel through ordinary `boolToWord` composition and add no
Core form, wire tag, or public behavior. The next feature is selected by a
separate ADR.
The completed fourteenth slice,
[ADR-0032](adr/0032-core-vnext-derived-builder-renaming-laws.md), adds arbitrary
renaming laws for the eight older conversion, short-circuit, and comparison-flag
builders that previously exposed only weakening laws. It also places
`rename_boolToWord` with `boolToWord` in `Conversions`; every law lives with its
builder. `swap01` golden tests exchange two free variables, and runtime tests
evaluate all three builder families in corresponding environments. Weakening,
runtime semantics, and wire behavior do not change. The next feature is
selected by a separate ADR.
The completed fifteenth slice,
[ADR-0033](adr/0033-core-vnext-direct-unary-primitive-interface.md), completes
the focused proof and test interface for the existing raw `boolNot` and
`wordNot` expressions. Named typing, inference, general and case evaluation,
renaming, and weakening results are complete, as are zero, maximum, and
universal word-complement facts. Tests cover exact 2/3 and 14/15 fuel, raw
faults, effects and final store, Wire v1 rejection, and exact Wire v2 projection
and round trips. It adds no Expr alias, operation tag, meaning, bytes, or public
behavior. The next feature is selected by a separate ADR.
The completed sixteenth slice,
[ADR-0034](adr/0034-core-vnext-totalized-unsigned-division.md), completes focused
proofs and regressions for the existing raw `wordDiv` and `wordMod` operators.
The numerator remains left and the divisor right. A zero divisor returns zero
after both operands evaluate left to right exactly once, retaining effects,
fault order, final store, and fuel. Four Word, two apply, and six evaluation
theorems accompany values including `0 / 0`, type/fault/effect tests, exact 4/5
and 28/29 fuel, Wire v1 rejection, and exact Wire v2 projection and round trips.
It adds no alias, generic API duplicate, tag, schema, Oracle behavior, or byte
change. The next feature is selected by a separate ADR.
These slices add no source spelling for mutable
declarations, assignment, data declarations, patterns, or casts; the conversions
also remain separate from future ABI decoding. Further Core work follows the
roadmap through separate semantic decisions.

This policy is recorded by
[ADR-0018](adr/0018-semantics-first-development-order.md). It changes
development order, not the meaning of any published protocol.

## Status vocabulary

The repository keeps four claims separate:

- Implemented: executable Lean code exists.
- Proved: stated theorems connect the code to independent judgments.
- Published: a versioned schema, profile, and Oracle expose the behavior.
- Runtime-ready: performance has been measured for the intended workload.

An Accepted ADR fixes a decision. It does not imply that the decision has been
implemented. Conversely, an internal implementation does not silently expand
a published profile.

## Decision records

The [ADR directory](adr/) contains durable decisions and rationale.

- ADR-0001 through ADR-0008 define authority, semantic layers, verdicts,
  resolution direction, ABI boundaries, standard-library pinning, and
  observations.
- ADR-0009 through ADR-0011 define the published Semantic Core.
- ADR-0012 through ADR-0017 record the parser, workspace, identity, and
  proposed resolution work.
- ADR-0018 records the semantics-first development pivot.
- ADR-0019 defines the first internal Core vNext feature.
- ADR-0020 defines non-recursive functions and lexical closures.
- ADR-0021 defines binary sums and exhaustive elimination.
- ADR-0022 defines first-order local cells and their explicit local store.
- ADR-0023 defines named algebraic data and direct normalized matching.
- ADR-0024 defines derived boolean and word conversions.
- ADR-0025 defines the derived word-valued zero test.
- ADR-0026 defines derived short-circuit boolean conjunction and disjunction.
- ADR-0027 defines the derived word-valued nonzero test.
- ADR-0028 defines derived word-valued equality and unsigned-greater flags.
- ADR-0029 defines the renaming and environment-insertion proof foundation.
- ADR-0030 completes proof interfaces for existing derived word comparisons.
- ADR-0031 derives word-valued flags for the remaining word comparisons.
- ADR-0032 backfills arbitrary renaming laws for eight older derived builders.
- ADR-0033 completes the focused interface for direct unary primitives.
- ADR-0034 completes focused interfaces for totalized unsigned division and modulo.
- ADR-0035 completes focused interfaces for bounded logical shifts.
- ADR-0036 completes focused interfaces for modular word arithmetic.
- ADR-0037 completes focused interfaces for binary bitwise logic.
- ADR-0038 completes focused interfaces for direct word comparisons.
- ADR-0039 completes an internal 256-bit word leading-zero count.
- ADR-0040 completes internal big-endian word byte selection.
- ADR-0041 completes internal 256-bit arithmetic right shift.
- ADR-0042 completes internal modular word exponentiation.
- ADR-0043 completes internal boolean signed word greater-than.
- ADR-0044 completes effect-safe derived signed word less-than.
- ADR-0045 completes canonical word-valued signed strict comparison flags.
- ADR-0046 completes effect-safe boolean signed non-strict comparisons; its
  independent audit found no P0-P3 issue.
- ADR-0047 completes internal index-left/value-right word sign extension; its
  independent audit found no P0-P3 issue.
- ADR-0048 completes internal dividend-left/divisor-right signed division and
  remainder; its independent audit found no P0-P3 issue.
- ADR-0049 completes canonical word-valued signed non-strict comparison flags;
  its independent audit found no P0-P3 issue.
- ADR-0050 completes dedicated internal ternary modular arithmetic; its
  independent audit found no P0-P3 issue.
- ADR-0051 completes canonical internal runtime scalar representations; its
  independent audit found no P0-P3 issue.
- ADR-0052 completes parametric internal contract-frame halt outcomes; its
  independent audit found no P0-P3 issue.
- ADR-0053 completes the strict internal address-to-word bridge and its
  non-truncating partial inverse; its independent audit found no P0-P3 issue.
- ADR-0054 completes an exact 20-byte big-endian internal address
  representation; its independent audit found no P0-P3 issue.
- ADR-0055 completes proof-only coherence between canonical Address text and bytes.
- ADR-0056 completes the minimal explicit Account and WorldState carrier.
- ADR-0057 completes the minimal internal frame-outcome state resolver.
- ADR-0058 completes the proof-only WorldState observational update algebra.
- ADR-0059 completes the proof-only WorldState storage-write algebra.
- ADR-0060 completes the internal external-checkpoint frame run result.
- ADR-0061 completes the parametric frame effect-journal policy.
- ADR-0062 completes synchronized frame state-and-effect resolution.
- ADR-0063 completes proof-only synchronized child-frame composition.
- [ADR-0064](adr/0064-unresolved-trap-propagation.md) completes the proof-only
  boundary for unresolved trap propagation through Option bind.
- [ADR-0065](adr/0065-resolved-frame-continuation-laws.md) completes the proof-only
  continuation equations for resolved return and revert results.
- [ADR-0066](adr/0066-caller-owned-frame-continuation.md) completes the first
  executable caller-owned frame continuation boundary.
- [ADR-0067](adr/0067-caller-owned-frame-continuation-context.md) completes the
  nominal caller-owned continuation-input bundle.
- [ADR-0068](adr/0068-total-frame-resolution-result.md) fixes the total
  branch-complete frame-resolution result.
- [ADR-0069](adr/0069-ordered-frame-trace-algebra.md) fixes the opt-in ordered
  frame-trace extension algebra.
- [ADR-0070](adr/0070-frame-trace-prefix-relation.md) fixes the proof-only
  ordered frame-trace prefix relation.
- [ADR-0071](adr/0071-trace-prefixed-frame-continuation-context.md) fixes the
  refined continuation context whose exact traces carry prefix evidence.
- [ADR-0072](adr/0072-indexed-frame-trace-extension.md) fixes event-only
  incremental extension from one indexed earlier trace.
- [ADR-0073](adr/0073-parent-indexed-frame-continuation-context.md) fixes the
  continuation context indexed by one exact parent working pair.
- [ADR-0074](adr/0074-trace-extension-parent-context-construction.md) fixes the
  restricted construction path from one indexed trace extension.
- [ADR-0075](adr/0075-parent-indexed-trap-rollback-selection.md) fixes opt-in
  frame-local rollback selection for a parent-indexed trapped frame.
- [ADR-0076](adr/0076-parent-indexed-trap-propagation-payload.md) fixes opt-in
  construction of one caller-designated trap-propagation payload.
- [ADR-0077](adr/0077-parent-indexed-trap-propagation-payload-coherence.md)
  fixes the proof interface for successful payload selection and its trace.
- [ADR-0078](adr/0078-heterogeneous-frame-outcome-trap-reason-mapping.md) fixes
  caller-supplied mapping between different frame trap-reason types.
- [ADR-0079](adr/0079-heterogeneous-frame-run-result-trap-reason-mapping.md)
  fixes the working-state-preserving lift to frame-run results.
- [ADR-0080](adr/0080-heterogeneous-frame-resolution-result-trap-reason-mapping.md)
  fixes caller-supplied reason mapping on total frame-resolution results.
- [ADR-0081](adr/0081-heterogeneous-frame-continuation-context-trap-reason-mapping.md)
  fixes the checkpoint-preserving lift to continuation contexts.
- [ADR-0082](adr/0082-frame-trap-reason-mapping-resolution-naturality.md) fixes
  the proof that context mapping commutes with total resolution.
- [ADR-0083](adr/0083-frame-trap-reason-mapping-continuation-invariance.md)
  fixes `continue?` result invariance under context reason mapping.
- [ADR-0084](adr/0084-heterogeneous-trace-prefixed-frame-continuation-context-trap-reason-mapping.md)
  fixes reason mapping for trace-prefix refined continuation contexts.
- [ADR-0085](adr/0085-heterogeneous-parent-indexed-frame-continuation-context-trap-reason-mapping.md)
  fixes reason mapping for parent-indexed continuation contexts.
- [ADR-0086](adr/0086-nominal-frame-checkpoint-snapshot.md) fixes the nominal
  representation of a caller-supplied synchronized checkpoint snapshot.
- [ADR-0087](adr/0087-frame-checkpointed-working-pair.md) fixes the structural
  pairing of a checkpoint snapshot with independent working values.
- [ADR-0088](adr/0088-continuation-context-from-checkpointed-working-pair.md)
  fixes pure construction of a continuation context from those values.
- [ADR-0089](adr/0089-bytes-aware-frame-resolution-continuation.md) fixes a
  caller-owned non-trapping continuation over total resolution results.
- [ADR-0090](adr/0090-frame-continuation-branch-byte-erasure-coherence.md)
  fixes proof-only compatibility after branch and byte erasure.
- [ADR-0091](adr/0091-frame-resolution-continuation-trap-reason-mapping-invariance.md)
  fixes bytes-aware continuation-result invariance under reason mapping.
- [ADR-0092](adr/0092-checkpointed-working-pair-storage-write.md) fixes a
  working-only lift of strict WorldState storage writes.
- [ADR-0093](adr/0093-checkpointed-working-pair-storage-address.md) fixes one
  retained storage selector for checkpointed working values.
- [ADR-0094](adr/0094-world-state-storage-read.md) fixes strict conditional
  WorldState storage reads.
- [ADR-0095](adr/0095-address-bound-working-storage-read.md) fixes the
  retained-address lift of working storage reads.
- [ADR-0096](adr/0096-world-state-storage-read-write-coherence.md) fixes
  stage-preserving WorldState read/write coherence.
- [ADR-0097](adr/0097-address-bound-working-storage-read-write-coherence.md)
  fixes the carrier-level lift of that coherence.
- [ADR-0098](adr/0098-parent-indexed-frame-initialization.md) fixes the
  parent-indexed frame-initialization recipe.
- [ADR-0099](adr/0099-parent-indexed-frame-initialization-storage-address.md)
  fixes the storage-address adapter for that recipe.
- [ADR-0100](adr/0100-checkpointed-working-pair-storage-write-algebra.md)
  fixes the sequential-write algebra over checkpointed working values.
- [ADR-0101](adr/0101-address-bound-working-storage-write-algebra.md) fixes the
  fixed-selector specialization of that algebra.
- [ADR-0102](adr/0102-address-bound-working-storage-write-preservation.md)
  fixes the structural-preservation observations for that writer.
- [ADR-0103](adr/0103-address-bound-working-storage-write-values-coherence.md)
  fixes the relation between wrapper and underlying write results.
- [ADR-0104](adr/0104-parent-indexed-initialization-continuation-context-coherence.md)
  fixes the equality of two initialization construction routes.
- [ADR-0105](adr/0105-present-working-storage-account-refinement.md) fixes an
  evidence-carrying refinement for a present working Account.
- [ADR-0106](adr/0106-present-working-storage-account-total-read.md) fixes the
  total read from that refinement.
- [ADR-0107](adr/0107-present-working-storage-account-total-write.md) fixes the
  synchronized total write.
- [ADR-0108](adr/0108-present-working-storage-account-total-read-write-coherence.md)
  fixes the read-after-write laws for the total operations.
- [ADR-0109](adr/0109-present-working-storage-account-total-write-algebra.md)
  fixes the algebra of sequential total writes.
- [ADR-0110](adr/0110-present-working-storage-account-total-write-isolation.md)
  fixes the non-selected Account isolation boundary.
- [ADR-0111](adr/0111-present-working-storage-account-total-write-projections.md)
  fixes the total-write data projections.
- [ADR-0112](adr/0112-present-working-storage-account-total-write-presence.md)
  fixes the sparse-storage presence observations.
- [ADR-0113](adr/0113-present-working-storage-account-total-write-sparse-preservation.md)
  fixes distinct-slot sparse-storage preservation.
- [ADR-0114](adr/0114-present-working-storage-account-optional-total-re-refinement-coherence.md)
  fixes optional/total write re-refinement coherence.
- [ADR-0115](adr/0115-parent-indexed-initialization-present-storage-account-refinement.md)
  fixes initialization-to-present-storage refinement.
- [ADR-0116](adr/0116-address-selected-checked-core-code.md)
  fixes checked Account code association, address selection, and raw Core execution.
- [ADR-0117](adr/0117-typed-core-storage-read-suspension.md)
  fixes typed storage-read requests, CEK suspension, and resumable host execution.
- [ADR-0118](adr/0118-address-selected-host-code-driver.md)
  fixes Account host-code migration and fuel-preserving handled execution.
- [ADR-0119](adr/0119-storage-write-capability-and-driver.md)
  fixes typed storage writes, request-generic handled execution, and the
  combined address-selected working-storage driver.
- [ADR-0120](adr/0120-handled-execution-completeness-and-fuel-stability.md)
  fixes two-way handled execution and done/fault stability under additional
  fuel without changing runtime behavior.

Historical ADRs are retained even when their implementation is no longer the
active priority.

## Sources of truth

When two sources disagree, use this order:

1. versioned declarative Lean definitions;
2. Accepted ADRs and the manifests or schemas they designate;
3. executable Lean definitions proved to implement those rules;
4. normative conformance tests;
5. explanatory documentation and comparison evidence.

Pinned Haskell and Rust behavior is evidence, never specification authority.
