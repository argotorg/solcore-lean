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
ADR-0028 are complete, with further Core conversions and primitives planned.
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
[ADR-0045](adr/0045-core-vnext-signed-word-comparison-flags.md) completes
canonical word-valued signed strict comparison flags with no new tag or public
representation. Its independent audit found no P0-P3 issue.
[ADR-0046](adr/0046-core-vnext-signed-word-nonstrict-comparisons.md) completes
effect-safe boolean signed ≤ and ≥ builders with no new tag or public
representation. Its independent audit found no P0-P3 issue.
[ADR-0047](adr/0047-core-vnext-word-sign-extension.md) completes internal word
sign extension with index-left/value-right evaluation and no public Wire
representation. Its independent audit found no P0-P3 issue.
[ADR-0048](adr/0048-core-vnext-signed-word-division.md) completes internal
signed division and remainder with dividend-left/divisor-right evaluation and
no public Wire representation. Its independent audit found no P0-P3 issue.
[ADR-0049](adr/0049-core-vnext-signed-word-nonstrict-comparison-flags.md)
completes internal word-valued signed ≤ and ≥ flags with no new Core tag or
public Wire representation. Its independent audit found no P0-P3 issue.
[ADR-0050](adr/0050-core-vnext-ternary-modular-arithmetic.md) completes the
internal three-operand modular arithmetic slice with no public Wire
representation. Its independent audit found no P0-P3 issue.
[ADR-0051](adr/0051-canonical-runtime-scalars.md) completes the internal
canonical runtime scalar foundation. Strict byte, address, and word
representations are executable and proved without publishing a contract
observation format.
[ADR-0052](adr/0052-contract-frame-outcomes.md) completes the internal
contract-frame outcome slice. Exactly six laws and 10 executable runtime
assertions cover return data, revert data, and a parametric trap reason without
defining state, rollback, or an execution profile. Its independent audit found
no P0-P3 issue.
[ADR-0053](adr/0053-strict-address-word-bridge.md) completes a strict internal
bridge between addresses and words. Widening preserves the numeric value;
narrowing rejects values at or above `2^160` rather than truncating them. Its
two definitions, exactly six axiom-free laws, and 10 runtime assertions are
complete and are not published. The independent audit found no P0-P3 issue.
[ADR-0054](adr/0054-strict-address-bytes.md) completes the strict address byte
slice. Two definitions, exactly six laws, and 10 runtime assertions cover an
exact 20-byte big-endian representation and rejection of every other width,
with no ABI, state, or publication commitment. Its independent audit found no
P0-P3 issue.
[ADR-0055](adr/0055-address-representation-coherence.md) completes the
proof-only Address coherence slice. It adds no public executable API; 15
private helpers and exactly four public laws prove that canonical text and
exact 20-byte decoding agree for arbitrary input.
[ADR-0056](adr/0056-minimal-world-state.md) completes the minimal WorldState
slice. It fixes explicit Account absence and canonical nonzero storage entries
without defining transactions, rollback, balances, or calls.
[ADR-0057](adr/0057-frame-outcome-world-state-resolution.md) completes the
minimal outcome-to-state resolver. Return selects working state, revert selects
the supplied checkpoint, and trap disposition remains deliberately unresolved.
[ADR-0058](adr/0058-world-state-observational-update-algebra.md) completes the
proof-only update algebra for Account and WorldState. It adds no
executable API or new state meaning.
[ADR-0059](adr/0059-world-state-storage-write-algebra.md) completes the
proof-only algebra for conditional WorldState storage writes. It adds no
executable API or operational decision.
[ADR-0060](adr/0060-external-checkpoint-frame-run-result.md) completes the
minimal frame-run payload. It pairs speculative working state with an outcome
while checkpoint ownership remains external.
[ADR-0061](adr/0061-frame-effect-journal-policy.md) completes the parametric
effect policy. It separates rollback-scoped and surviving snapshots without a
concrete event taxonomy or order.
[ADR-0062](adr/0062-synchronized-frame-state-effect-resolution.md) completes the
synchronized resolver. One outcome selects WorldState and parametric
effects together without a new carrier.
[ADR-0063](adr/0063-synchronized-child-frame-composition.md) completes the
proof-only child composition laws. They add no executable API or nested stack.
[ADR-0064](adr/0064-unresolved-trap-propagation.md) completes the proof-only
trap-propagation slice. It records that a trapped synchronized resolution
remains `none` through any continuation, without selecting a trap or
transaction policy.
[ADR-0065](adr/0065-resolved-frame-continuation-laws.md) completes the
proof-only slice that fixes the matching generic continuation equations for
returned and reverted synchronized results without adding an execution API.
[ADR-0066](adr/0066-caller-owned-frame-continuation.md) completes the executable
caller-owned continuation boundary without adding a frame stack, checkpoint
creation, or trace algebra.
[ADR-0067](adr/0067-caller-owned-frame-continuation-context.md) completes the
carrier that groups one completed frame's caller-owned continuation inputs
without defining a full execution frame.
[ADR-0068](adr/0068-total-frame-resolution-result.md) completes the total
frame-resolution result. It converts one continuation context into a
branch-complete value without choosing trap or transaction disposition.
[ADR-0069](adr/0069-ordered-frame-trace-algebra.md) completes the ordered trace
slice. It adds an opt-in finite chronological extension algebra while leaving
event kinds and the generic effect journal open.
[ADR-0070](adr/0070-frame-trace-prefix-relation.md) completes the trace-prefix
proof slice. It adds an explicit non-strict factorization relation, which
ADR-0071 attaches to one context's exact checkpoint and working traces.
[ADR-0071](adr/0071-trace-prefixed-frame-continuation-context.md) completes the
refined continuation boundary. It binds that proof to the exact checkpoint and
working traces in one context without treating value factorization as runtime
lineage.
[ADR-0072](adr/0072-indexed-frame-trace-extension.md) completes indexed trace
extension. It fixes one earlier trace and permits only event-by-event extension,
producing the prefix evidence needed by ADR-0071 without a new fragment append
API.
[ADR-0073](adr/0073-parent-indexed-frame-continuation-context.md) completes the
parent-indexed continuation context. It ties one completed context's
checkpoints and trace prefix to an exact parent working pair while reusing the
existing resolver.
[ADR-0074](adr/0074-trace-extension-parent-context-construction.md) completes
the restricted construction path for that carrier. Its one operation derives
the checkpoints, working trace, and relationship proofs from an ADR-0072
indexed extension without accepting a complete working trace.
[ADR-0075](adr/0075-parent-indexed-trap-rollback-selection.md) completes the
opt-in frame-local trap rollback selector. Return and revert produce `none`;
trap selects parent checkpoint state and rollback with the accumulated internal
working trace without changing the existing generic resolvers.
[ADR-0076](adr/0076-parent-indexed-trap-propagation-payload.md) completes one
opt-in payload selector. It combines ADR-0075's selected pair with the original
trapped outcome for a caller-designated prospective enclosing boundary without
performing or proving runtime propagation.
[ADR-0077](adr/0077-parent-indexed-trap-propagation-payload-coherence.md)
completes two proof-only laws that invert a successful payload selection and
attach the existing non-strict trace-prefix fact to its journal.
[ADR-0078](adr/0078-heterogeneous-frame-outcome-trap-reason-mapping.md)
completes one caller-supplied pure mapping on `FrameOutcome` that preserves
return/revert bytes and changes only trapped reasons.
[ADR-0079](adr/0079-heterogeneous-frame-run-result-trap-reason-mapping.md)
completes the lift to `FrameRunResult`: keep its working state exactly and
delegate only its outcome to ADR-0078.
[ADR-0080](adr/0080-heterogeneous-frame-resolution-result-trap-reason-mapping.md)
completes mapping for total frame-resolution results while preserving
return/revert state, effects, and bytes.
[ADR-0081](adr/0081-heterogeneous-frame-continuation-context-trap-reason-mapping.md)
completes the lift to caller-owned continuation contexts while preserving
every checkpoint and working field.
[ADR-0082](adr/0082-frame-trap-reason-mapping-resolution-naturality.md)
completes the proof that mapping a context before resolution agrees with
mapping its total resolution result afterward.
[ADR-0083](adr/0083-frame-trap-reason-mapping-continuation-invariance.md)
completes the proof that context reason mapping leaves the `Option Next`
value produced by `FrameContinuationContext.continue?` unchanged.
[ADR-0084](adr/0084-heterogeneous-trace-prefixed-frame-continuation-context-trap-reason-mapping.md)
completes the lift to trace-prefix refined contexts without rebuilding
their proof evidence.
[ADR-0085](adr/0085-heterogeneous-parent-indexed-frame-continuation-context-trap-reason-mapping.md)
completes the final lift to parent-indexed contexts while preserving the
exact `parentWorking` index and checkpoint equality.
[ADR-0086](adr/0086-nominal-frame-checkpoint-snapshot.md) completes the
nominal representation of one caller-supplied synchronized checkpoint pair.
It does not claim actual capture, entry, ownership, or runtime execution.
[ADR-0087](adr/0087-frame-checkpointed-working-pair.md) completes the
structural carrier that stores such a snapshot beside an independent working
pair without claiming any relationship or transition.
[ADR-0088](adr/0088-continuation-context-from-checkpointed-working-pair.md)
completes the pure adapter from those values and a caller-supplied outcome
to the existing continuation context.
[ADR-0089](adr/0089-bytes-aware-frame-resolution-continuation.md) completes the
caller-owned continuation seam that preserves return/revert branch,
selected state/effects, and bytes while leaving traps unresolved.
[ADR-0090](adr/0090-frame-continuation-branch-byte-erasure-coherence.md)
completes the proof that erasing branch and bytes from the richer continuation
recovers the existing context continuation.
[ADR-0091](adr/0091-frame-resolution-continuation-trap-reason-mapping-invariance.md)
completes the proof that result-level reason mapping leaves the bytes-aware
continuation result unchanged.
[ADR-0092](adr/0092-checkpointed-working-pair-storage-write.md) completes the
working-only storage-write boundary for checkpointed pairs while preserving
the checkpoint and complete working journal.
[ADR-0093](adr/0093-checkpointed-working-pair-storage-address.md) completes a
storage-address refinement that removes per-write address choice while
retaining the selector beside the checkpointed working values.
[ADR-0094](adr/0094-world-state-storage-read.md) completes a strict WorldState
storage-read boundary that keeps an absent Account distinct from a present
Account whose missing slot reads as zero.
[ADR-0095](adr/0095-address-bound-working-storage-read.md) completes the
stored-address lift of that read over checkpointed working values. It reads
only the working WorldState and never consults the checkpoint.
[ADR-0096](adr/0096-world-state-storage-read-write-coherence.md) completes the
proof interface for observing conditional writes through subsequent reads
without collapsing write failure and read-target absence.
[ADR-0097](adr/0097-address-bound-working-storage-read-write-coherence.md)
completes the proof-only lift of the same-slot and different-slot observations
through the retained-address working carrier.
[ADR-0098](adr/0098-parent-indexed-frame-initialization.md) completes a pure,
parent-indexed initialization recipe that keeps initial WorldState and rollback
values caller-supplied.
[ADR-0099](adr/0099-parent-indexed-frame-initialization-storage-address.md)
completes a canonical adapter from that initialization to the existing
storage-address carrier.
[ADR-0100](adr/0100-checkpointed-working-pair-storage-write-algebra.md)
completes a proof-only lift of overwrite and independent-write commutation to
the address-parameterized checkpointed working write.
[ADR-0101](adr/0101-address-bound-working-storage-write-algebra.md) completes
a thin lift of same-slot overwrite and distinct-slot commutation through the
retained storage selector.
[ADR-0102](adr/0102-address-bound-working-storage-write-preservation.md)
completes stage-preserving observations that retained-address writes keep the
same selector, checkpoint, and working effect journal.
[ADR-0103](adr/0103-address-bound-working-storage-write-values-coherence.md)
completes the proof that projecting a retained-address write result to its
values recovers the underlying address-parameterized write.
[ADR-0104](adr/0104-parent-indexed-initialization-continuation-context-coherence.md)
completes the proof that the parent-indexed trace-extension route and
checkpointed-working-pair route construct the same plain continuation context.
[ADR-0105](adr/0105-present-working-storage-account-refinement.md) accepts a
partial refinement that retains the exact address-bound context, selected
working Account, and its presence evidence; implementation is complete.
[ADR-0106](adr/0106-present-working-storage-account-total-read.md) accepts a
total slot read from that proven-present Account and a coherence law with the
existing conditional context read; implementation is complete.
[ADR-0107](adr/0107-present-working-storage-account-total-write.md) accepts a
total slot write that synchronizes the retained Account, working-state entry,
and new presence evidence; implementation is complete.
[ADR-0108](adr/0108-present-working-storage-account-total-read-write-coherence.md)
accepts same-slot and distinct-slot read-after-write laws for the total carrier;
implementation is complete.
[ADR-0109](adr/0109-present-working-storage-account-total-write-algebra.md)
accepts overwrite and distinct-slot commutation laws for total carrier writes;
implementation is complete.
[ADR-0110](adr/0110-present-working-storage-account-total-write-isolation.md)
accepts non-selected working Account isolation for total carrier writes;
implementation is complete.
[ADR-0111](adr/0111-present-working-storage-account-total-write-projections.md)
accepts the four selector, checkpoint, journal, and stored-Account projections;
implementation is complete.
[ADR-0112](adr/0112-present-working-storage-account-total-write-presence.md)
accepts zero deletion and nonzero sparse-entry presence after total writes;
implementation is complete.
[ADR-0113](adr/0113-present-working-storage-account-total-write-sparse-preservation.md)
accepts preservation of every distinct sparse-storage entry at the Account and
proven-present carrier boundaries; implementation is complete.
[ADR-0114](adr/0114-present-working-storage-account-optional-total-re-refinement-coherence.md)
accepts equality between optional write plus canonical refinement and the total
writer; implementation is complete.
[ADR-0115](adr/0115-parent-indexed-initialization-present-storage-account-refinement.md)
accepts a partial adapter from parent-indexed initialization to the existing
proven-present storage carrier; implementation is complete.
[ADR-0116](adr/0116-address-selected-checked-core-code.md) accepts checked
Core code as rollback-visible Account state and fixes address-selected raw Core
execution; implementation is complete. It deliberately leaves frame outcomes,
ABI conversion, contract inputs, and WorldState effects unresolved.

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
| Address-selected checked Core code | Complete | Admission, Account association, selection, stateful execution, termination threshold, and no-fault safety proved | Not published |
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
| Internal signed word comparisons | Complete | Complete | Explicitly excluded from Wire v1/v2 |
| Internal signed comparison flags | Complete | Complete | Explicitly excluded from Wire v1/v2 |
| Internal word sign extension | Complete | Complete | Explicitly excluded from Wire v1/v2 |
| Internal signed division and remainder | Complete | Complete | Explicitly excluded from Wire v1/v2 |
| Internal ternary modular arithmetic | Complete | Complete | Explicitly excluded from Wire v1/v2 |
| Canonical runtime scalar observations | Complete | Complete | Not published |
| Internal contract frame outcomes | Complete | Complete | Not published |
| Strict address and word bridge | Complete | Complete | Not published |
| Strict 20-byte address representation | Complete | Complete | Not published |
| Address text and byte coherence | Complete | Complete | Not published |
| Minimal Account and WorldState carrier | Complete | Complete | Not published |
| Frame-outcome WorldState resolution | Complete | Complete | Not published |
| WorldState observational update algebra | Complete | Complete | Not published |
| WorldState storage-write algebra | Complete | Complete | Not published |
| External-checkpoint frame run result | Complete | Complete | Not published |
| Parametric frame effect journal policy | Complete | Complete | Not published |
| Synchronized frame state/effect resolution | Complete | Complete | Not published |
| Synchronized child-frame composition | Complete | Complete | Not published |
| Unresolved trap propagation | Complete | Complete | Not published |
| Resolved frame continuation laws | Complete | Complete | Not published |
| Caller-owned frame continuation | Complete | Complete | Not published |
| Caller-owned frame continuation context | Complete | Complete | Not published |
| Total frame resolution result | Complete | Complete | Not published |
| Ordered frame trace algebra | Complete | Complete | Not published |
| Frame trace prefix relation | Complete | Complete | Not published |
| Trace-prefixed frame continuation context | Complete | Complete | Not published |
| Indexed frame trace extension | Complete | Complete | Not published |
| Parent-indexed frame continuation context | Complete | Complete | Not published |
| Parent-indexed frame continuation construction | Complete | Complete | Not published |
| Parent-indexed trapped-frame rollback selection | Complete | Complete | Not published |
| Parent-indexed trap propagation payload selection | Complete | Complete | Not published |
| Parent-indexed trap propagation payload coherence | Complete | Complete | Not published |
| Heterogeneous frame-outcome trap-reason mapping | Complete | Complete | Not published |
| Heterogeneous frame-run-result trap-reason mapping | Complete | Complete | Not published |
| Heterogeneous frame-resolution-result trap-reason mapping | Complete | Complete | Not published |
| Heterogeneous frame-continuation-context trap-reason mapping | Complete | Complete | Not published |
| Frame trap-reason mapping resolution naturality | Complete | Complete | Not published |
| Frame trap-reason mapping continuation-result invariance | Complete | Complete | Not published |
| Heterogeneous trace-prefixed continuation-context trap-reason mapping | Complete | Complete | Not published |
| Heterogeneous parent-indexed continuation-context trap-reason mapping | Complete | Complete | Not published |
| Nominal frame checkpoint snapshot | Complete | Complete | Not published |
| Frame checkpointed working pair | Complete | Complete | Not published |
| Continuation context from checkpointed working pair | Complete | Complete | Not published |
| Bytes-aware frame resolution continuation | Complete | Complete | Not published |
| Frame continuation branch/byte erasure coherence | Complete | Complete | Not published |
| Frame-resolution continuation trap-reason mapping invariance | Complete | Complete | Not published |
| Checkpointed working-pair storage write | Complete | Complete | Not published |
| Checkpointed working-pair storage address | Complete | Complete | Not published |
| Conditional WorldState storage read | Complete | Complete | Not published |
| Address-bound working storage read | Complete | Complete | Not published |
| WorldState storage read/write coherence | No new operation | Complete | Not published |
| Address-bound working storage read/write coherence | No new operation | Complete | Not published |
| Parent-indexed frame initialization | Complete | Complete | Not published |
| Parent-indexed initialization storage-address adapter | Complete | Complete | Not published |
| Checkpointed working-pair storage-write algebra | No new operation | Complete | Not published |
| Address-bound working storage-write algebra | No new operation | Complete | Not published |
| Address-bound working storage-write preservation | No new operation | Complete | Not published |
| Address-bound working storage-write values coherence | No new operation | Complete | Not published |
| Parent-indexed initialization continuation-context coherence | No new operation | Complete | Not published |
| Present working storage Account refinement | Complete | Complete | Not published |
| Present working storage Account total read | Complete | Complete | Not published |
| Present working storage Account total write | Complete | Complete | Not published |
| Present working storage Account total read/write coherence | No new operation | Complete | Not published |
| Present working storage Account total-write algebra | No new operation | Complete | Not published |
| Present working storage Account total-write isolation | No new operation | Complete | Not published |
| Present working storage Account total-write projections | No new operation | Complete | Not published |
| Present working storage Account total-write presence | No new operation | Complete | Not published |
| Present working storage Account total-write sparse preservation | No new operation | Complete | Not published |
| Present working storage Account optional/total re-refinement coherence | No new operation | Complete | Not published |
| Parent-indexed initialization present storage Account refinement | Partial adapter complete | Complete | Not published |
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
- further closed Core conversions or primitives after the completed strict
  address-and-word bridge;
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

## Completed Core vNext signed comparison flag slice

[ADR-0045](adr/0045-core-vnext-signed-word-comparison-flags.md) derives
`wordSgtFlag` and `wordSltFlag` by applying `boolToWord` to the existing signed
boolean comparisons. True becomes word one and false becomes word zero. Source
left remains before source right, with only `wordSlt`'s bound values reversed.
The two exact builders have ten static and ten evaluation theorems. Same-sign
cases conditionally produce canonical word one or zero, while cross-sign cases
produce constant results. Values/types, invalid payloads on both sides, ordered
faults, effects/final store, exact 7/8 and 31/32 `wordSgtFlag` fuel, exact 13/14
and 37/38 `wordSltFlag` fuel, and frozen v1/v2 builder, handwritten expansion,
and `wordSgt` rejection are complete. Public behavior remains unchanged;
the independent audit found no P0-P3 issue.

## Completed Core vNext signed non-strict comparison slice

[ADR-0046](adr/0046-core-vnext-signed-word-nonstrict-comparisons.md) derives
boolean `wordSle` by negating signed greater-than and `wordSge` by negating the
effect-safe signed less-than builder. Source left remains before source right;
only `wordSge` reverses the computed bound values. The exact twenty-theorem and
sign/equality, type, underlying invalid and ordered-fault, effect/store, exact
6/7, 30/31, 12/13, and 36/37 fuel, and frozen-Wire regressions are complete.
Focused and full builds, the full test runner, kernel policy, and metadata
verification pass. Public behavior remains unchanged; the independent audit
found no P0-P3 issue.

## Completed Core vNext word sign-extension slice

[ADR-0047](adr/0047-core-vnext-word-sign-extension.md) adds internal
`BinaryOp.wordSignExtend`. The left word selects a byte width and the right word
is the value. Indices below 32 extend the selected sign bit through the upper
word; indices at least 32 return the value unchanged. The exact ten theorems
and focused regressions cover indices 0, 1, 31, 32, and maximum, values and
types, raw and ordered faults, effects and final stores, exact 4/5 and 28/29
fuel, and frozen v1/v2 rejection. Focused/full builds, tests, kernel policy,
and metadata verification pass. There is no public format or source
commitment; the independent audit found no P0-P3 issue.

## Completed Core vNext signed division and remainder slice

[ADR-0048](adr/0048-core-vnext-signed-word-division.md) adds internal
`BinaryOp.wordSdiv` and `BinaryOp.wordSmod`. Both evaluate dividend then
divisor. Division rounds toward zero; remainder follows the dividend's sign;
zero divisors return zero after both operands evaluate; and minimum divided by
negative one wraps. The exact fourteen theorems and focused sign,
zero, minimum, type, raw and ordered fault, effect/final-store, exact 4/5 and
28/29 fuel, and frozen v1/v2 rejection regressions are complete. Focused/full
builds and tests, kernel policy, and metadata verification pass. They add no
public format or source commitment; the independent audit found no P0-P3 issue.

## Completed Core vNext signed non-strict comparison flag slice

[ADR-0049](adr/0049-core-vnext-signed-word-nonstrict-comparison-flags.md)
derives `wordSleFlag` and `wordSgeFlag` from the existing boolean comparisons.
Both return canonical word one or zero and keep source left-to-right evaluation;
only `wordSgeFlag` swaps already computed bound values. The exact ten static
and ten evaluation theorems cover same-sign, cross-sign, equality, and
canonical word one/zero results. Focused type, underlying and ordered fault,
effect/final-store, exact 9/10, 33/34, 15/16, and 39/40 fuel, and frozen
builder/handwritten-expansion/v2-`wordSgt` rejection regressions are complete.
Focused/full builds and tests, kernel policy, and metadata verification pass.
There is no public format or source commitment; the independent audit found no
P0-P3 issue.

## Completed Core vNext ternary modular arithmetic slice

[ADR-0050](adr/0050-core-vnext-ternary-modular-arithmetic.md) adds
`TernaryOp.wordAddMod`, `wordMulMod`, and `Expr.ternary`. First value, second
value, and modulus evaluate in source order. Nonzero moduli reduce a
full-precision natural sum or product; a zero modulus returns zero only after
all operands evaluate. The exact fourteen focused theorems sit on
generic typing, checking, Safety, correspondence, and renaming support.
Focused result/type, dedicated raw fault, ordered fault/effect/store, exact 6/7
and 42/43 fuel, no-prewrap, and frozen v1/v2 rejection regressions are complete.
Focused/full builds and tests, kernel policy, metadata, trust-zero, and axiom
checks pass. There is no public format or source commitment; the independent
audit found no P0-P3 issue.

## Completed canonical runtime scalar slice

[ADR-0051](adr/0051-canonical-runtime-scalars.md) fixes internal `Bytes`,
160-bit `Address`, existing 256-bit `Word`, strict lowercase `0x` hexadecimal,
and a 32-byte big-endian Word representation. It changes no Core expression,
public Wire format, source syntax, ABI rule, contract state, or observation
profile. A reusable fixed-radix and hexadecimal foundation supports the scalar
APIs. Exactly sixteen focused theorems prove their lengths, round trips,
canonicality, injectivity, and big-endian agreement with `Word.byteAt`.
Executable tests cover boundaries, strict rejection, accepted-input
canonicalization, a complete 32-byte big-endian fixture, and indexed agreement
with `Word.byteAt`. The frozen Wire v1 and v2 codecs remain unchanged;
compatibility tests confirm that their representative Word output matches the
new encoder. Focused and full checks pass, and the independent audit found no
P0-P3 issue.

## Completed contract frame outcome slice

[ADR-0052](adr/0052-contract-frame-outcomes.md) fixes the next internal carrier:
return with return data, revert with revert data, or trap with a reason supplied
by later semantics. The trap-reason type remains a parameter. Total projections
distinguish a present empty byte string from a payload that does not belong to
the selected halt kind. Exactly six laws characterize all three kinds and all
three successful projections. Ten executable runtime assertions cover empty
and zero-padded return and revert data, matching and
nonmatching projections, two distinct trap reasons, and constructor
distinction.

This slice is only a syntax-independent halt vocabulary. It does not connect
Core results to contract entry, add state or rollback, choose trap reasons or
an EVM revision, or publish a Wire, Oracle, verdict, or observation format.
Focused and full builds and tests, trust-zero, semantic-kernel, metadata,
axiom, document-link, and diff checks pass. The independent audit found no
P0-P3 issue.

## Completed strict address and word bridge slice

[ADR-0053](adr/0053-strict-address-word-bridge.md) specifies a lossless
conversion from the existing 160-bit `Address` to `Core.Word` and a strict
partial inverse. Narrowing succeeds only below `2^160` and preserves the same
natural-number value; overflow returns `none` instead of truncating high bits.

The implementation contains two conversions, exactly six focused axiom-free
laws, and exactly 10 direct runtime assertions. Tests cover zero, one, a
nontrivial middle value, the maximum address, and rejection of both `2^160` and
the maximum Word. Focused and full builds and tests, trust-zero,
semantic-kernel, metadata, axiom, document-link, and diff checks pass. The
independent audit found no P0-P3 issue. The slice changes no scalar text, Core
operation, source or ABI rule, contract state, rollback behavior, or published
interface.

## Completed strict address byte slice

[ADR-0054](adr/0054-strict-address-bytes.md) specifies two conversions between
the existing 160-bit Address and exactly 20 most-significant-byte-first octets.
Exactly six laws cover width, both round-trip directions, the decoder success
domain, injectivity, and agreement with widened Word byte indices 12 through
31. Exactly 10 runtime assertions cover independent zero, one, and maximum
fixtures; a representative-four-value round trip; 19- and 21-byte rejection;
19 leading zeros for address one; and all 20 aligned bytes for each
representative.

The slice changes no address text, numeric bridge, source or ABI rule, contract
state, EVM behavior, or published format.
Laws one through five depend on `propext` and `Quot.sound`; law six additionally
depends on `Classical.choice`. No custom axiom or `sorryAx` is present. Focused
and full builds and tests, trust-zero, semantic-kernel, metadata,
document-link, and diff checks pass. The independent audit found no P0-P3
issue.

## Completed Address representation coherence slice

[ADR-0055](adr/0055-address-representation-coherence.md) connects the completed
Address text and exact 20-byte codecs without adding an executable API. The
exact four laws cover canonical encoding equality, both encoded-input
decoder boundaries, and complete arbitrary-text decoder-bind coherence.
Exactly eight runtime assertions cover zero, one, middle, maximum, 19/20/21
bytes, and malformed or noncanonical text.

Fifteen private helper theorems support the public boundary. All four public
laws report `propext`, `Classical.choice`, and `Quot.sound`; there is no custom
axiom or unchecked declaration. Trust-zero, focused and full builds and tests,
semantic-kernel, and metadata checks pass. ABI behavior, source casts, contract
state, EVM rules, and every public format remain unchanged. The independent
audit found no P0-P3 issue.

## Completed minimal WorldState slice

[ADR-0056](adr/0056-minimal-world-state.md) introduces exactly two carriers and
eight public operations over private semantic lookup functions. The finite Word
and Address domains keep these partial maps finite without exposing a tree,
hash, iteration, or insertion order. An absent Account stays distinct from a
present empty Account. Missing storage reads as Word zero; zero writes
canonically erase the entry; and storage writes never create a missing Account.

The exact twelve laws and twelve runtime assertions cover Account
lookup, explicit insertion, storage presence and reads, zero deletion,
nonzero insertion, absent-Account write failure, and preservation at different
keys and addresses. Transactions, rollback, ABI, balances, code, calls,
ordering, serialization, and publication remain separate decisions.

The two carriers expose only private semantic lookup functions; Account also
contains a private zero-free proposition. Constructors and fields are private,
and there is no concrete map, `BEq`, `DecidableEq`, or `Repr`. Privacy,
recursor, trust-zero, build, test, metadata, and semantic-kernel checks pass.
Ten laws report only `[propext]`; the two empty Account laws additionally
report `Quot.sound`. No custom axiom, `sorryAx`, or unchecked declaration is
present. The final independent audit found no P0-P3 issue.

## Completed frame-outcome state-resolution slice

[ADR-0057](adr/0057-frame-outcome-world-state-resolution.md) provides exactly one
internal operation, three constructor laws, and three runtime assertions.
Returned frames select the working WorldState; reverted frames select the
supplied checkpoint; trapped frames return `none` because trap disposition is
not yet decided. That `none` does not mean rollback, deletion, Account absence,
or an inconclusive execution. Nested checkpoints, surviving effects,
transaction atomicity, ABI, Core-result adaptation, EVM, and gas remain outside
the slice.

The definition and properties modules contain 24 and 32 lines. The 53-line test
module plus two runner lines exercises all constructors using distinguishable
states. All three laws report exactly `[propext]`; no custom axiom, `sorryAx`,
or unchecked declaration is present. Builds, tests, trust-zero, kernel,
metadata, link, and diff checks pass.

## Completed WorldState observational update algebra

[ADR-0058](adr/0058-world-state-observational-update-algebra.md) provides exactly
six public laws, two compile-time theorem-use examples, and four runtime
assertions, with no new executable API, carrier, or instance. Extensionality
uses public lookups; same-key updates overwrite; and distinct-slot or
distinct-address updates commute. The commutation laws are not simp rules.
This proof-only slice makes no trap, nested-effect, lifecycle, delta, ordering,
serialization, ABI, Core-adapter, EVM, or gas decision.

The extensionality and algebra modules contain 31 and 66 lines, with one
umbrella import each. Two compile-time examples and four runtime assertions are
in a 76-line test module with two runner lines. The two extensionality laws are
`@[ext]`, only the two overwrite laws are `@[simp]`, and both commutation laws
remain non-simp. All six laws report exactly `[propext, Quot.sound]`, with no
`Classical.choice`, custom axiom, `sorryAx`, or unchecked declaration. Full
validation and independent audits pass.

## Completed WorldState storage-write algebra

[ADR-0059](adr/0059-world-state-storage-write-algebra.md) provides one private
helper, exactly four public laws, and four runtime assertions, with no public
executable API, carrier, or instance. The laws cover sequential overwrite,
distinct-slot and distinct-address commutation, and zero deletion while the
Account remains present. An absent-address `none` is only storage-write failure;
it is not a trap, revert, rollback, or inconclusive result. Operational effects,
lifecycle, serialization, ABI, Core adaptation, EVM, and gas remain undecided.

The 189-line properties module plus one umbrella import publishes exactly four
laws. Only overwrite is simp; both commutation laws and zero deletion are
non-simp. The first three laws report `[propext, Quot.sound]`, while zero
deletion reports `[propext]`. No `Classical.choice`, custom axiom, `sorryAx`, or
unchecked declaration is present. Four assertions in a 94-line definition-only
test module plus two runner lines pass full validation and independent audits.

## Completed external-checkpoint frame run result

[ADR-0060](adr/0060-external-checkpoint-frame-run-result.md) provides exactly one
public carrier and one named executable resolver. Its public fields expose the
speculative working WorldState and parametric FrameOutcome intentionally. Three
constructor laws and three runtime assertions cover return, revert, and trap;
tests also observe the payload projections. The checkpoint remains caller-owned
and trap resolution remains open. Nested frames, surviving effects,
transactions, ABI, Core adaptation, EVM, gas, and publication remain outside.

The carrier definition contains 28 lines plus one umbrella import. Its two
fields and generated constructor, projections, and recursor are intentional;
there are no derived instances, extensionality laws, or helpers. One named
resolver and the three simp laws in the 32-line properties module all report
`[propext]`. Three assertions in a 68-line definition-only test module plus two
runner lines cover both resolution and projections. Full validation and audits
pass.

## Completed parametric frame effect policy

[ADR-0061](adr/0061-frame-effect-journal-policy.md) provides one public carrier,
one named resolver, five laws, and five Nat-fixture runtime assertions. Return
keeps the working journal; revert restores checkpoint rollback state while the
working trace survives; trap remains unresolved. Two nested bind laws cover
child return followed by parent revert and child revert followed by parent
revert. No concrete effects, trace order, append algebra, invocation stack,
transaction, ABI, Core adaptation, EVM, gas, or publication is selected.

The definition and properties modules contain 32 and 57 lines with one umbrella
import each. The carrier has two public fields and one resolver. Exactly five
laws comprise three simp constructor equations and two non-simp nested laws;
the resolver and all laws introduce no axioms. Five assertions in a 64-line
definition-only test module plus two runner lines pass full validation. The
independent audits found no P0-P3 issue.

## Completed synchronized frame state/effect resolution

[ADR-0062](adr/0062-synchronized-frame-state-effect-resolution.md) provides one
public executable operation, five laws, and three definition-only runtime
assertions, with no carrier, instance, or helper. Return keeps both working
components; revert restores checkpoint WorldState and rollback effects while
preserving working trace; trap remains unresolved. Two projection laws prove
coherence with the existing independent resolvers. Nested composition, trace
ownership, concrete effects or order, transactions, ABI, Core adaptation, EVM,
gas, and publication remain outside.

The 27-line definition module and 78-line properties module each have one
umbrella import. No carrier, instance, or helper is added. Exactly five laws
split into three simp constructor equations and two non-simp coherence laws;
the resolver and every law report `[propext]`. Three assertions in a 66-line
definition-only test module plus two runner lines cover both projections. Full
validation and independent P0-P3 audits pass.

## Completed synchronized child-frame composition

[ADR-0063](adr/0063-synchronized-child-frame-composition.md) provides exactly two
non-simp laws and two definition-only runtime assertions, with no carrier, API,
instance, or helper. Child return is adopted before parent revert; child revert
first restores the child checkpoint. Both paths finish at parent checkpoint
WorldState and rollback state while preserving the child's accumulated working
trace. That trace already includes the parent prefix. Stack ownership,
invocation, checkpoint creation, append/order, transactions, trap policy, ABI,
Core adaptation, EVM, gas, and publication remain outside.

The 47-line properties module plus one umbrella import contains two non-simp,
`rfl` laws, each reporting `[propext]`. Two assertions in a 74-line
definition-only test module plus two runner lines inspect both intermediate and
final projections. No carrier, API, instance, or helper is added. Full
validation and independent P0-P3 audits pass.

## Completed unresolved trap propagation

[ADR-0064](adr/0064-unresolved-trap-propagation.md) adds no carrier, executable
API, instance, or helper. Its 26-line properties module plus one umbrella
import publishes exactly one non-simp `rfl` law with axiom set `[propext]`.
One assertion in a 34-line definition-only test module plus two runner lines
checks a concrete reason, the trapped `none`, and sentinel-bind propagation.

The three implementation commits contain 122, 27, and 36 changed lines; this
completion update is the fourth commit. Full validation and independent P0-P3
audits pass. `none` remains limited to unresolved trap disposition and chooses
no rollback, working state, trace, fatal, or transaction policy.

## Completed resolved frame continuation laws

[ADR-0065](adr/0065-resolved-frame-continuation-laws.md) adds no carrier,
executable API, instance, or helper. Its proof-only scope is exactly two
non-simp laws: after synchronized return or revert resolution, binding an
arbitrary continuation invokes it with exactly the selected state-and-effect
pair. Together with ADR-0064, these equations cover every FrameOutcome
constructor.

A 44-line properties module plus one umbrella import publishes the two `rfl`
laws with exact axiom sets `[propext]`. A 61-line definition-only test module
plus two runner lines provides exactly two sentinel assertions, one for return
and one for revert. The implementation commits contain 147, 45, and 63 changed
lines; this completion update is the fourth commit. Full validation and
independent P0-P3 audits pass.

Checkpoint creation and ownership, trace append and ordering, invocation,
transactions, and trap disposition remain separate decisions.

## Completed caller-owned frame continuation

[ADR-0066](adr/0066-caller-owned-frame-continuation.md) adds exactly one public
operation and no carrier, instance, or helper. The caller supplies state and
effect checkpoints plus a working journal whose trace is already accumulated.
The operation resolves one FrameRunResult and invokes an arbitrary Option
continuation only when synchronized resolution succeeds.

The 25-line definition module plus one umbrella import contains the operation,
whose axiom set is `[propext]`. A 59-line properties module plus one umbrella
import publishes exactly three simp `rfl` constructor laws, each with axiom set
`[propext]`. A 71-line definition-only test module plus two runner lines
contains exactly three assertions.

The four implementation commits contain 149, 26, 60, and 73 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. Parent-frame shape, checkpoint creation, trace append/order,
transaction atomicity, and diagnostic failure carriers remain separate.

## Completed caller-owned frame continuation context

[ADR-0067](adr/0067-caller-owned-frame-continuation-context.md) adds exactly one
carrier with four public fields and one delegating continuation operation. It
bundles a state checkpoint, effect checkpoint, working journal, and the existing
FrameRunResult. It does not duplicate working WorldState or outcome.

A 35-line definition module plus one umbrella import contains the carrier and
operation, both with axiom set `[propext]`. A 23-line properties module plus one
umbrella import publishes exactly one non-simp `rfl` coherence law with axiom
set `[propext]`. An 87-line definition-only test module plus two runner lines
contains exactly three assertions.

The four implementation commits contain 171, 36, 24, and 89 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. The carrier does not establish checkpoint lineage,
trace-prefix membership, a frame stack, or transaction behavior.

## Completed total frame resolution result

[ADR-0068](adr/0068-total-frame-resolution-result.md) adds exactly one public
three-constructor carrier and one total context-resolution operation. Return
and revert carry payload plus selected state/effects; trap carries its reason
and selects no state/effect pair.

A 43-line definition module plus one umbrella import contains the carrier and
operation. A 50-line properties module plus one umbrella import contains
exactly three simp `rfl` laws. The carrier, operation, and laws report
`[propext]`. A 77-line definition-only test module plus two runner lines
contains exactly three assertions.

The four implementation commits contain 198, 44, 51, and 79 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. Stack/depth, checkpoint lineage, trace append/order, trap
disposition, and transaction atomicity remain outside.

## Completed ordered frame trace algebra

[ADR-0069](adr/0069-ordered-frame-trace-algebra.md) adds one constructor-private
`FrameTrace Event` carrier with empty, chronological observation, tail record,
and earlier-before-later append operations. It is an opt-in `TraceState` for
the existing generic FrameEffectJournal, not a replacement for that parameter.

A 37-line definition module plus one umbrella import contains the carrier and
four operations. A 65-line properties module plus one umbrella import contains
exactly seven axiom-free laws. An 87-line definition-only test module plus two
runner lines contains exactly six assertions.

The four implementation commits contain 210, 38, 66, and 89 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. Event taxonomy, trace lineage, call scheduling, and
transaction behavior remain outside.

## Completed frame trace prefix relation

[ADR-0070](adr/0070-frame-trace-prefix-relation.md) adds exactly one
proposition-valued relation: an earlier trace is a prefix of a later trace when
some ordered fragment extends it to that later value.

A 16-line definition module plus one umbrella import contains the relation. A
37-line properties module plus one umbrella import contains exactly four
non-simp, axiom-free laws. A 41-line definition-only compile-regression module
plus one main test import contains exactly four private examples and no runtime
call.

The four implementation commits contain 165, 17, 38, and 42 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. Runtime provenance, frame identity, checkpoint ownership,
and trap or transaction behavior remain outside.

## Completed trace-prefixed frame continuation context

[ADR-0071](adr/0071-trace-prefixed-frame-continuation-context.md) adds exactly
one refined carrier over `FrameContinuationContext`. Its proof field relates
the exact effect-checkpoint trace to the exact working trace in that same value.
Existing continuation and total-resolution operations remain available without
aliases.

A 21-line definition module plus one umbrella import contains the carrier. It
reports exactly `[propext]` and adds no operation, theorem, properties module,
instance, coercion, alias, or helper. A 52-line definition-only regression
module plus one main test import contains exactly three private examples and no
runtime call.

The three implementation commits contain 174, 22, and 53 changed lines; this
completion update is the fourth commit. Full validation and independent P0-P3
audits pass. Producer identity, event authenticity, checkpoint ownership,
nested scheduling, trap disposition, and transaction atomicity remain outside.

## Completed indexed frame trace extension

[ADR-0072](adr/0072-indexed-frame-trace-extension.md) adds one
constructor-private `FrameTrace.ExtensionFrom earlier` carrier. `start` fixes
the earlier trace once, `record` accepts one event, and `toTrace` observes the
full chronological value. A canonical theorem supplies prefix evidence.

The 43-line definition module plus one umbrella import contains exactly three
operations and the non-simp canonical theorem. A 34-line properties module plus
one umbrella import contains exactly two simp laws. All declarations are
axiom-free. A 71-line definition-only test module plus one import and one call
contains three assertions and one private ADR-0071 integration example.

The four implementation commits contain 206, 44, 39, and 73 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. The API adds no indexed fragment append or named fragment
projection. Runtime provenance, checkpoint ownership, child identity, and
transaction behavior remain outside.

## Completed parent-indexed frame continuation context

[ADR-0073](adr/0073-parent-indexed-frame-continuation-context.md) adds one
`ParentIndexedFrameContinuationContext` indexed by a designated parent working
WorldState and effect journal. It inherits the ADR-0071 trace-prefix proof and
adds equality between its checkpoints and that exact pair.

The 22-line carrier module plus one umbrella import adds no operation. A
66-line properties module plus one umbrella import publishes exactly three
non-simp laws. The carrier and all three laws report exactly `[propext]`. A
101-line definition-only test module plus one import and one call contains
exactly three runtime assertions covering return, revert, and trap.

The four implementation commits contain 216, 23, 67, and 103 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. Runtime parent/child provenance, scheduling, trap
disposition, and transaction atomicity remain outside.

## Completed parent-indexed frame continuation construction

[ADR-0074](adr/0074-trace-extension-parent-context-construction.md) adds exactly
one `ParentIndexedFrameContinuationContext.fromTraceExtension` operation. It
accepts a parent working pair, working rollback value, indexed trace extension,
and frame result, then constructs the exact checkpoints and working journal
while deriving both stored relationship proofs.

A 31-line definition module plus one umbrella import contains the operation. A
58-line properties module plus one umbrella import publishes exactly four simp
`rfl` projection laws. The operation and all four laws report exactly
`[propext]`. An 87-line definition-only test module plus two runner lines
contains exactly three assertions covering checkpoint observations, the
nonduplicated extended working trace, and preservation of the supplied result.

The four implementation commits contain 217, 32, 59, and 89 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. Runtime provenance, invocation, scheduling, trap
disposition, and transaction behavior remain outside.

## Completed parent-indexed trapped-frame rollback selection

[ADR-0075](adr/0075-parent-indexed-trap-rollback-selection.md) adds exactly one
`ParentIndexedFrameContinuationContext.trapRollback?` selector. Return and
revert produce `none`; trap selects the indexed parent state and rollback with
the accumulated working trace.

A 30-line definition module plus one umbrella import contains the selector. A
56-line properties module plus one umbrella import publishes exactly three
non-simp outcome laws. The selector and all three laws report exactly
`[propext]`. An 84-line definition-only test module plus two runner lines
contains exactly three assertions covering return, revert, and trapped
frame-local selection with distinct parent and working witnesses.

The four implementation commits contain 226, 31, 57, and 86 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. Internal `FrameTrace` retention is the new narrow policy
selected here; it does not claim that concrete contract logs survive a trap.
Propagation, fatality, resumption, and transaction disposition remain outside.

## Completed parent-indexed trap propagation payload selection

[ADR-0076](adr/0076-parent-indexed-trap-propagation-payload.md) adds one
`ParentIndexedFrameContinuationContext.trapPropagationPayload?` operation. It
maps the ADR-0075 rollback pair into a prospective enclosing frame result and
selected journal while preserving the original trapped outcome.

A 24-line definition module plus one umbrella import contains the selector. A
56-line properties module plus one umbrella import publishes exactly three
non-simp outcome laws. The selector, its generated equation, and all three laws
report exactly `[propext]`. A 91-line definition-only test module plus two
runner lines contains exactly three assertions covering return, revert, and
trap with distinct designated enclosing and working state and rollback values,
the exact parent-then-nested trace, and one preserved concrete trap reason.

The four implementation commits contain 224, 25, 57, and 93 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. The completed operation only constructs a value for one
caller-designated prospective enclosing boundary. It does not perform or prove
a runtime transition, parent execution, ancestry, handling, repeated
propagation, or transaction policy.

## Completed parent-indexed trap propagation payload coherence

[ADR-0077](adr/0077-parent-indexed-trap-propagation-payload-coherence.md)
adds exactly two non-simp proof laws and no new executable operation. One
law recovers the trapped reason and complete canonical payload from a `some`
selector equality. The other reuses ADR-0073 to prove that the designated
enclosing trace prefixes the selected journal's internal working trace.

A 58-line properties module plus one umbrella import contains both laws. Each
reports exactly `[propext]` and neither is a simp rule. A 78-line compile-only
test module plus one runner import contains exactly two private examples: iff
elimination and reconstruction of the exact payload, then prefix recovery with
the exact parent-then-nested trace.

The three implementation commits contain 209, 59, and 79 changed lines; this
completion update is the fourth commit. Full validation and independent P0-P3
audits pass. Successful selection remains a value-level fact, and the prefix is
non-strict; neither claims runtime propagation, ancestry, parent execution,
handling, or transaction behavior.

## Completed heterogeneous frame-outcome trap-reason mapping

[ADR-0078](adr/0078-heterogeneous-frame-outcome-trap-reason-mapping.md)
adds exactly one `FrameOutcome.mapTrapReason` operation. The caller owns
the pure function; return and revert retain their exact bytes, and only a
trapped reason is mapped to the target reason type.

A 22-line definition module plus one umbrella import contains the operation. A
51-line properties module plus one umbrella import publishes exactly five simp
laws covering all constructors, identity, and composition. The operation, its
three generated equations, and all five laws are axiom-free. A 64-line
definition-only test module plus two runner lines contains exactly three
assertions with different source and target reason types.

The four implementation commits contain 227, 27, 52, and 66 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. No `Functor`, taxonomy, payload mapper, runtime propagation,
ancestry, handling, or transaction policy is added.

## Completed heterogeneous frame-run-result trap-reason mapping

[ADR-0079](adr/0079-heterogeneous-frame-run-result-trap-reason-mapping.md)
adds exactly one pure `FrameRunResult.mapTrapReason` operation. It preserves the
exact working state and maps only the contained outcome with ADR-0078 and a
caller-owned function.

A 20-line definition module and a 57-line properties module each add one
umbrella import. Exactly five simp laws cover construction, both projections,
identity, and composition. The operation, its generated equation, and all five
laws report exactly `[propext]`. An 83-line definition-only test module plus two
runner lines contains exactly three assertions with distinct working states.

The four implementation commits contain 235, 21, 58, and 85 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. No resolver, payload, journal, trace, propagation, taxonomy,
or transaction policy is included.

## Completed heterogeneous frame-resolution-result trap-reason mapping

[ADR-0080](adr/0080-heterogeneous-frame-resolution-result-trap-reason-mapping.md)
adds exactly one pure `FrameResolutionResult.mapTrapReason` operation. Return
and revert keep exact selected state, effects, and bytes; trap alone changes
its reason through the caller's function.

A 24-line definition module and a 68-line properties module each add one
umbrella import. Exactly five simp laws cover all constructors, identity, and
composition. The operation, its three generated equations, and all five laws
report exactly `[propext]`. A 92-line definition-only test module plus two
runner lines contains exactly three assertions.

The four implementation commits contain 249, 25, 69, and 94 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. Resolution, continuation contexts, payloads, propagation,
and transaction policy remain outside this slice.

## Completed heterogeneous frame-continuation-context trap-reason mapping

[ADR-0081](adr/0081-heterogeneous-frame-continuation-context-trap-reason-mapping.md)
adds exactly one pure `FrameContinuationContext.mapTrapReason` operation. State
and effect checkpoints, working effects, and the result's working state remain
exact; only its outcome reason can change through ADR-0079.

A 27-line definition module and an 87-line properties module each add one
umbrella import. Exactly seven simp laws cover construction, four projections,
identity, and composition. The operation, its generated equation, and all
seven laws report exactly `[propext]`. A 118-line definition-only test module
plus two runner lines contains exactly three assertions.

The four implementation commits contain 250, 32, 88, and 120 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. Continuation, resolution, parent indexing, payloads,
propagation, and transaction policy remain outside this slice.

## Completed frame trap-reason mapping resolution naturality

[ADR-0082](adr/0082-frame-trap-reason-mapping-resolution-naturality.md) adds
exactly one simp theorem proving that context reason mapping commutes with
total resolution. It introduces no executable operation or branch-specific
law, and the theorem reports exactly `[propext]`.

The 26-line properties module adds one umbrella import. A 34-line compile-only
test module plus one runner import contains exactly two private examples for
heterogeneous naturality and ordered two-map composition, with no runtime
assertion or call.

The three implementation commits contain 175, 27, and 35 changed lines; this
completion update is the fourth commit. Full validation and independent P0-P3
audits pass. Continuation execution, parent indexing, payloads, propagation,
and transaction policy remain outside this proof-only slice.

## Completed frame trap-reason mapping continuation-result invariance

[ADR-0083](adr/0083-frame-trap-reason-mapping-continuation-invariance.md)
adds exactly one simp theorem proving that the `Option Next` value produced by
`FrameContinuationContext.continue?` is unchanged by context reason mapping.
It introduces no executable operation or branch-specific law, and the theorem
reports exactly `[propext]`.

The 30-line properties module adds one umbrella import. A 38-line compile-only
test module plus one runner import contains exactly two private examples for
one and two heterogeneous context mappings, with no runtime assertion or call.

The three implementation commits contain 187, 31, and 39 changed lines; this
completion update is the fourth commit. Full validation and independent P0-P3
audits pass. Mapper evaluation, execution cost, step count, exactly-once
invocation, parent indexing, payloads, propagation, and transaction policy
remain outside this proof-only slice.

## Completed heterogeneous trace-prefixed context trap-reason mapping

[ADR-0084](adr/0084-heterogeneous-trace-prefixed-frame-continuation-context-trap-reason-mapping.md)
adds one pure lift of ADR-0081 to the ADR-0071 proof-carrying context. The base
context is mapped while the exact trace-prefix evidence is reused without a
cast or helper.

The 27-line definition and 61-line properties modules each add one umbrella
import. The operation, generated equation, and exactly four simp laws report
exactly `[propext]`. A 95-line definition-only test module plus one runner
import contains exactly three private compile examples and no runtime call.

The four implementation commits contain 246, 28, 62, and 96 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. Parent indexing, checkpoint equality, payloads, provenance,
propagation, and transaction policy remain outside this slice.

## Completed heterogeneous parent-indexed context trap-reason mapping

[ADR-0085](adr/0085-heterogeneous-parent-indexed-frame-continuation-context-trap-reason-mapping.md)
adds one pure lift of ADR-0084 to the ADR-0073 parent-indexed context. The
trace-prefix context is mapped while the exact parent index and checkpoint
equality are reused without a cast or helper.

The 29-line definition and 67-line properties modules each add one umbrella
import. The operation, generated equation, and exactly four simp laws report
exactly `[propext]`. A 109-line definition-only test module plus one runner
import contains exactly three private compile examples and no runtime call.

The four implementation commits contain 259, 30, 68, and 110 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. Rollback selection, payloads, provenance, propagation,
nested execution, and transaction policy remain outside this final mapper
slice.

## Completed nominal frame checkpoint snapshot

[ADR-0086](adr/0086-nominal-frame-checkpoint-snapshot.md) adds one
`FrameCheckpointSnapshot` carrier and one `fromWorkingPair` adapter. The
adapter retains the exact caller-supplied state and effect journal as a single
nominal value.

The 29-line definition and 25-line properties modules each add one umbrella
import. The carrier, constructor, projections, operation, generated equation,
and exactly two simp laws report exactly `[propext]`. A 47-line definition-only
test module plus one runner import contains exactly three private compile
examples and no runtime call.

The four implementation commits contain 237, 30, 26, and 48 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. Checkpoint creation time, ownership, lifetime, entry
provenance, working initialization, scheduling, and transaction atomicity
remain undecided.

## Completed frame checkpointed working pair

[ADR-0087](adr/0087-frame-checkpointed-working-pair.md) adds one
`FrameCheckpointedWorkingPair` carrier with a checkpoint snapshot and an
independent synchronized working pair. The generated constructor and
projections are its complete API; no custom operation or law is added.

The 17-line definition module adds one umbrella import. The carrier, generated
constructor, and two projections report exactly `[propext]`. A 53-line
definition-only test module plus one runner import contains exactly three
private compile examples and no runtime call.

The three implementation commits contain 186, 18, and 54 changed lines; this
completion update is the fourth commit. Full validation and independent P0-P3
audits pass. Equality, derivation, initialization, execution, ownership,
scheduling, and transaction policy remain undecided.

## Completed continuation-context construction from checkpointed working values

[ADR-0088](adr/0088-continuation-context-from-checkpointed-working-pair.md)
adds one `FrameContinuationContext.fromCheckpointedWorkingPair` adapter.
It maps checkpoint state/effects, working effects, and working state plus an
opaque supplied outcome into the existing four context fields.

The 25-line definition and 47-line properties modules each add one umbrella
import. The operation, generated equation, and exactly four simp laws report
exactly `[propext]`. A 68-line definition-only test module plus one runner
import contains exactly three private compile examples and no runtime call.

The four implementation commits contain 225, 26, 48, and 69 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. Resolution, continuation, outcome provenance, execution,
initialization, scheduling, and transaction policy remain outside this slice.

## Completed bytes-aware frame resolution continuation

[ADR-0089](adr/0089-bytes-aware-frame-resolution-continuation.md) adds one
`FrameResolutionResult.continue?` operation. Separate return and revert
callbacks receive the exact selected state/effect pair and bytes; trap yields
`none` without selecting either callback.

The 28-line definition and 54-line properties modules each add one umbrella
import. The operation, its three generated match equations, and exactly three
definitional simp laws report exactly `[propext]`. An 83-line definition-only
test module plus one runner import and call contains exactly three runtime
assertions.

The four implementation commits contain 244, 29, 55, and 85 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. The operation performs no delivery, parent mutation,
scheduling, trap handling, resolution, or transaction transition.

## Completed frame continuation branch/byte erasure coherence

[ADR-0090](adr/0090-frame-continuation-branch-byte-erasure-coherence.md)
adds one proof-only non-simp law. It equates the explicit
`context.resolve.continue?` route with the established context `continue?`
only when both branch callbacks are the same and ignore bytes.

The 29-line properties module adds one umbrella import and reports exactly
`[propext]`. A 45-line test module plus one runner import contains exactly two
private compile regressions and no runtime call.

The three implementation commits contain 199, 30, and 46 changed lines; this
completion update is the fourth commit. Full validation and independent P0-P3
audits pass. The slice adds no carrier, operation, delivery, callback-count
claim, trap handling, or transaction transition.

## Completed frame-resolution continuation trap-reason mapping invariance

[ADR-0091](adr/0091-frame-resolution-continuation-trap-reason-mapping-invariance.md)
adds one proof-only simp law. It equates bytes-aware continuation after
heterogeneous result reason mapping with continuation of the original result,
using the same arbitrary return and revert callbacks.

The 27-line properties module adds one umbrella import and reports exactly
`[propext]`. A 42-line test module plus one runner import contains exactly two
private compile regressions and no runtime call.

The three implementation commits contain 187, 28, and 43 changed lines; this
completion update is the fourth commit. Full validation and independent P0-P3
audits pass. The slice adds no carrier, operation, callback-count claim, trap
handling, or transaction transition. ADR-0090 remains non-simp.

## Completed checkpointed working-pair storage write

[ADR-0092](adr/0092-checkpointed-working-pair-storage-write.md) adds one
working-only `FrameCheckpointedWorkingPair.writeWorkingStorage?` operation.
It reuses the existing strict WorldState write, preserves the exact checkpoint
and working journal, and returns `none` for an absent working account.

The 20-line definition and 33-line properties modules each add one umbrella
import. The operation, generated equation, and exactly two simp laws report
exactly `[propext]`. A 98-line definition-only test module plus one runner
import and call contains exactly three runtime assertions.

The four implementation commits contain 230, 21, 34, and 100 changed lines;
this completion update is the fifth commit. Full validation and independent
P0-P3 audits pass. The address is caller-selected; the slice adds no
authorization, account creation, checkpoint lifecycle, outcome, parent
mutation, scheduling, trap, gas, or transaction policy.

## Completed checkpointed working-pair storage address

[ADR-0093](adr/0093-checkpointed-working-pair-storage-address.md) adds one
`FrameCheckpointedWorkingPairWithStorageAddress` carrier and one
`writeStorage?` operation. One caller-designated storage address is retained
beside the existing checkpointed working values and supplies each delegated
ADR-0092 write without another address argument.

The 34-line definition and 44-line properties modules each add one umbrella
import. Exactly two simp laws report `[propext]`. A 94-line definition-only
test module plus one runner import and call contains exactly three runtime
assertions. All staged commits remain below 300 changed lines; full validation
and independent P0-P3 audits pass.

The carrier establishes no current-contract identity, address authority,
account creation, contract entry, outcome, parent mutation, scheduling, trap,
gas, ABI, or transaction policy.

## Completed conditional WorldState storage read

[ADR-0094](adr/0094-world-state-storage-read.md) adds one
`WorldState.readStorage?` operation. It returns `none` only for an absent
Account; a present Account with a missing slot returns `some zero`.

The 17-line definition and 28-line properties modules each add one umbrella
import. The operation, generated equation, and exactly two simp laws report
`[propext]`. A 56-line definition-only test module plus one runner import and
call contains exactly three runtime assertions. Full validation and independent
P0-P3 audits pass.

No frame lift, mutation, authorization, gas, ABI, or transaction policy is
included.

## Completed address-bound working storage read

[ADR-0095](adr/0095-address-bound-working-storage-read.md) adds one
carrier-level `readStorage?` operation. It accepts only a slot, selects
the retained storage address, and delegates the working WorldState read to
ADR-0094 without consulting the checkpoint.

The 20-line definition and 37-line properties modules each add one umbrella
import. The operation, generated equation, and exactly two simp laws report
`[propext]`. An 84-line definition-only test module plus one runner import and
call contains exactly three runtime assertions. Full validation and independent
P0-P3 audits pass.

No address authority, mutation, frame entry, gas, ABI, or transaction policy
is included.

## Completed WorldState storage read/write coherence

[ADR-0096](adr/0096-world-state-storage-read-write-coherence.md) adds exactly
three simp laws for same-slot observation, different-slot
preservation, and different-address preservation after conditional writes.

All three laws retain the outer write result with `Option.map`, distinguishing
write failure from a successful write followed by an absent read target.
The 99-line properties module adds no executable API, carrier, or helper. A
41-line compile-only module contains exactly three private examples; the runner
imports it once and makes no call. All three laws report exactly `[propext]`,
and full validation plus independent P0-P3 audits pass.

## Completed address-bound working storage read/write coherence

[ADR-0097](adr/0097-address-bound-working-storage-read-write-coherence.md)
adds exactly two carrier-level simp laws. They expose the newly written
value at the retained address and preserve a different-slot read while keeping
working-Account absence as outer `none`.

The 39-line properties module adds no executable API, carrier, or helper. A
35-line compile-only module contains exactly two private examples; the runner
imports it once and makes no call. Both laws report exactly `[propext]`, and
full validation plus independent P0-P3 audits pass.

The following contract-entry boundary review selected ADR-0098's payload-free
initialization layer. Address roles, invocation inputs, and outcome provenance
remain separate decisions before an entry carrier is introduced.

## Completed parent-indexed frame initialization

[ADR-0098](adr/0098-parent-indexed-frame-initialization.md) adds a
two-field carrier for caller-supplied initial WorldState and rollback values,
indexed by one designated parent working pair.

Exactly two operations derive an indexed trace extension starting at the
parent trace and an existing checkpointed working-pair value. The 48-line
definition, 36-line properties, and 48-line compile-only test modules contain
exactly two simp laws and three private examples. All declarations meet the
`[propext]` boundary, full validation and independent audits pass, and no
address, payload, entry event, scheduler action, or execution claim is added.

## Completed initialization storage-address adapter

[ADR-0099](adr/0099-parent-indexed-frame-initialization-storage-address.md)
adds one pure adapter. It combines an ADR-0098 initialization value and a
caller-supplied storage selector into the existing ADR-0093 carrier.

The 24-line definition, 34-line properties, and 50-line compile-only test
modules contain exactly one operation, two simp projection laws, and three
private examples. The adapter reaches the existing storage-write consumer
without adding a carrier, storage operation, address authority, runtime
assertion, helper, or runner call. All declarations meet the `[propext]`
boundary, and the full validation and independent P0-P3 audits pass.

## Completed checkpointed working-pair storage-write algebra

[ADR-0100](adr/0100-checkpointed-working-pair-storage-write-algebra.md)
adds three proof-only laws for the existing address-parameterized working
write: final-write overwrite, distinct-slot commutation, and distinct-address
commutation.

The 77-line properties module has one private normalization helper and exactly
the three public laws. A 52-line compile-only module has exactly three private
examples. All three laws remain non-simp; a follow-up critical-pair audit
removed overwrite from simp because the present-Account branch can rewrite its
first write before the surrounding bind. All public laws report
`[propext, Quot.sound]`, full validation and
independent audits pass, and no operation, address authority, runtime
reordering claim, runtime assertion, or runner call is added.

## Completed address-bound working storage-write algebra

[ADR-0101](adr/0101-address-bound-working-storage-write-algebra.md) adds
two proof-only laws for the retained-address writer: final-write overwrite and
distinct-slot commutation.

The 58-line properties module has one private normalization helper and exactly
the two public laws. A 38-line compile-only module has exactly two private
examples. Both laws remain named non-simp rules to avoid overlap with
present-Account branch reduction and report `[propext, Quot.sound]`. Full
validation and independent audits pass. The thin lift adds no operation,
address argument, authority claim, runtime reordering claim, assertion, or
runner call.

## Completed address-bound working storage-write preservation

[ADR-0102](adr/0102-address-bound-working-storage-write-preservation.md)
adds three proof-only observations of the retained address, checkpoint,
and working effect journal after a conditional write.

Each observation keeps Account absence as `none` and exposes the exact original
field on success. The 53-line properties module contains exactly three public
simp laws, and the 48-line compile-only module contains exactly three private
regressions. All laws report `[propext]`; full validation and independent
audits pass. The slice adds no operation, carrier, whole-state preservation
claim, runtime assertion, or runner call.

## Completed address-bound working storage-write values coherence

[ADR-0103](adr/0103-address-bound-working-storage-write-values-coherence.md)
adds one proof-only relation between the retained-address writer and its
underlying address-parameterized values writer.

Projecting a successful wrapper result recovers the exact underlying values,
while write failure remains `none`. The 24-line properties module contains the
single public simp law, and the 38-line compile-only module contains exactly two
private regressions. The law reports `[propext]`; full validation and
independent audits pass. The slice adds no operation, carrier, address policy,
runtime assertion, or runner call.

## Completed parent-indexed initialization continuation-context coherence

[ADR-0104](adr/0104-parent-indexed-initialization-continuation-context-coherence.md)
adds one proof-only equality between the two existing continuation-context
construction routes out of parent-indexed initialization.

The equality forgets only prefix and parent-index evidence from the refined
route and keeps every base-context field exact. The 29-line properties module
contains one named non-simp law, and the 52-line compile-only module contains
two private regressions. The law reports `[propext]`; full validation and
independent audits pass. It adds no operation, frame transition, outcome
provenance, runtime assertion, or runner call.

## Completed present working storage Account refinement

[ADR-0105](adr/0105-present-working-storage-account-refinement.md) adds one
carrier and one partial producer for the Account selected by an address-bound
context's working WorldState.

Failure remains `none`; success retains the exact context, Account, and lookup
evidence. Two simp branch laws report `[propext]`. Three runtime assertions and
three private compile regressions cover absence, exact success, retained state,
and direct reuse by the existing read and write laws. Full validation and
independent P0-P3 audits pass. The slice creates no Account, assigns no address
authority, and adds no total storage operation, transition, or published surface.

## Completed present working storage Account total read

[ADR-0106](adr/0106-present-working-storage-account-total-read.md) adds
one total slot read from the Account stored by ADR-0105 and one coherence law
with the existing conditional context read.

The operation performs no WorldState lookup and cannot fail after refinement.
Three runtime assertions cover zero-default and exact two-address/two-slot
reads; two private compile regressions exercise direct and `Option.getD`
consumers. The operation, generated equation, and law report `[propext]`; full
validation and independent P0-P3 audits pass. It adds no write, Account
creation, address authority, transition, or published surface.

## Completed present working storage Account total write

[ADR-0107](adr/0107-present-working-storage-account-total-write.md) adds
one total write that updates the selected working Account in both the retained
carrier and its context, together with fresh presence evidence.

The operation performs no lookup and cannot fail after refinement. Three
runtime assertions cover nonzero synchronization, zero deletion, and
sequential overwrite; three private compile regressions cover context
coherence, arbitrary observation, and canonical re-refinement. The operation,
generated equation, and law report `[propext]`; full validation and independent
P0-P3 audits pass. It adds no Account creation, address authority, frame
transition, or published surface.

## Completed present working storage Account total read/write coherence

[ADR-0108](adr/0108-present-working-storage-account-total-read-write-coherence.md)
adds same-slot read-after-write and distinct-slot read preservation for
the ADR-0106/0107 total operations.

The two simp laws delegate to existing Account laws and report `[propext]`.
Three private compile regressions cover both laws directly and their named
composition with ADR-0106 conditional-read coherence. Full validation and
independent P0-P3 audits pass. The slice adds no lookup, mutation, runtime
assertion, address authority, transition, or published surface.

## Completed present working storage Account total-write algebra

[ADR-0109](adr/0109-present-working-storage-account-total-write-algebra.md)
adds same-slot overwrite and distinct-slot commutation for sequential ADR-0107
total writes.

The overwrite law is the sole new simp rule; commutation remains explicitly
directed by its caller. Both laws report `[propext, Quot.sound]`. Two private
compile regressions name the laws directly, and full validation plus independent
P0-P3 audit pass. The proof-only slice adds no operation, runtime assertion,
address authority, transition, or published surface.

## Completed present working storage Account total-write isolation

[ADR-0110](adr/0110-present-working-storage-account-total-write-isolation.md)
adds a law proving that a total write preserves the complete optional Account
lookup at every working address different from the selected storage address.

The simp law reports `[propext]`. Two private compile regressions apply it
directly and across two sequential writes; full validation and independent
P0-P3 audit pass. The proof-only slice adds no operation, runtime assertion,
address role, transition, or published surface.

## Completed present working storage Account total-write projections

[ADR-0111](adr/0111-present-working-storage-account-total-write-projections.md)
adds exact projections for the retained selector, checkpoint, working
journal, and updated stored Account.

All four simp laws report `[propext]`. Five private compile regressions name
the projections directly and verify nested ADR-0110 composition; full
validation and independent P0-P3 audit pass. The proof-only slice adds no
operation, runtime assertion, address role, transition, or published surface.

## Completed present working storage Account total-write presence

[ADR-0112](adr/0112-present-working-storage-account-total-write-presence.md)
adds deletion of the selected sparse-storage entry after a zero write and
`some value` presence after a nonzero write.

Both named non-simp laws report `[propext]`. Two private compile regressions
apply them directly; full validation and independent P0-P3 audit pass. The
proof-only slice adds no operation, runtime assertion, address role, transition,
or published surface.

## Completed present working storage Account total-write sparse preservation

[ADR-0113](adr/0113-present-working-storage-account-total-write-sparse-preservation.md)
adds one Account law and one proven-present carrier lift showing that a write
preserves the optional sparse entry at every distinct slot.

Both named non-simp laws report exactly `[propext]`. Two direct compile
regressions cover the two abstraction boundaries; full validation and
independent P0-P3 audits pass. No operation or runtime fixture was added because
existing execution tests already exercise the underlying distinct-slot
behavior.

## Completed present working storage Account optional/total re-refinement coherence

[ADR-0114](adr/0114-present-working-storage-account-optional-total-re-refinement-coherence.md)
exposes one complete-carrier equality between the failure-aware optional writer
followed by Account refinement and the proven-present total writer.

The named non-simp law reports exactly `[propext]` and supports repeated
optional-write/refinement stages. Two compile-only regressions cover direct use
and two-stage composition; full validation and independent P0-P3 audits pass.
No new executable behavior or runtime fixture was added.

## Completed parent-indexed initialization present storage Account refinement

[ADR-0115](adr/0115-parent-indexed-initialization-present-storage-account-refinement.md)
composes the existing initialization storage-address adapter with working
Account presence refinement.

Explicit absent and present branch laws preserve the `initialWorld` lookup
result. A compile-only consumer connects the successful branch to the existing
total write/read interface. Full validation and independent P0-P3 audits pass.
The adapter adds no Account creation, entry identity, authority, lifetime
claim, or runtime fixture.

## Completed address-selected checked Core code

[ADR-0116](adr/0116-address-selected-checked-core-code.md) admits exactly the
closed Core programs accepted by the existing checker, associates optional code
with Account state, selects it through WorldState by Address, and returns the
complete stateful Core-machine result.

Four checked-code laws, four Account laws, and seven WorldState laws cover
admission, typed eventual completion, no-fault safety, storage/code preservation,
all lookup branches, and exact execution. Runtime regressions retain a returned
cell reference together with its local store, distinguish absent and no-code
Accounts, select different programs at two addresses, preserve code through a
storage write, and leave fuel exhaustion unclassified. Full validation and two
independent P0-P3 audits pass. No FrameOutcome, ABI, contract input, WorldState
effect, or published interface was added.

## Completed typed Core storage-read suspension

[ADR-0117](adr/0117-typed-core-storage-read-suspension.md) provides a
syntax-independent storage-read request. Existing Core function application
receives one runtime-only capability through a fixed typed context. Execution
can return a first-order suspension that retains the exact CEK continuation and
Core-local store, then resume with a typed Word response.

The closed checker and its sufficient-fuel completion theorem remain unchanged.
Every finite host-checked run instead has a typed done, out-of-fuel, or
suspended result, and machine faults are excluded. A Semantics handler reads
the request through the proven-present working Account and resumes the typed
state without changing the Account context or Core-local store.

Core requests contain words only; WorldState, addresses, checkpoints, rollback,
and commit policy stay in Semantics. Address-selected host-code migration, the
fuel-preserving handler loop, and storage write remain later work. Full
validation and two independent audits pass.

## Meaning of completion

A Core feature is complete only when its declarative rules, total executable
checker and evaluator, correspondence proofs, safety coverage, negative and
boundary tests, and version-isolation behavior agree. Publication is a later,
separate decision.
