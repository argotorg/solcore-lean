# ADR-0141: Checked Word completion to canonical return bytes

- Status: Accepted
- Decision date: 2026-08-30
- Scope: connect typed handled Word completion to one canonical returned frame
- Implementation: Complete

## Context

Handled Core execution already retains a branch-complete `HostDriverResult`.
It distinguishes completion, exhaustion, raw machine fault, and unsupported
policy and preserves
the exact terminal host context, Core value, Core-local Store, and exhausted
state. The checked host runner proves that its completed value has the
program's declared result type and that a raw fault is unreachable.

Frame continuation construction is also complete, but its generic adapter
requires the caller to interpret every possible Core value and Store as a
`FrameOutcome`. No internal policy currently connects an actual typed Core
completion to return bytes.

The canonical runtime scalar layer already encodes a Word as exactly 32
most-significant-byte-first octets and proves strict decoding. A Word-result
program is therefore the smallest completion shape that can be connected to a
frame without defining serialization for arbitrary Core values or Store.

## Decision

Add a checked Word-result refinement:

```lean
structure CheckedHostCoreWordProgram where
  code : CheckedHostCoreProgram
  resultType_eq_word : code.program.resultType = .word
```

Provide an optional constructor from `CheckedHostCoreProgram`. It succeeds
exactly when the declared result type is Word. The refinement adds no new Core
checker, expression, type, program representation, or execution engine.

Add a success-only completion carrier:

```lean
structure WordReturnedFrameCompletion
    (RollbackState : Type u) (TraceState : Type v) where
  context : HostStorageDriver.Context RollbackState TraceState
  word : Core.Word
  store : Core.Store
```

The carrier retains the exact terminal mutable context, Word, and complete
Core-local Store. It is not a replacement for `HostDriverResult` and does not
represent exhaustion, fault, or unsupported completion.

## Raw projection and retraction

Add a pure projection on storage-backed handled results:

```text
done (word value) store -> some { context, value, store }
done otherValue store  -> none
outOfFuel state        -> none
fault error state      -> none
unsupported suspension remainingFuel -> none
```

The projection is intentionally syntactic and may be applied to an arbitrary
raw result. It assigns no trap, revert, empty bytes, default Word, or other
meaning to a non-Word completion.

Add a retraction from a successful completion to the exact raw result:

```lean
completion.toHostDriverResult =
  ⟨completion.context, .done (.word completion.word) completion.store⟩
```

Prove that projecting this raw result returns exactly `some completion`, and
that projection equals `some completion` iff the source raw result equals this
retraction. The existing `HostDriverResult` remains the only branch-complete
execution carrier and continues to retain every exhausted state and fault.

Do not add another four-way classifier duplicating it.

## Canonical frame conversion

Convert every successful completion totally to the existing continuation:

```lean
FrameContinuationContext.fromCheckpointedWorkingPair
  completion.context.context.values
  (.returned (encodeWordBytesBE completion.word))
```

The conversion is polymorphic in `TrapReason`; its outcome is returned and
therefore constructs no trap reason. It must work with `Empty` as the trap
reason type.

The terminal context supplies the checkpoint state and effects and the final
working WorldState and effects exactly. Return data is exactly the existing
32-byte big-endian Word encoding. The carrier continues to expose the complete
Core Store, but the conversion does not serialize or otherwise consume it.

## Checked Word execution

Delegate `CheckedHostCoreWordProgram.runWithStorage` to the wrapped checked
program's existing storage-backed handled run. Add a completion projection for
that exact raw result.

For every checked Word program, context, immutable execution input, and fuel,
prove:

- the raw outcome has type Word;
- a completed raw value has the unique shape `.word word`;
- a raw fault is impossible;
- completion projection equals `some completion` iff the raw run is exactly
  `completion.toHostDriverResult`;
- completion projection equals `none` iff the raw run is exactly exhausted at
  some retained context and Core state or stopped at an unsupported-policy
  suspension; and
- once projection succeeds, it returns the same exact completion for every
  larger fuel budget.

The `none` equivalence is a theorem only for the checked Word specialization.
For the lower-level projection, `none` also covers non-Word completion and raw
fault. This distinction must be visible in names and documentation.

Resumption continues to use the raw result and the existing exact
`HostDriverResult.resumeWithFuel`/storage-driver split law. The successful
projection does not carry an exhausted state and gains no resumption method.
Publish the wrapper's exact same-input split law rather than introducing a
second session abstraction.

## Exact proof interface

Expose laws for:

- all checked Word wrapper projections and optional-constructor branches;
- all completion carrier projections;
- exact raw projection for Word completion, non-Word completion, exhaustion,
  fault, and unsupported policy;
- projection/retraction equality and exact `some` inversion;
- exact continuation checkpoint state, checkpoint effects, working effects,
  working WorldState, and returned outcome;
- return-data size 32 and strict decode back to the exact Word;
- exact returned `FrameResolutionResult` selecting the terminal working state,
  effects, and bytes;
- checked Word raw typing, completed Word shape, and no-fault;
- checked Word `some`/raw-completion and
  `none`/raw-exhaustion-or-unsupported equivalences;
- larger-fuel completion stability; and
- wrapper same-input split-fuel coherence through the existing driver law.

Proofs must reuse checked host-run safety, `word_shape`, handled-driver fuel
laws, canonical Word byte laws, and existing frame-continuation construction
and resolution. They must not replay the Core machine or define a new codec.

## Required regressions

Compile-time consumers must apply every public projection, raw adapter,
retraction, frame conversion, checked typing/shape/no-fault, exact branch,
stability, and fuel-split theorem.

Executable regressions must:

- use the ADR-0138 checked Word program and exact storage-backed context;
- observe no completion at measured fuel 15 and the exact retained exhausted
  raw context and state;
- observe canonical completion at fuel 16 and stability with larger fuel;
- retain the write exactly once in the final working storage while preserving
  the checkpoint and effect journals;
- retain the exact Word and complete Core Store;
- produce exactly 32 returned bytes that strictly decode to the Word;
- resolve to the exact final working WorldState, working effects, and bytes;
- cover zero, a nontrivial Word, and the maximum Word at the frame bridge;
- show that an arbitrary completed Unit raw result projects to `none` and is
  not converted to return, revert, or trap; and
- reject a checked non-Word program at the Word-refinement constructor.

A focused cell-bearing Word program must additionally complete with a nonempty
Core Store, proving that the success carrier retains it while canonical return
bytes depend only on the Word.

Measured fuel values are regression observations, not semantic constants.

## Dependency and publication boundary

The wrapper, success carrier, projection, and frame bridge live in Semantics.
They may depend on checked host execution, storage-backed driver safety and fuel
laws, runtime Word bytes, and existing frame continuation construction and
resolution. Core does not import frame or WorldState semantics.

The parent-indexed selected path is unchanged. `Account.code?` currently
returns `CheckedHostCoreProgram` without retaining a Word-result refinement,
so this ADR does not claim automatic Word-return conversion after WorldState
code selection. A later slice must specify an exact selected-code refinement or
an explicit non-Word branch before connecting that boundary.

Acceptance requires focused and full builds, the executable suite, trust-zero
and warning-as-error checks for every changed Lean root, semantic-kernel checks,
diff hygiene, and independent contract audits.

No Wire tag, schema, profile, source form, grammar, parser
rule, or source elaboration is added. Frozen public
formats continue to reject internal values and programs as before. The parser
proof program remains paused. The root README does not change.

## Non-goals

This ADR does not define or prove:

- Solidity ABI encoding, a source-level return statement, dynamic return data,
  tuples, arrays, strings, named data, or arbitrary Core-value serialization;
- conversion, erasure, serialization, or frame meaning for Core-local Store;
- implicit revert, trap, default bytes, or recovery for non-Word completion,
  exhaustion, raw fault, or unsupported policy;
- parent Core resumption, child-result delivery, invocation, call kind, call
  stack, scheduling, recursion, or reentrancy;
- code selection refinement, Account mutation, balance transfer, gas charging,
  transaction commit, rollback application, or persistence;
- a public byte contract, external compatibility promise, or concrete syntax.

## Implemented sequence

1. recorded and activated this internal completion contract;
2. added the checked Word refinement and success-only completion carrier;
3. added exact raw projection/retraction and canonical frame conversion;
4. proved checked Word branch, safety, stability, and split-fuel laws;
5. added compile-time and measured executable regressions; and
6. completed full validation, independent audits, and documentation sync.

## Implementation record

Seven focused Semantics modules implement the wrapper, execution adapter,
success carrier, raw projection and retraction, frame conversion, and their
proof interfaces. Thirty-five public theorems have thirty-five compile-only
consumers. Their reported axioms are subsets of `propext` and `Quot.sound`.

Executable regressions retain exact exhaustion before the write at fuel 9,
after it at fuel 10, and at the input-size request at fuel 15. Fuel 16
completes; exact 9+7 and 10+6 split laws and larger fuel preserve completion.
The returned frame contains the exact terminal state and effects and canonical
bytes. Synthetic bridge tests cover Word zero, `0x1234`, and the maximum Word.
A cell-bearing program retains a nonempty Core Store while the frame conversion
remains Store-independent.

The 695-job full build, 1,278-job test executable build, and full test run pass.
All 12 changed Lean roots pass trust-zero with warnings as errors.
Semantic-kernel and diff checks pass. No public format or root README changed.

## Consequences

One actual typed Core completion now has a concrete frame meaning: a Word may
be returned as its already-canonical 32-byte big-endian representation while
the terminal WorldState, effects, and Core Store remain explicit. Unsupported
values and unfinished or faulty execution receive no invented outcome.

This creates a narrow Core-to-frame bridge without calling it an ABI or
changing code selection. The next integration step can refine selected code by
result type before choosing whether and how this bridge applies there.
