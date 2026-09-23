# ADR-0135: Strict optional input-word big-endian observation

- Status: Accepted
- Decision date: 2026-08-29
- Scope: observe one exact 32-byte big-endian word from bounded immutable input
- Implementation: Complete

## Context

ADR-0133 gives one handled run a bounded immutable `InputData` value and an
optional single-byte observation. ADR-0134 derives its exact Word-sized length
and proves that byte lookup succeeds exactly below that boundary. The same
input already remains fixed through request handling, recursive driving,
selected execution, and parent-indexed continuation construction.

The repository also has one canonical internal Word byte representation:
`encodeWordBytesBE` emits exactly 32 most-significant-byte-first octets and
`decodeWordBytesBE?` accepts exactly that representation. Its round trips and
per-byte agreement with Core's existing `Word.byteAt` operation are proved.
Reusing this representation is the smallest wider input observation that does
not require a new scalar format, mutable memory, source syntax, or frame
lifecycle.

This decision is deliberately stricter than a zero-filling calldata load. An
incomplete window is absent rather than padded. The operation is an internal
observation of raw input bytes; it is not an ABI or calldata rule.

## Decision

Add one derived optional observation to the existing carrier:

```lean
namespace Solcore.Semantics.HostStorageDriver.InputData

def wordBE? (input : InputData) (offset : Core.Word) : Option Core.Word :=
  if offset.val + 32 ≤ input.bytes.size then
    decodeWordBytesBE?
      (input.bytes.extract offset.val (offset.val + 32))
  else
    none

end Solcore.Semantics.HostStorageDriver.InputData
```

The comparison and both extraction bounds use `Nat`. Addition does not occur
in `Core.Word`, so `offset.val + 32` cannot wrap modulo `wordModulus`.
`ByteArray.extract` is used only after proving that the complete half-open
window `[offset.val, offset.val + 32)` lies within `input.bytes`.

Do not add a cached word, cursor, second byte sequence, unchecked constructor,
default input, fallback value, or compatibility entry point. The existing
`ExecutionInputs.inputData` field remains the only source of the result.

## Exact window and codec contract

The operation succeeds exactly when the complete 32-byte window exists:

```lean
(∃ word, input.wordBE? offset = some word) ↔
  offset.val + 32 ≤ input.sizeWord.val

input.wordBE? offset = none ↔
  input.sizeWord.val < offset.val + 32
```

For every successful result, characterize the bytes in both directions:

```lean
input.wordBE? offset = some word ↔
  offset.val + 32 ≤ input.sizeWord.val ∧
  input.bytes.extract offset.val (offset.val + 32) =
    encodeWordBytesBE word
```

Thus decoding uses the existing exact big-endian codec, and encoding the
result recovers the selected window byte-for-byte. No separate endianness
definition or duplicate word assembler is permitted.

For every `index : Fin 32`, successful loading must also agree with the
existing byte observations at the exact natural position `offset.val +
index.val`. Full-window evidence proves that this position is below
`input.sizeWord.val` and therefore below `Core.wordModulus`; conversion back to
a Core Word is lossless and is not justified by modular wraparound. The
observed byte must equal the corresponding big-endian `word.byteAt` result.

A window containing 32 zero octets returns `some Core.Word.zero`. `none` means
only that the complete window is unavailable; it never represents a decoded
zero word. Empty input, every input shorter than 32 bytes, and every final
partial window are absent.

## Core host capability

Append one internal capability after the eight existing entries:

```lean
inductive HostFunction where
  | storageRead
  | storageWrite
  | storageAddress
  | codeAddress
  | callValue
  | callerAddress
  | inputDataByte?
  | inputDataSize
  | inputDataWordBE?
```

`HostFunction.inputDataWordBE?` has parameter type Word and result type
`Sum Unit Word`. Its stable index is 8. Existing indexes 0 through 7 do not
move. `hostContext` and `hostEnvironment` append matching entries, have length
9, and reject index 9 as the first unbound host-capability index.

Append the matching first-order request:

```lean
inductive HostRequest where
  -- existing requests
  | inputDataWordBE? (offset : Word)
```

`HostRequest.Response (.inputDataWordBE? offset)` is `Option Word`. Core
response injection preserves the distinction exactly:

- `none` becomes the left Unit value;
- `some word` becomes the right Word value, including `word = Word.zero`.

Applying the capability to a Word emits the request with that exact offset.
Applying it to Unit, Bool, Product, Sum, function, cell, named-data, or host
function values produces the existing exact `invalidHostArgument` fault.
Resumption injects the matching sum value while preserving the saved
continuation and Core-local Store.

Core owns only the typed Word-to-`Sum Unit Word` capability, optional response
shape, and first-order request. It must not import bytes, codecs, storage,
frames, ABI, or an origin story for the immutable input.

## Handler, driver, and context identity

The semantics handler interprets the request exactly as follows:

```lean
handleRequest inputs context (.inputDataWordBE? offset) =
  (context, inputs.inputData.wordBE? offset)
```

This request is read-only. It performs no Account, Address, code, checkpoint,
or storage lookup and leaves the complete mutable handler context unchanged.
The same whole immutable `ExecutionInputs` value is reused when the recursive
driver resumes with its exact remaining fuel.

The suspension law preserves the request offset, continuation, and Store and
injects exactly the absent or present response above. Handled-step, fuel,
selected-execution, completion, and parent-indexed adapters retain their
existing option boundaries and continue selecting code solely through
`inputs.codeAddress`.

## Exact proof obligations

Expose focused laws for:

- success iff the full 32-byte window exists and absence iff it does not;
- exact extract bounds, exact extract size on success, and Nat-only offset
  arithmetic without truncation or modular wrap;
- decoder success and encoder equality for every returned Word;
- all 32 per-byte observations agreeing with `encodeWordBytesBE` and
  `Word.byteAt` at exact representable input positions;
- preservation of `some Word.zero` for an all-zero window;
- capability parameter type, result type, append-only index 8, both table
  lookups, table length 9, and first-unbound index 9;
- request response type and exact `Option Word` to Core sum injection;
- request emission for a Word and exact invalid-argument behavior for every
  other Core value shape;
- exact suspension resumption with continuation and Store identity;
- executable/declarative emission and transition correspondence;
- progress, response typing, state typing, preservation, runner
  correspondence, and checked-program no-fault safety;
- exact handler response and complete mutable-context identity;
- recursive driver resumption with unchanged immutable input and exact
  remaining fuel;
- driver completeness, fuel soundness, type safety, and completed
  larger-budget stability; and
- unchanged selected failure, storage absence, exhaustion, completion,
  parent-indexed coherence, and triple-option boundaries.

No theorem may interpret the selected Word as an ABI argument, selector,
source parameter, memory cell, return value, or authenticated input.

## Required regressions

Focused `InputData` tests must cover:

- empty input and lengths 1 and 31 returning `none` at offset zero;
- exactly 32 bytes at offset zero returning the exact known big-endian Word;
- first, middle, and final complete windows in a longer fixture;
- the last complete offset succeeding and the immediately following partial
  window failing;
- the maximum Core Word offset failing without wraparound;
- 32 zero bytes returning `some Word.zero`; and
- encoder equality plus all 32 byte-coherence positions for a nontrivial Word.

Low-level Core tests must cover:

- fixed host indexes 0 through 8, both table lookups, length 9, and first
  unbound index 9;
- host-check acceptance, closed-check rejection, and static rejection of a
  non-Word argument;
- exact request emission, both response branches, continuation, and Store;
- exact raw invalid-argument faults and checked-program no-fault behavior;
- measured request-ready, suspension, handled-completion, and larger-fuel
  boundaries rather than assumed costs; and
- direct rejection of `.hostFunction .inputDataWordBE?` by frozen Wire v1
  and v2.

Direct end-to-end tests must vary only `inputData`, retaining code, storage,
call value, caller Address, and code Address, and observe only the selected
optional Word changing. They must separately cover a present zero window and
an absent window.

A storage end-to-end program must observe one present Word, case-analyze the
sum, write the right-branch Word to working storage, observe the same window
again, and return both Words. The stored Word and both observations must be
equal while all selector, checkpoint, journal, and non-selected Account
observations remain unchanged. Exact fuel boundaries must be measured and
larger-budget completion proved stable.

A parent-indexed end-to-end test must preserve storage-Account absence,
selected-code absence, selected exhaustion, and completion as three nested
optional layers. On completion, ADR-0129's resolution fold must recover both
the exact word-derived storage entry and exact terminal bytes. It must not
claim that the fold applies rollback or resumes a parent.

## Dependency and publication boundary

Semantics owns `InputData.wordBE?`, exact window bounds, use of the existing
big-endian codec, byte coherence, and request interpretation. Core remains
independent of `Bytes` and owns only the typed internal capability. Generic
HostDriver and continuation layers remain parametric.

Frozen Core Wire v1 and v2 continue to reject every host-function value. Add no
Wire tag, runtime schema, profile, ABI
rule, source form, parser rule, or source elaboration. The root README does
not change. Publication requires a separate ADR.

## Non-goals

This ADR does not define or prove:

- calldata, ABI arguments, selectors, dispatch, or source parameter meaning;
- zero padding, partial loads, clamping, alignment, truncation, or a
  load-past-end rule;
- arbitrary-length slicing or copying, mutable memory, return-data or
  revert-data access, hashing, or decoding of structured values;
- little-endian input interpretation or a second Word byte codec;
- nested invocation, child-input derivation or forwarding, call stack, call
  kind, delegate behavior, creation input, callback delivery, or parent
  resumption;
- checkpoint creation or lifetime, rollback application, transaction
  finalization, balance transfer, payability, gas, or fork policy;
- mutable input, cursor state, streaming, aliasing with Core-local cells, or
  WorldState storage; or
- any parser, source syntax, schema, profile, Wire, ABI, public-format, or
  publication change.

## Implementation sequence

Every commit must stay green and contain at most 300 changed lines:

1. add this ADR, then activate it in the five internal status documents in a
   separate small commit;
2. add `InputData.wordBE?`, exact window/codec/byte-coherence laws, and focused
   carrier tests, splitting proofs from tests if the change approaches 300
   lines;
3. append the Core capability and request and close every exhaustive machine,
   progress, typing, preservation, runner, and no-fault case;
4. add exact handler, suspension, recursive-driver, and context-identity laws;
5. update request-exhaustive custom handlers and add focused Core, fuel, and
   frozen-Wire regressions;
6. add direct optional-word observation and input-only variation regressions;
7. add the observe-write-observe storage execution and measured fuel
   regressions;
8. add triple-option parent completion and ADR-0129 fold regressions;
9. register executable tests and run trust, axiom, dependency, build, test,
   metadata, kernel, compatibility, and independent audits; and
10. synchronize completion evidence in internal documents without changing
    the root README.

Temporary migration helpers and transitional APIs must be removed before
completion.

## Implementation record

`InputData.wordBE?` now checks the exact natural-number bound
`offset.val + 32 <= input.bytes.size`, extracts that complete half-open
window, and decodes it with the canonical big-endian Word codec. Offset
arithmetic never wraps, incomplete windows are absent rather than padded, and
a complete all-zero window remains the distinct result `some Word.zero`.
Exact window, codec, and all 32 per-byte coherence laws are proved.

Core appends `inputDataWordBE? : word -> sum unit word` at index 8. Both host
tables have length 9 and index 9 is first unbound. The request carries an exact
Word offset and receives `Option Word`; emission, both response branches,
resumption, raw faults, progress, typing, preservation, runner
correspondence, and checked-program no-fault safety are complete.

The canonical handler returns
`(context, inputs.inputData.wordBE? offset)` and preserves the complete mutable
context, saved continuation, and Core-local Store. Direct execution covers a
present nonzero word, a present zero word, and an absent window. The
observe-write-observe storage program completes at fuel 32, is exhausted at
31, reaches its request-ready boundary at 23, and remains stable at fuel 64.

Parent-indexed execution completes a present window at fuel 30 after its fuel
29 exhaustion boundary. The shorter absent branch completes at fuel 12 after
its fuel 11 exhaustion boundary. Its regressions preserve all three optional
layers, recover the exact result through the ADR-0129 fold, preserve terminal
bytes, and confirm completed-result stability at fuel 64. Frozen Wire v1 and
v2 continue to reject the internal host value.

## Acceptance evidence

- `lake build` completed successfully with 655 jobs;
- `lake test` completed successfully with 1,198 jobs;
- all 21 changed Lean roots passed with `--trust=0` and warnings as errors;
- metadata, semantic-kernel, and diff checks passed;
- axiom reports use the existing `propext` and `Quot.sound`; the per-byte
  coherence theorem additionally uses `Classical.choice` through the existing
  codec proof path; and
- no custom axiom or `sorry` remains; the independent audit found no P0-P3
  issue.

## Consequences

Internal checked Core code can observe one exact Word from the
same bounded run-fixed bytes used by the completed byte and size observations.
The operation preserves absence, exact natural offsets, and the repository's
existing big-endian Word representation without publishing calldata or ABI
semantics.

Current/callee roles, call kind, lifecycle, return/revert consumption, nested
execution, and public exposure remain separate decisions.
