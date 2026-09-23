# ADR-0133: Bounded optional input-byte observation

- Status: Accepted
- Decision date: 2026-08-29
- Scope: expose one indexed byte from an explicitly bounded immutable input
- Implementation: Complete

## Context

ADR-0131 and ADR-0132 establish one canonical immutable
`HostStorageDriver.ExecutionInputs` record. The same exact record is used for
checked-code selection, request handling, recursive driving, fuel evidence,
selected completion, and parent-indexed continuation construction. Its current
fields expose only values with direct internal consumers: code Address, call
value, and caller Address.

The next syntax-independent input observation is one byte selected by a Core
Word. It must preserve the difference between an in-bounds zero byte and an
out-of-bounds index. It must also avoid committing to calldata, ABI, padding,
word decoding, endianness, or a source-language spelling.

## Decision

Introduce one immutable bounded byte carrier in the semantics layer:

```lean
namespace Solcore.Semantics.HostStorageDriver

structure InputData where
  bytes : Bytes
  size_lt_wordModulus : bytes.size < Core.wordModulus

end Solcore.Semantics.HostStorageDriver
```

Append it as a required final field of the existing input record:

```lean
structure ExecutionInputs where
  codeAddress : Address
  callValue : Core.Word
  callerAddress : Address
  inputData : InputData
```

Every construction of `ExecutionInputs` must supply `inputData` explicitly.
Do not add an empty default, optional field, fallback constructor, inferred
value, compatibility overload, or parallel driver seam that omits it.

The field is fixed for exactly one handled run because every recursive driver
call and every selected or parent-indexed adapter receives the same complete
`ExecutionInputs`. It is not stored in mutable WorldState or handler context.

## Exact byte lookup

Define the one observation owned by the carrier:

```lean
InputData.byte? : InputData -> Core.Word -> Option Core.Word
```

For input `data` and index `index`, lookup uses the exact natural value of
`index` as a zero-based position in `data.bytes`:

- if that position is out of bounds, return `none`;
- if it contains byte `b`, return `some` of the Core Word whose natural value
  is exactly `b.toNat`.

The widening is lossless and every successful result is strictly less than
256. A present zero byte returns `some Core.Word.zero`; it is never collapsed
to `none`. No index is truncated, wrapped, clamped, or reduced modulo the byte
sequence size.

The strict size proof establishes that every valid byte position is itself
representable as a Core Word. It does not expose the size to Core and does not
impose any encoding interpretation on the byte order.

## Core host capability

Append one internal capability after the six existing entries:

```lean
inductive HostFunction where
  | storageRead
  | storageWrite
  | storageAddress
  | codeAddress
  | callValue
  | callerAddress
  | inputDataByte?
```

`HostFunction.inputDataByte?` has parameter type Word, result type
`Sum Unit Word`, and stable index 6. Existing indexes 0 through 5 do not move.
`hostContext` and `hostEnvironment` append the matching entries and therefore
have length 7. Index 7 becomes the first unbound host-capability index.

Append the matching first-order request:

```lean
inductive HostRequest where
  -- existing requests
  | inputDataByte? (index : Word)
```

`HostRequest.Response (.inputDataByte? index)` is `Option Word`. Its Core
response type is `Sum Unit Word`. Response injection is exact:

- `responseValue (.inputDataByte? index) none = .inLeft .word .unit`;
- `responseValue (.inputDataByte? index) (some value) =
  .inRight .unit (.word value)`.

Applying the capability to a Word emits exactly the indexed request. Applying
it to any other Core value produces the existing exact
`invalidHostArgument` fault. Resumption injects the corresponding sum value
while preserving the saved continuation and Core-local Store.

Core owns only the typed capability, optional response shape, and first-order
request. It does not import `Bytes`, `InputData`, storage, frames, ABI, or any
origin story for the supplied bytes.

## Handler, driver, and continuation meaning

The semantics handler interprets the request exactly as follows:

```lean
handleRequest inputs context (.inputDataByte? index) =
  (context, inputs.inputData.byte? index)
```

This request is read-only. It performs no Account, code, Address, or storage
lookup, exposes no separate input-size query, and leaves the complete mutable
context unchanged. The suspension law preserves the request index, saved
continuation, and local Store and injects exactly the left-or-right Core
response selected above.

`handler`, `handleSuspension`, recursive `HostStorageDriver.run`, handled-step
and fuel relations, selected execution, completion, and parent-indexed
continuation construction continue to receive the same whole immutable input.
Code selection remains solely `code? inputs.codeAddress`. No result carrier or
continuation gains a separate bytes field.

## Exact proof obligations

Expose focused laws for:

- `InputData` construction and both field projections;
- every existing `ExecutionInputs` projection after appending the required
  field;
- empty input lookup and exact present or absent indexed lookup;
- first, arbitrary in-bounds, last, and out-of-bounds observations;
- present-zero preservation as `some Core.Word.zero`;
- successful lookup implying a result natural value below 256;
- capability parameter type, result type, append-only index 6, table lookups,
  table length 7, and first-unbound index 7;
- request response type and exact `Option Word` to Core sum injection;
- request emission for a Word argument and exact invalid-argument behavior for
  every other value shape;
- exact suspension resumption with continuation and Store preservation;
- executable/declarative emission and transition correspondence;
- progress, response typing, state typing, preservation, runner
  correspondence, and checked-program no-fault safety;
- exact handler response and complete mutable-context identity;
- recursive driver resumption with the same immutable input and remaining
  fuel;
- driver completeness, fuel soundness, type safety, and completed larger-fuel
  stability;
- selected lookup continuing to depend only on `inputs.codeAddress`;
- unchanged selected failure, storage absence, exhaustion, and completion
  option boundaries; and
- unchanged parent-indexed coherence, triple-option completion, and terminal
  larger-fuel stability.

No theorem may interpret byte positions as fields, words, selectors, lengths,
ABI values, source arguments, nested-call payloads, or authenticated data.

## Required regressions

Focused lookup tests must use explicit bounded carriers and cover:

- empty bytes at index zero;
- first, middle, and last bytes of a nonempty sequence;
- exactly last-plus-one as out of bounds;
- the maximum Core Word index as out of bounds for the finite fixture;
- a present zero byte remaining `some Word.zero`; and
- every successful returned Word having natural value below 256.

Low-level Core tests must cover:

- fixed host indexes 0 through 6, both table lookups, length 7, and first
  unbound index 7;
- host-check acceptance of a Word-indexed observation and closed-check
  rejection;
- exact raw fault for a non-Word argument;
- exact request index, optional response injection, continuation, and Store;
- measured request-ready and completion fuel rather than an assumed cost; and
- direct rejection of `.hostFunction .inputDataByte?` by frozen Wire v1 and
  v2.

End-to-end regressions must:

- supply nonempty `inputData` explicitly at every `ExecutionInputs`
  construction and retain all existing address and call-value distinctions;
- vary only `inputData`, retaining code, storage, call value, and caller
  Address, and observe only the byte-dependent result change;
- demonstrate both missing and present-zero branches without conflation;
- observe one present byte, case-analyze the `Sum Unit Word`, write the exact
  right-branch Word to working storage, and observe the same index again;
- prove that the two successful observations agree around the mutation and
  that the stored value is the exact widened byte;
- preserve the three nested optional boundaries of parent-indexed completion;
- consume the completed context through ADR-0129's fold and recover both the
  byte-derived storage entry and exact terminal bytes; and
- retain existing storage-address, code-address, call-value, caller-address,
  safety, fuel, and terminal-stability regressions.

No completed construction may silently choose empty input bytes.

## Dependency and publication boundary

Semantics owns `InputData`, its size proof, exact byte indexing and widening,
and request interpretation. Core owns only a Word-to-`Sum Unit Word` internal
host capability. Generic HostDriver and continuation layers remain parametric
and must not import bytes-specific meaning.

Frozen Core Wire v1 and v2 continue to reject every host-function value. Add no
Wire tag, runtime schema, profile, ABI
rule, source form, parser rule, or source elaboration. The root README does
not change. Publication requires a separate ADR.

## Non-goals

This ADR does not define or prove:

- an input-size capability, `inputDataSize`, length query, or length result;
- `inputWord`, multi-byte reads, word assembly, slicing, copying, hashing, or
  decoding;
- big-endian or little-endian interpretation, left or right padding,
  truncation, alignment, or canonical encoding;
- calldata, ABI arguments, function selectors, dispatch, return data, revert
  data, memory, storage layout, or source parameter meaning;
- bounds faults, traps, zero-filling, default bytes, sentinel words, or a
  missing-value collapse;
- mutable input, input writes, input consumption, cursor state, streaming, or
  aliasing with Core-local cells or WorldState storage;
- nested invocation, child-input derivation, forwarding, call stack, call
  kind, delegate behavior, creation input, callbacks, or parent resumption;
- provenance, authentication, signing, ownership, authority, privacy, or trust
  in the supplied bytes;
- balance, transfer, affordability, payability, gas, fork rules, or transaction
  finalization;
- a public representation, compatibility promise, parser change, schema,
  profile, ABI, or publication; or
- any relationship between input bytes and code, storage, caller Address, or
  call value.

## Implementation sequence

Keep each green commit at roughly 300 changed lines or fewer:

1. record and activate this exact contract;
2. add `InputData`, `byte?`, and focused lookup laws and tests;
3. append the required `ExecutionInputs.inputData` field and migrate every
   explicit construction without a default;
4. append the Core capability and request and close exhaustive machine,
   progress, typing, preservation, runner, and no-fault cases;
5. add exact handler, suspension, recursive-driver, and strict optional
   response laws;
6. repair request-exhaustive custom handlers and add focused Core, fuel, and
   Wire regressions;
7. add input-only variation and observe-case-write-observe selected-execution
   regressions;
8. add triple-option parent completion and ADR-0129 fold regressions;
9. run trust, axiom, dependency, build, test, metadata, kernel, compatibility,
   and independent audits; and
10. synchronize completion evidence in current-facing internal documents.

Temporary migration names must be removed before completion. No transitional
API may infer input bytes, omit the size proof, or manufacture empty input.

## Implementation record

`ExecutionInputs` now requires a bounded `InputData` value. Lookup uses the
exact natural value of the Core Word offset, widens every present byte without
loss, and keeps `some Word.zero` distinct from `none`. The bound proves that
every position in the byte sequence has an exact Core Word index.

Core appends `inputDataByte? : word -> sum unit word` at index 6, making both
host tables length 7 and index 7 the first unbound position. The request uses
`Option Word`; response injection, suspension, raw invalid-argument faults,
resumption, progress, typing, preservation, runner correspondence, and checked
no-fault safety are complete. Frozen Wire v1 and v2 reject the internal host
value.

The canonical handler returns `inputs.inputData.byte? offset` and preserves the
complete mutable context, saved continuation, and Core-local Store. The driver
keeps the same immutable input and remaining fuel. Exact laws cover generic,
absent, and present responses, and direct execution proves that changing only
`inputData` changes no part of the completed context.

Runtime regressions cover empty, first, middle, last, last-plus-one, maximum
Word, and a value above machine-word range without narrowing. Direct
observation covers fuel 4/5 and larger-fuel stability. A case-analyzing program
writes a present byte to storage and observes it again, while separate runs
distinguish a present zero from absence. Parent-indexed execution preserves all
three optional boundaries and reaches ADR-0129's fold with the exact
byte-derived storage entry and terminal bytes.

## Acceptance evidence

- the full build completed successfully with 649 jobs;
- the complete 1,186-job test target and executable suite passed;
- every changed Lean root passed with `--trust=0` and warnings as errors;
- metadata verification and semantic-kernel policy checks passed;
- key axiom reports contain only the existing `propext` and `Quot.sound`;
- independent Core, handler, end-to-end, parent, and full-ADR audits found no
  remaining P0-P3 issue; and
- no parser, source syntax, schema, profile, Wire tag, public format, or root
  README changed.

## Consequences

Internal checked Core code can distinguish an absent indexed byte from every
present octet, including zero, while the byte sequence remains an explicit
run-fixed semantic input. Existing sum case analysis and storage writing are
sufficient to consume a successful observation without adding a new Core data
type.

Input length, multi-byte interpretation, ABI meaning, nested-call derivation,
and publication remain separate future decisions.
