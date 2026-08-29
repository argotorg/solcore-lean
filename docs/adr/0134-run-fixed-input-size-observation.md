# ADR-0134: Run-fixed input-size observation

- Status: Accepted
- Decision date: 2026-08-29
- Scope: expose the exact size of the bounded immutable input to internal Core code
- Implementation: Complete

## Context

ADR-0133 adds one bounded, immutable `InputData` value to
`HostStorageDriver.ExecutionInputs`. Internal Core code can observe an indexed
byte as `Sum Unit Word`, preserving the difference between a present zero byte
and an out-of-bounds index. The byte sequence remains fixed across request
handling, recursive driving, selected execution, and parent-indexed
continuation construction.

The existing carrier already proves:

```lean
input.bytes.size < Core.wordModulus
```

Consequently, its exact natural-number size can be represented by a Core Word
without truncation or modular reduction. Exposing that value is the smallest
next observation with an existing semantic source and a direct internal Core
consumer. It also makes the precise boundary of `InputData.byte?` observable
without defining calldata, ABI, padding, or a multi-byte decoding rule.

## Decision

Add one derived observation to the existing carrier:

```lean
namespace Solcore.Semantics.HostStorageDriver.InputData

def sizeWord (input : InputData) : Core.Word :=
  ⟨input.bytes.size, input.size_lt_wordModulus⟩

end Solcore.Semantics.HostStorageDriver.InputData
```

`sizeWord` is derived from `InputData`; it is not a second field and carries no
independent value. Its natural value is definitionally the exact byte length.
It does not clamp, wrap, truncate, use a machine-size conversion, or reduce the
length modulo `Core.wordModulus`.

Do not add another `ExecutionInputs` field, cached length, unchecked
constructor, default input, fallback value, or compatibility path. The strict
bound accepted by ADR-0133 remains the only evidence required to construct the
Word.

## Byte-boundary coherence

The size observation must agree exactly with ADR-0133 byte lookup. Prove both
equivalent boundary forms:

```lean
input.byte? offset = none ↔ input.sizeWord.val ≤ offset.val

(∃ byte, input.byte? offset = some byte) ↔
  offset.val < input.sizeWord.val
```

These laws concern only whether a byte position exists. They do not constrain
the value of a present byte. In particular, a present zero byte remains
`some Core.Word.zero`, while the first index at or above `sizeWord` is absent.

The strict input bound also preserves the existing converse reachability law:
every natural position below `sizeWord.val` has an exact `Core.Word` offset.
No theorem implies that a byte array close to the logical Word limit can or
must be allocated by a concrete runtime.

## Core host capability

Append one internal capability after the seven existing entries:

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
```

`HostFunction.inputDataSize` has parameter type Unit, result type Word, and
stable index 7. Existing indexes 0 through 6 do not move. `hostContext` and
`hostEnvironment` append the matching entries and therefore have length 8.
Index 8 becomes the first unbound host-capability index.

Append the matching first-order request:

```lean
inductive HostRequest where
  -- existing requests
  | inputDataSize
```

`HostRequest.Response .inputDataSize` is `Word`. Its Core response type is
Word, and response injection is exactly `.word response`. Applying the
capability to Unit emits exactly `.inputDataSize`. Applying it to any other
Core value produces the existing exact `invalidHostArgument` fault.
Resumption injects the exact size Word while preserving the saved continuation
and Core-local Store.

Core owns only the typed Unit-to-Word capability and first-order request. It
does not import `Bytes`, `InputData`, storage, frames, ABI, or any source-level
meaning for the input.

## Handler, driver, and continuation meaning

The semantics handler interprets the request exactly as follows:

```lean
handleRequest inputs context .inputDataSize =
  (context, inputs.inputData.sizeWord)
```

The request is read-only and leaves the complete mutable context unchanged.
It performs no Account, code, Address, or storage lookup. Its result comes from
the same `InputData` value already used by `inputDataByte?`.

`handler`, `handleSuspension`, recursive `HostStorageDriver.run`, handled-step
and fuel relations, selected execution, completion, and parent-indexed
continuation construction continue to receive the same whole immutable
`ExecutionInputs`. Code selection remains solely `code? inputs.codeAddress`.
No result carrier or continuation gains a separate input-size field.

## Exact proof obligations

Expose focused laws for:

- exact `sizeWord.val = input.bytes.size` and construction from the retained
  strict bound;
- both byte-boundary coherence statements above;
- empty input having size zero and every nonempty fixture having its exact
  natural size;
- capability parameter type, result type, append-only index 7, both table
  lookups, table length 8, and first-unbound index 8;
- request response type, exact Word response injection, and suspension
  resumption with continuation and Store identity;
- request emission for Unit and exact invalid-argument behavior for every
  other Core value shape;
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

No theorem may interpret the size as an ABI payload length, selector boundary,
argument count, memory size, storage extent, return-data size, or authenticated
property.

## Required regressions

Focused carrier tests must cover:

- exact sizes for empty, one-byte, and representative multi-byte inputs;
- byte presence at `sizeWord - 1` for a nonempty fixture;
- byte absence exactly at `sizeWord` and above it;
- present zero immediately below the boundary remaining distinct from
  absence at the boundary; and
- the two exact byte-boundary coherence directions.

Low-level Core tests must cover:

- fixed host indexes 0 through 7, both table lookups, length 8, and first
  unbound index 8;
- host-check acceptance of `inputDataSize Unit` and closed-check rejection;
- static rejection and exact raw fault for a non-Unit argument;
- exact request emission, Word response injection, continuation, and Store;
- measured request-ready, suspension, and handled-completion fuel rather than
  an assumed cost; and
- direct rejection of `.hostFunction .inputDataSize` by frozen Wire v1 and
  v2.

End-to-end regressions must:

- directly observe exact zero and nonzero input sizes;
- vary only `inputData`, retaining code, storage, call value, caller Address,
  and code Address, and observe only the size-dependent result change;
- observe the size, write that exact Word to working storage, observe the size
  again, and prove both observations and the stored value agree;
- retain the ADR-0133 distinction between present zero and absence;
- preserve all three optional boundaries of parent-indexed completion;
- consume a completed context through ADR-0129's fold and recover both the
  size-derived storage entry and exact terminal bytes; and
- retain existing storage-address, code-address, call-value, caller-address,
  input-byte, safety, fuel, and terminal-stability regressions.

Every `ExecutionInputs` construction continues to supply bounded input data
explicitly. No test may introduce a hidden empty-input compatibility path.

## Dependency and publication boundary

Semantics owns `InputData`, its strict length proof, `sizeWord`, byte-boundary
coherence, and request interpretation. Core owns only a Unit-to-Word internal
host capability. Generic HostDriver and continuation layers remain parametric
and must not import input-specific meaning.

Frozen Core Wire v1 and v2 continue to reject every host-function value. Add no
Wire tag, Oracle command, runtime schema, profile, metadata capability, ABI
rule, Surface form, parser rule, or source elaboration. The root README does
not change. Publication requires a separate ADR.

## Non-goals

This ADR does not define or prove:

- calldata, ABI arguments, function selectors, dispatch, or source parameter
  meaning;
- multi-byte loads, word assembly, slicing, copying, hashing, decoding, or
  encoding;
- endianness, padding, truncation, alignment, or a zero-fill rule;
- memory, return data, revert data, storage layout, or a relationship between
  their sizes and input size;
- mutable input, resizing, appending, consumption, cursor state, streaming, or
  aliasing with Core-local cells or WorldState storage;
- nested invocation, child-input derivation, forwarding, call stack, call
  kind, delegate behavior, creation input, callbacks, or parent resumption;
- provenance, authentication, ownership, authority, privacy, or trust in the
  supplied bytes;
- balance, transfer, affordability, payability, gas, fork rules, or
  transaction finalization;
- an allocation guarantee near `Core.wordModulus`; or
- any public representation, compatibility promise, parser change, Oracle
  behavior, schema, profile, ABI, Wire tag, or publication.

## Implementation sequence

Keep each green commit at roughly 300 changed lines or fewer:

1. record and activate this exact contract;
2. add `InputData.sizeWord`, exact value and byte-boundary coherence laws, and
   focused carrier tests;
3. append the Core capability and request and close exhaustive machine,
   progress, typing, preservation, runner, and no-fault cases;
4. add exact handler, suspension, recursive-driver, and context-identity laws;
5. repair request-exhaustive custom handlers and add focused Core, fuel, and
   Wire regressions;
6. add direct size observation, input-only variation, and
   observe-write-observe selected-execution regressions;
7. add triple-option parent completion and ADR-0129 fold regressions;
8. run trust, axiom, dependency, build, test, metadata, kernel,
   compatibility, and independent audits; and
9. synchronize completion evidence in current-facing internal documents.

Temporary migration names must be removed before completion. No transitional
API may cache, infer, truncate, or manufacture an input size.

## Implementation record

`InputData.sizeWord` now constructs a Core Word directly from the exact natural
byte length and the retained strict bound. It performs no machine-size
conversion or modular reduction. The proved boundary laws characterize byte
presence exactly below `sizeWord`, absence at or above it, and absence at the
size itself.

Core appends `inputDataSize : unit -> word` at index 7, making both host tables
length 8 and index 8 the first unbound position. The request has a total Word
response. Exact emission, raw invalid-argument faults, response injection,
resumption, progress, typing, preservation, runner correspondence, and checked
no-fault safety are complete. Frozen Wire v1 and v2 reject the internal host
value.

The canonical handler returns `(context, inputs.inputData.sizeWord)`. It
preserves the complete mutable context, saved continuation, and Core-local
Store, while the recursive driver resumes with the same immutable input and
remaining fuel. Direct selected execution returns exact zero and nonzero
sizes, changing only the result when only input data changes.

Runtime regressions cover fuel 4/5 and larger-fuel stability. A second checked
program observes size, writes that Word to storage, and observes size again at
the measured 23/29/30/32 boundaries. Parent-indexed execution preserves the
storage-absence, code-absence, exhaustion, and completion options before the
ADR-0129 fold recovers the exact size-derived storage entry and terminal bytes.

## Acceptance evidence

- the full build completed successfully with 652 jobs;
- the complete 1,192-job test target and executable suite passed;
- all 21 changed Lean roots passed with `--trust=0` and warnings as errors;
- metadata verification and semantic-kernel policy checks passed;
- key axiom reports contain only the existing `propext` and `Quot.sound`;
- independent full-contract and completion audits found no remaining P0-P3
  issue; and
- no parser, Surface, Oracle, schema, profile, Wire tag, public format, or root
  README changed.

## Consequences

Internal checked Core code can observe the exact length of the same bounded
run-fixed byte sequence used by ADR-0133. The observed size and optional byte
lookup share a formally proved boundary, while mutable execution context and
all existing selector roles remain unchanged.

Multi-byte interpretation, ABI meaning, nested-call derivation, and public
exposure remain separate future decisions.
