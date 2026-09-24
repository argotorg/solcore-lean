# ADR-0150: Static Word ABI

- Status: Accepted
- Decision date: 2026-08-30
- Scope: parser-independent `uint256 -> uint256` external dispatch
- Implementation: Complete

## Context

ADR-0006 requires one ABI-admissibility decision to cover metadata, canonical
signature spelling, calldata decoding, returndata encoding, duplicate
signatures, and selector collisions together. The executable lifecycle in
ADR-0145 through ADR-0149 can now run checked Core from an explicit
`WorldState`, apply top-level and nested rollback, retain fuel exhaustion for
resumption, and return persistent-state and transaction-journal observations.
It does not yet turn an external method call into that execution path.

Concrete Solcore syntax may change substantially. ABI work must therefore
start from syntax-independent method metadata and checker-accepted Core, not
from the parser or source AST. This milestone implements the smallest useful
vertical slice: one or more statically declared methods, each with exactly one
`uint256` input and one `uint256` result.

## Decision

Implement an internal Static Word ABI profile that joins all of the following
in one admitted artifact:

1. method metadata and canonical signature spelling;
2. Ethereum Keccak-256 and four-byte selector derivation;
3. calldata and returndata codecs;
4. duplicate-signature and selector-collision rejection;
5. generation and checking of one Core dispatcher; and
6. execution of that dispatcher through the existing balanced top-level
   lifecycle.

No component alone establishes ABI support. A contract is admitted only after
the whole path has succeeded. Admission and decoding are total and return
structured results; malformed or unsupported input must not cause a partial
function, panic, `unsafe` escape, or fabricated default method.

## Supported metadata and implementations

The only supported external type in this profile is `uint256`. Every method
has exactly this public shape:

```text
name(uint256) -> uint256
```

Metadata records the validated method name, the single `uint256` input, and
the single `uint256` output. Keeping the types explicit, although the first
profile has only one shape, prevents a name-only record from being mistaken
for complete ADR-0006 evidence.

A method name is a nonempty ASCII identifier matching:

```text
[A-Za-z_][A-Za-z0-9_]*
```

Non-ASCII names and other byte spellings are rejected rather than normalized.
The canonical signature is exactly the ASCII byte sequence:

```text
<name>(uint256)
```

Each metadata entry is paired with a checker-accepted Core implementation of
type `word -> word` under the fixed host environment. The initial profile uses
no named Core data definitions. The generator may rename host variables while
embedding an implementation, but it must preserve their meaning and prove or
recheck the generated program. An unchecked expression is never upgraded to
an ABI contract merely because its metadata is valid.

## Keccak-256 and selectors

Provide a total, pure Ethereum Keccak-256 implementation over arbitrary
bytes. This is the original Keccak-256 used by the Ethereum ABI, not the
standardized SHA3-256 variant. Its fixed parameters are:

- Keccak-f[1600] with 24 rounds;
- rate 1088 bits (136 bytes) and capacity 512 bits;
- legacy domain byte `0x01` with `pad10*1` ending in `0x80`;
- little-endian byte order within each 64-bit lane; and
- the first 32 squeezed bytes as the digest.

The selector is the first four digest bytes of the canonical-signature bytes,
kept as an exact four-byte value and with an equivalent `Fin (2^32)` view.
Hashing happens during admission and generation. Generated Core dispatch does
not implement or invoke Keccak at runtime; it compares calldata against the
already derived selector constants.

The implementation must include independent known-answer tests, including:

```text
keccak256("")
  = c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
selector("f(uint256)")   = b3de648b
selector("foo(uint256)") = 2fbebd38
selector("transfer(address,uint256)") = a9059cbb
```

The last vector tests the hash primitive and canonical byte handling only;
`address` and two-argument methods are not admitted by this ABI profile.

## Admission and collision rejection

Admission validates every name and implementation, computes every canonical
signature and selector, and then rejects before Core generation if either of
these conditions holds:

- two entries have the same canonical signature; or
- distinct canonical signatures have the same four-byte selector.

The rejection retains the conflicting metadata entries, signatures, and
selector so a caller can report the exact cause. Canonical ordering makes the
selected cause deterministic across input order; the general proof contract
also shows that reordering cannot change acceptance or the rejection class.
The known collision pair below is a required executable regression:

```text
f38491(uint256)  -> 77dbd42e
f116643(uint256) -> 77dbd42e
```

Successful admission returns a unique lookup table together with the
generated checker-accepted `CheckedCoreContract`. Rejected input produces no
runnable dispatcher. Empty method tables are rejected; this profile has no
fallback or receive entry.

## Calldata and returndata

A valid call consists of the selected method's four-byte selector followed by
the argument's canonical 32-byte big-endian encoding:

```text
bytes 0..3   selector
bytes 4..35  uint256 argument
bytes 36..   ignored suffix
```

Thus encoding a method and argument always produces exactly 36 bytes. Decoding
accepts 36 bytes or more and deliberately ignores a trailing suffix. Fewer
than 36 bytes is `shortCalldata`; a well-sized input whose selector is absent
from the admitted table is `unknownSelector`. Neither case selects a method.

The successful result codec is the existing canonical 32-byte big-endian Word
encoding. Its decoder is strict: exactly 32 bytes decode to a result Word;
shorter or longer returndata is rejected. Prove the call and result round trips
for every Word, selector extraction from encoded calls, and disjointness of
the structured decode failures.

These choices define only the Static Word ABI profile. In particular, suffix
acceptance must not be generalized to future dynamic or tuple codecs without
a separate decision.

## Generated checked Core dispatcher

Generate one closed host-aware Core program with the ADR-0145
`wordOutcomeV1` entry profile. The dispatcher:

1. reads `inputDataSize` and reverts when it is below 36;
2. reads `inputDataWordBE? 0` and takes its high 32 bits as the selector;
3. reads `inputDataWordBE? 4` as the argument;
4. compares the selector with the admitted selector constants;
5. applies the uniquely selected checked `word -> word` implementation; and
6. returns the resulting Word through the left/success branch of
   `wordOutcomeV1`.

The size check makes both 32-byte windows present for every coherent host.
The generated option cases remain total and map an unexpected missing window
to the same short-input revert rather than inventing bytes.

ABI dispatch failures use the revert branch of `wordOutcomeV1` with these
stable internal Word reasons:

```text
0  short calldata or an unexpectedly missing required window
1  unknown selector
```

No method implementation runs before routing succeeds. The ABI wrapper itself
does not synthesize a trap. A selected method may use the existing host
capabilities, so its storage, calls, value transfer, creation, logs, and fuel
behavior remains governed by ADR-0145 through ADR-0149.

The generated program must pass the ordinary Core checker, and admission must
return the exact `CheckedCoreContract` produced from that evidence. A parallel
interpreter or a metadata-only dispatcher is not an acceptable substitute.

## Top-level execution connection

Provide two syntax-independent entry points around the admitted contract:

- a raw-calldata entry point for short-input, unknown-selector, suffix, and
  differential-testing cases; and
- a method-and-Word convenience entry point that uses the canonical call
  encoder.

Both receive an explicit initial `WorldState`, target, caller, call value,
exact installation witness for the generated checked contract, fixed
`ExecutionEnvironment`, and fuel budget. They build a `TopLevelInvocation` and
delegate to `BalancedTopLevelExecution.runWithEnvironment`.

The returned value is the existing total sealed result. Top-level value
preflight rejection remains distinct from Core execution. A successful method
return commits the selected working world and transaction journal. ABI
reverts, later method reverts where future profiles permit them, and traps
select the root checkpoint. Exhaustion retains the same dispatcher state,
environment, world, and journal and resumes with only additional fuel.

The adapter must preserve the existing one-shot/split-fuel equality and expose
the existing return/revert/trap, returndata, world-delta, ordered-log, and
created-contract observations without copying or reinterpreting them.

## Required proofs and executable regressions

Implementation is complete when it provides external consumers for:

- ASCII-name validation and exact canonical-signature bytes;
- total Keccak padding, block absorption, squeezing, and the known vectors;
- exact selector prefix extraction and selector numeric/byte equivalence;
- call and result codec round trips and every length boundary;
- deterministic duplicate and selector-collision rejection before generation;
- generated-program checker acceptance and exact admitted-contract provenance;
- routing of at least two distinct methods to their exact implementations;
- stable short-calldata and unknown-selector reverts with no method effects;
- acceptance of a valid 36-byte call and of the same call with a suffix;
- exact canonical 32-byte successful returndata;
- commit, rollback, logs, and state deltas through an effectful selected method;
- exhaustion before and after dispatch and inside a method, followed by exact
  resumption without duplicate effects; and
- full build, executable suite, warnings-as-errors, trust-zero,
  semantic-kernel, axiom, and diff-hygiene checks.

## Exclusions and next boundary

This milestone does not define parser or source syntax, source-type lowering,
contract inheritance, overloading beyond canonical-signature uniqueness,
fallback or receive functions, constructors, events, indexed logs, storage
layout, or an external execution schema.

It also excludes zero-argument and multi-argument functions; `bool`, `address`,
bytes, strings, arrays, tuples, user ADTs, dynamic offsets, multiple return
values, revert-string ABI encoding, Solidity metadata JSON, payable/view/pure
annotations, gas accounting, recursive calls, and revision-dependent EVM
behavior.

Storage layout is deliberately not a prerequisite for this slice: selected
checked implementations already use the exact Word storage operations of the
executable semantics. A later storage-layout milestone may map source-level
fields into those slots without changing this ABI profile. Runtime execution
is exposed through a versioned direct Lean API; source-level storage layout
remains independent and can follow with an elaboration adapter.

## Implementation evidence

The implementation admits only validated ASCII metadata paired with a checked
`word -> word` Core implementation. It computes Ethereum Keccak selectors,
rejects duplicate signatures and selector collisions, generates and rechecks a
single dispatcher, and runs the admitted contract through the balanced
top-level lifecycle.

Executable regressions cover exact calldata and returndata boundaries, the
published collision pair in both input orders, two-method routing, suffix
acceptance, short and unknown-selector rollback, state/balance/log commit, and
fuel exhaustion before dispatch, after routing but before the first method
effect, and inside the selected method. Resumption is compared with the exact
one-shot budget and does not duplicate transfer, storage, or log effects.

Keccak padding alignment, absorber read bounds, digest width, codec round trips,
table uniqueness/provenance, generated checker acceptance, and ABI runner
delegation are exposed to external proof consumers. Full build, executable
tests, warnings-as-errors, and trust-zero checks pass at completion.
