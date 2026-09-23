# ADR-0055: Address representation coherence

- Status: Accepted
- Decision date: 2026-08-27
- Scope: fifth internal contract-runtime foundation slice
- Implementation: Complete

## Context

[ADR-0051](0051-canonical-runtime-scalars.md) fixes canonical Address text as
`0x` followed by exactly 40 lowercase hexadecimal digits.
[ADR-0054](0054-strict-address-bytes.md) independently fixes the same 160-bit
value as exactly 20 most-significant-byte-first octets. Both representations
are strict and executable, but their agreement is not yet a published theorem.

Maintaining two unconnected codecs would allow later refactoring to preserve
each local round trip while silently changing their relationship. The next safe
step is therefore a proof-only coherence layer over the existing APIs. It does
not need source syntax, ABI rules, contract state, or another runtime value.

## Decision

Add no new public executable API. Reuse these existing operations:

```text
encodeAddressText     : Address → String
decodeAddressText?    : String → Option Address
encodeAddressBytesBE  : Address → ByteArray
decodeAddressBytesBE? : ByteArray → Option Address
encodeBytesText       : ByteArray → String
decodeBytesText?      : String → Option ByteArray
```

Canonical text for an address equals canonical byte text for its exact 20-byte
encoding. Both decoder paths accept the same strings and produce the same
address. This includes malformed, noncanonical, and incorrectly sized text:
neither path may normalize uppercase, add or remove leading zeros, pad bytes,
or truncate input.

## Required proof interface

Publish exactly four focused laws:

1. `encodeBytesText_encodeAddressBytesBE` proves
   `encodeBytesText (encodeAddressBytesBE value) = encodeAddressText value`.
2. `decodeBytesText?_encodeAddressText` proves that decoding canonical Address
   text as Bytes returns `some (encodeAddressBytesBE value)`.
3. `decodeAddressText?_encodeBytesText` proves, for every byte array, that
   decoding its canonical Bytes text as an Address equals
   `decodeAddressBytesBE? bytes`.
4. `decodeAddressText?_eq_decodeBytesText?_bind` proves, for every string, that
   direct Address decoding equals decoding Bytes and then applying
   `decodeAddressBytesBE?`.

The fourth law fixes complete acceptance and result coherence, not only the
successful canonical examples. Private radix, digit-pairing, length, and
canonicality helpers do not add to the exact four public laws. The
implementation uses no custom axioms or unchecked declarations; standard Lean
axiom dependencies are audited and recorded.

## Required tests

Provide exactly eight executable runtime assertions:

1. address zero has identical Address text and encoded-byte text;
2. address one has identical text with all required leading zeros;
3. a nontrivial middle address has identical text;
4. the maximum address has identical text;
5. canonical Bytes text for an independent 19-byte array agrees with strict
   Address-byte rejection;
6. canonical Bytes text for an independent 20-byte array agrees with strict
   Address-byte decoding;
7. canonical Bytes text for an independent 21-byte array agrees with strict
   Address-byte rejection; and
8. a table of canonical Address literals, uppercase, odd-width, and wrong-width
   text agrees under the two decoder paths.

Each assertion calls the existing executable codecs directly. Table checks
remain one runtime assertion each and must report which fixture failed.

## Staged implementation plan

Keep every commit below 300 changed lines and leave the tree green:

1. accept this ADR and mark the proof-only slice active in documentation;
2. add private base-256-to-base-16 digit-pairing helpers;
3. add the exact four coherence laws and expose them through the semantics
   umbrella;
4. add the exact eight executable runtime assertions; and
5. independently audit the slice and update completion documentation.

The helper stage adds no public executable API or focused law. It isolates the
radix-regrouping proof needed to connect the independently implemented codecs.

## Completion evidence

The completed proof-only layer adds no public executable API. Fifteen private
helper theorems establish the radix regrouping and canonicality boundary, while
exactly four public theorems expose the representation-coherence contract.
Exactly eight runtime assertions cover the required canonical address values,
independent 19-, 20-, and 21-byte inputs, and canonical, malformed, uppercase,
odd-width, and wrong-width text.

The staged implementation is recorded by commits `fe06803` (decision),
`59b44cf` (private coherence kernel), `e519ac8` (public laws), and `e6e43ba`
(runtime assertions). Every commit remains below 300 changed lines.

All four public laws report exactly `propext`, `Classical.choice`, and
`Quot.sound`. There are no custom axioms or unchecked declarations. Focused and
full builds and tests, trust-zero, semantic-kernel, and metadata checks pass.
The independent audit found no P0-P3 issue.

## Publication and exclusions

This slice adds no codec, runtime value, alternate text or byte spelling,
variable width, byte order, padding, truncation, modulo conversion, source cast,
source type rule, elaboration rule, ABI rule, selector, hashing algorithm, or
address derivation. It changes none of the existing scalar APIs.

It adds no Core type, expression, primitive, evaluator step, contract entry,
frame adapter, trap taxonomy, world state, account, storage, balance, log, call,
creation, checkpoint, rollback, state delta, EVM revision, gas schedule, host
behavior, or resource-limit meaning.

It adds no Wire tag, JSON schema, profile, or published observation. Frozen
public formats and metadata remain unchanged.

## Consequences

Internal runtime code can move between Address text and exact bytes without two
independent notions of canonicality. Any future ABI or source conversion must
remain a separately named and decided operation rather than weakening this
strict coherence boundary.
